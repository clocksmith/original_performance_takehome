#!/usr/bin/env python3
"""
Energy-based search over SpecBase knobs.

This treats kernel search as an energy minimization problem:
  energy = cycles + penalty * max(0, lower_bound_cycles - target)

Cycles are estimated from a graph scheduler on the op list when enabled,
otherwise we use the per-engine lower bound from op counts.
"""
from __future__ import annotations

import argparse
import json
import math
import os
import random
import sys
from dataclasses import replace, fields
from typing import Any

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
if ROOT not in sys.path:
    sys.path.insert(0, ROOT)

from generator.spec_base import SPEC_BASE, SpecBase
from problem import SLOT_LIMITS
from scripts.graph_dp_auto_search import build_final_ops, schedule_graph_with_restarts
from generator.build_kernel_base import build_base_instrs

CAPS = {k: v for k, v in SLOT_LIMITS.items() if k != "debug"}


def parse_list(s: str) -> list[str]:
    return [x.strip() for x in s.split(",") if x.strip()]


def parse_int_list(s: str) -> list[int]:
    items: list[int] = []
    for token in parse_list(s):
        if ":" in token:
            parts = [p for p in token.split(":") if p]
            if len(parts) < 2:
                continue
            start = int(parts[0])
            end = int(parts[1])
            step = int(parts[2]) if len(parts) > 2 else 1
            if step == 0:
                continue
            if end < start:
                rng = range(start, end - 1, -abs(step))
            else:
                rng = range(start, end + 1, abs(step))
            items.extend(list(rng))
        else:
            items.append(int(token))
    # preserve order, drop dups
    seen: set[int] = set()
    out: list[int] = []
    for v in items:
        if v in seen:
            continue
        seen.add(v)
        out.append(v)
    return out


def parse_bool_list(s: str) -> list[bool]:
    return [bool(int(x)) for x in parse_list(s)]


def parse_round_sets(s: str) -> list[tuple[int, ...]]:
    out: list[tuple[int, ...]] = []
    for block in s.split("|"):
        block = block.strip()
        if not block:
            continue
        out.append(tuple(parse_int_list(block)))
    return out


def parse_round_maps(s: str) -> list[dict[int, int]]:
    out: list[dict[int, int]] = []
    for block in s.split("|"):
        block = block.strip()
        if not block or block.lower() in {"none", "null", "{}"}:
            out.append({})
            continue
        mapping: dict[int, int] = {}
        for token in parse_list(block):
            if ":" not in token:
                continue
            key, value = token.split(":", 1)
            try:
                mapping[int(key)] = int(value)
            except ValueError:
                continue
        out.append(mapping)
    return out


def parse_selection_by_round(s: str) -> list[dict[int, str]]:
    """
    Parse per-round selection overrides.
      - "none" -> {}
      - "11,12,13,14=bitmask" -> {11: "bitmask", ...}
      - "11-14=mask_precompute" -> same using range syntax
    Multiple options separated by "|".
    """
    out: list[dict[int, str]] = []
    for block in s.split("|"):
        block = block.strip()
        if not block:
            continue
        if block in {"none", "null", "{}"}:
            out.append({})
            continue
        if "=" not in block:
            continue
        rounds_part, mode = block.split("=", 1)
        rounds_part = rounds_part.replace("-", ":")
        rounds = parse_int_list(rounds_part)
        mapping = {r: mode for r in rounds}
        out.append(mapping)
    return out


def parse_partial_cache(s: str) -> list[tuple[dict[int, int], dict[int, int]]]:
    """
    Parse partial-cache choices. Tokens:
      - "none" -> empty dicts
      - "x16"/"x24"/"x32" -> canonical depths for rounds 11-14 with cached_round_x set to X
    """
    out: list[tuple[dict[int, int], dict[int, int]]] = []
    for token in parse_list(s):
        if token == "none":
            out.append(({}, {}))
            continue
        if token.startswith("x"):
            try:
                x_val = int(token[1:])
            except ValueError:
                continue
            depth = {11: 0, 12: 1, 13: 2, 14: 3}
            cached_x = {r: x_val for r in depth.keys()}
            out.append((depth, cached_x))
    return out


def make_presets() -> dict[str, tuple[int, ...]]:
    return {
        "top4": (0, 1, 2, 3, 11, 12, 13, 14),
        "skip_r3": (0, 1, 2, 11, 12, 13, 14),
        "skip_r3_r13": (0, 1, 2, 11, 12, 14),
        "loadbound": (0, 1, 2, 11, 12, 13),
    }


def _count_ops(ops) -> dict[str, int]:
    counts = {k: 0 for k in CAPS}
    for op in ops:
        if op.engine == "debug":
            continue
        counts[op.engine] = counts.get(op.engine, 0) + 1
    return counts


def lower_bound_cycles(counts: dict[str, int]) -> int:
    lb = 0
    for eng, cap in CAPS.items():
        total = counts.get(eng, 0)
        if total:
            lb = max(lb, math.ceil(total / cap))
    return lb


def bundle_cycles(spec) -> int:
    instrs = build_base_instrs(spec)
    cycles = 0
    for bundle in instrs:
        if any(engine != "debug" and bundle.get(engine) for engine in bundle):
            cycles += 1
    return cycles


def score_spec(
    spec,
    *,
    target: int,
    penalty: float,
    schedule: bool,
    sched_restarts: int,
    sched_seed: int,
    sched_jitter: float,
    sched_policy: str,
    score_mode: str,
) -> dict[str, Any]:
    try:
        ops = build_final_ops(spec)
    except (RuntimeError, IndexError, ValueError, KeyError) as exc:
        # Treat invalid specs (e.g., scratch overflow) as high-energy.
        return {
            "energy": float("inf"),
            "cycles": 0,
            "lb": 0,
            "counts": {},
            "gap": 0,
            "error": str(exc),
        }
    counts = _count_ops(ops)
    lb = lower_bound_cycles(counts)
    cycles = lb
    if score_mode == "bundle":
        if schedule:
            cycles = bundle_cycles(spec)
    elif score_mode == "graph":
        if schedule:
            cycles = schedule_graph_with_restarts(
                ops, restarts=sched_restarts, seed=sched_seed, jitter=sched_jitter, policy=sched_policy
            )
    elif score_mode == "lb":
        cycles = lb
    else:
        raise ValueError(f"unknown score_mode {score_mode!r}")
    gap = max(0, lb - target) if target > 0 else 0
    energy = cycles + penalty * gap
    return {
        "energy": energy,
        "cycles": cycles,
        "lb": lb,
        "counts": counts,
        "gap": gap,
    }


def mutate_spec(spec, rnd: random.Random, domains: dict[str, list[Any]]):
    key = rnd.choice(list(domains.keys()))
    choices = domains[key]
    if not choices:
        return spec
    value = rnd.choice(choices)
    if key == "selection_mode":
        return replace(
            spec,
            selection_mode=value,
            use_bitmask_selection=(value == "bitmask"),
        )
    if key == "base_cached_rounds":
        return replace(spec, base_cached_rounds=tuple(value))
    if key == "depth4_rounds":
        return replace(spec, depth4_rounds=len(value), depth4_cached_rounds=tuple(value))
    if key == "cached_round_x":
        return replace(spec, cached_round_x=dict(value))
    if key == "cached_round_depth":
        return replace(spec, cached_round_depth=dict(value))
    if key == "selection_by_round":
        return replace(spec, selection_mode_by_round=value)
    if key == "partial_cache":
        depth_map, x_map = value
        return replace(spec, cached_round_depth=depth_map, cached_round_x=x_map)
    return replace(spec, **{key: value})


def spec_to_json(spec) -> dict[str, Any]:
    return dict(spec.__dict__)


def _spec_from_dict(seed: dict[str, Any]) -> SpecBase:
    field_names = {f.name for f in fields(SpecBase)}
    tuple_fields = {f.name for f in fields(SpecBase) if str(f.type).startswith("tuple")}
    overrides: dict[str, Any] = {}
    for key, value in seed.items():
        if key not in field_names:
            continue
        if key in tuple_fields and isinstance(value, list):
            overrides[key] = tuple(value)
        else:
            overrides[key] = value
    return replace(SPEC_BASE, **overrides)


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--steps", type=int, default=2000)
    ap.add_argument("--seed", type=int, default=0)
    ap.add_argument("--report-every", type=int, default=50)
    ap.add_argument("--schedule-every", type=int, default=10,
                    help="schedule every N steps (0 = always schedule)")
    ap.add_argument("--score-mode", type=str, default="graph",
                    choices=["graph", "bundle", "lb"],
                    help="How to score cycles: graph scheduler, bundle count, or per-engine LB.")
    ap.add_argument("--target", type=int, default=0,
                    help="target cycles; adds penalty if per-engine LB exceeds this")
    ap.add_argument("--penalty", type=float, default=100.0)
    ap.add_argument("--temp-start", type=float, default=50.0)
    ap.add_argument("--temp-decay", type=float, default=0.995)
    ap.add_argument("--out", type=str, default="")
    ap.add_argument("--seed-spec", type=str, default="",
                    help="JSON path for a seed spec (accepts {spec: {...}} or spec dict).")

    ap.add_argument("--selection", type=str, default="eq,bitmask,mask,mask_precompute")
    ap.add_argument("--idx-shifted", type=str, default="0,1")
    ap.add_argument("--vector-block", type=str, default="32,16,8")
    ap.add_argument("--extra-vecs", type=str, default="0,1,2,4")
    ap.add_argument("--reset-on-valu", type=str, default="0,1")
    ap.add_argument("--shifts-on-valu", type=str, default="0,1")
    ap.add_argument("--cached-nodes", type=str, default="none,7,15,31,63")
    ap.add_argument("--base-cached-presets", type=str, default="top4,skip_r3,skip_r3_r13")
    ap.add_argument("--depth4-rounds", type=str, default="4")
    ap.add_argument("--x4", type=str, default="8,12,15,24,32")
    ap.add_argument("--selection-by-round", type=str, default="none",
                    help="per-round selection overrides, e.g. '11-14=bitmask|none'")
    ap.add_argument("--cached-round-x", type=str, default="",
                    help="Per-round partial caching (e.g. '11:16,12:16|11:8,12:8').")
    ap.add_argument("--cached-round-depth", type=str, default="",
                    help="Override per-round cache depth (e.g. '11:2,12:2').")
    ap.add_argument("--partial-cache", type=str, default="none",
                    help="partial cache choices: none|x16|x24|x32 (applies to rounds 11-14)")
    ap.add_argument("--offload-op1", type=str, default="0,200,400,800,1200,1600")
    ap.add_argument("--offload-hash-op1", type=str, default="0,1")
    ap.add_argument("--offload-hash-shift", type=str, default="0,1")
    ap.add_argument("--offload-hash-op2", type=str, default="0,1")
    ap.add_argument("--offload-parity", type=str, default="0,1")
    ap.add_argument("--offload-node-xor", type=str, default="0,1")
    ap.add_argument("--node-ptr-incremental", type=str, default="0,1")
    ap.add_argument("--valu-select", type=str, default="0,1")
    ap.add_argument("--ptr-setup-engine", type=str, default="flow,alu")
    ap.add_argument("--setup-style", type=str, default="packed,inline")

    ap.add_argument("--sched-restarts", type=int, default=10)
    ap.add_argument("--sched-jitter", type=float, default=0.4)
    ap.add_argument("--sched-policy", type=str, default="mix")
    args = ap.parse_args()

    rnd = random.Random(args.seed)
    presets = make_presets()

    selection_modes = parse_list(args.selection)
    idx_shifted_list = parse_bool_list(args.idx_shifted)
    vector_blocks = parse_int_list(args.vector_block)
    extra_vecs_list = parse_int_list(args.extra_vecs)
    reset_on_valu_list = parse_bool_list(args.reset_on_valu)
    shifts_on_valu_list = parse_bool_list(args.shifts_on_valu)

    cached_nodes_list: list[int | None] = []
    for item in parse_list(args.cached_nodes):
        if item.lower() in {"none", "null"}:
            cached_nodes_list.append(None)
        else:
            cached_nodes_list.append(int(item))

    base_presets = []
    for name in parse_list(args.base_cached_presets):
        if name not in presets:
            raise SystemExit(f"Unknown preset: {name}")
        base_presets.append(presets[name])

    depth4_sets = parse_round_sets(args.depth4_rounds) if args.depth4_rounds else [tuple()]
    x4_list = parse_int_list(args.x4)
    selection_by_round_list = parse_selection_by_round(args.selection_by_round)
    cached_round_x_list = parse_round_maps(args.cached_round_x) if args.cached_round_x else [{}]
    cached_round_depth_list = parse_round_maps(args.cached_round_depth) if args.cached_round_depth else [{}]
    partial_cache_list = parse_partial_cache(args.partial_cache)

    domains = {
        "selection_mode": selection_modes,
        "idx_shifted": idx_shifted_list,
        "vector_block": vector_blocks,
        "extra_vecs": extra_vecs_list,
        "reset_on_valu": reset_on_valu_list,
        "shifts_on_valu": shifts_on_valu_list,
        "cached_nodes": cached_nodes_list,
        "base_cached_rounds": base_presets,
        "depth4_rounds": depth4_sets,
        "x4": x4_list,
        "selection_by_round": selection_by_round_list,
        "cached_round_x": cached_round_x_list,
        "cached_round_depth": cached_round_depth_list,
        "partial_cache": partial_cache_list,
        "offload_op1": parse_int_list(args.offload_op1),
        "offload_hash_op1": parse_bool_list(args.offload_hash_op1),
        "offload_hash_shift": parse_bool_list(args.offload_hash_shift),
        "offload_hash_op2": parse_bool_list(args.offload_hash_op2),
        "offload_parity": parse_bool_list(args.offload_parity),
        "offload_node_xor": parse_bool_list(args.offload_node_xor),
        "node_ptr_incremental": parse_bool_list(args.node_ptr_incremental),
        "valu_select": parse_bool_list(args.valu_select),
        "ptr_setup_engine": parse_list(args.ptr_setup_engine),
        "setup_style": parse_list(args.setup_style),
    }

    spec = SPEC_BASE
    if args.seed_spec:
        with open(args.seed_spec, "r", encoding="utf-8") as f:
            payload = json.load(f)
        seed_dict = payload.get("spec", payload)
        spec = _spec_from_dict(seed_dict)
    best_spec = spec
    best_score = score_spec(
        spec,
        target=args.target,
        penalty=args.penalty,
        schedule=True,
        sched_restarts=args.sched_restarts,
        sched_seed=args.seed,
        sched_jitter=args.sched_jitter,
        sched_policy=args.sched_policy,
        score_mode=args.score_mode,
    )
    curr_score = best_score
    temp = args.temp_start

    for step in range(1, args.steps + 1):
        cand = mutate_spec(spec, rnd, domains)
        do_schedule = args.schedule_every == 0 or (step % args.schedule_every == 0)
        cand_score = score_spec(
            cand,
            target=args.target,
            penalty=args.penalty,
            schedule=do_schedule,
            sched_restarts=args.sched_restarts,
            sched_seed=args.seed + step,
            sched_jitter=args.sched_jitter,
            sched_policy=args.sched_policy,
            score_mode=args.score_mode,
        )
        delta = cand_score["energy"] - curr_score["energy"]
        accept = delta <= 0
        if not accept and temp > 1e-9:
            prob = math.exp(-delta / temp)
            accept = rnd.random() < prob
        if accept:
            spec = cand
            curr_score = cand_score
        if cand_score["energy"] < best_score["energy"]:
            best_spec = cand
            best_score = cand_score
        if step % args.report_every == 0:
            print(
                f"[{step:5d}] energy={curr_score['energy']:.1f} "
                f"cycles={curr_score['cycles']} lb={curr_score['lb']} "
                f"best={best_score['energy']:.1f}"
            )
        temp *= args.temp_decay

    print("best_score:", best_score)
    print("best_spec:", spec_to_json(best_spec))
    if args.out:
        with open(args.out, "w", encoding="utf-8") as f:
            json.dump({"score": best_score, "spec": spec_to_json(best_spec)}, f, indent=2)


if __name__ == "__main__":
    main()
