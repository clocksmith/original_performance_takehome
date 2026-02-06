#!/usr/bin/env python3
"""
Stochastic upper-bound search over SpecBase knobs.

This avoids generator changes: it samples from existing spec knobs,
filters with a cheap resource bound, and schedules the best candidates
using the graph scheduler.
"""
from __future__ import annotations

import argparse
import math
import os
import random
import sys
from dataclasses import replace
from typing import Any

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
if ROOT not in sys.path:
    sys.path.insert(0, ROOT)

from generator.spec_base import SPEC_BASE
from problem import SLOT_LIMITS
from generator.build_kernel_base import build_base_instrs
from generator.schedule_dep import schedule_ops_dep
from scripts.graph_dp_auto_search import build_final_ops, schedule_graph_with_restarts

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
    # "4,5,6|4,5|4" -> [(4,5,6),(4,5),(4,)]
    out: list[tuple[int, ...]] = []
    for block in s.split("|"):
        block = block.strip()
        if not block:
            continue
        out.append(tuple(parse_int_list(block)))
    return out


def parse_round_choices(s: str) -> list[tuple[str, tuple[int, ...] | None]]:
    # "base|depth4|all|4,5,6|0:15"
    out: list[tuple[str, tuple[int, ...] | None]] = []
    for block in s.split("|"):
        block = block.strip()
        if not block:
            continue
        if block == "none":
            out.append(("explicit", tuple()))
            continue
        if block in {"base", "depth4", "all"}:
            out.append((block, None))
        else:
            out.append(("explicit", tuple(parse_int_list(block))))
    return out


def _count_ops(ops) -> dict[str, int]:
    counts = {k: 0 for k in CAPS}
    for op in ops:
        if op.engine == "debug":
            continue
        counts[op.engine] = counts.get(op.engine, 0) + 1
    return counts


def estimate_cycles(spec) -> int:
    ops = build_final_ops(spec)
    counts = _count_ops(ops)
    lb = 0
    for eng, cap in CAPS.items():
        total = counts.get(eng, 0)
        if total:
            lb = max(lb, math.ceil(total / cap))
    return lb


def engine_bounds(spec) -> tuple[dict[str, int], dict[str, int]]:
    ops = build_final_ops(spec)
    counts = _count_ops(ops)
    lbs: dict[str, int] = {}
    for eng, cap in CAPS.items():
        total = counts.get(eng, 0)
        lbs[eng] = math.ceil(total / cap) if total else 0
    return counts, lbs


def _freeze(obj: Any) -> Any:
    if isinstance(obj, dict):
        return tuple(sorted((k, _freeze(v)) for k, v in obj.items()))
    if isinstance(obj, (list, tuple)):
        return tuple(_freeze(v) for v in obj)
    if isinstance(obj, set):
        return tuple(sorted(_freeze(v) for v in obj))
    return obj


def _spec_key(spec, *, ignore_offload: bool = False) -> tuple[tuple[str, Any], ...]:
    data = dict(spec.__dict__)
    if ignore_offload:
        data.pop("offload_op1", None)
    data.pop("total_cycles", None)
    data.pop("valu_pad_cycles", None)
    return tuple(sorted((k, _freeze(v)) for k, v in data.items()))


def make_presets() -> dict[str, tuple[int, ...]]:
    return {
        "top4": (0, 1, 2, 3, 11, 12, 13, 14),
        "skip_r3": (0, 1, 2, 11, 12, 13, 14),
        "skip_r3_r13": (0, 1, 2, 11, 12, 14),
        "loadbound": (0, 1, 2, 11, 12, 13),
    }


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--samples", type=int, default=300)
    ap.add_argument("--beam", type=int, default=40, help="keep top-K by estimate")
    ap.add_argument("--mutations", type=int, default=200, help="mutations per beam")
    ap.add_argument("--seed", type=int, default=0)
    ap.add_argument("--schedule-top", type=int, default=20)
    ap.add_argument("--sched-mode", choices=["graph", "dep", "bundled"], default="graph")
    ap.add_argument("--sched-restarts", type=int, default=6)
    ap.add_argument("--sched-jitter", type=float, default=0.4)
    ap.add_argument("--sched-policy", type=str, default="mix")
    ap.add_argument("--mode", choices=["random", "sweep_offload", "grid"], default="random")
    ap.add_argument("--target", type=int, default=0, help="drop candidates whose per-engine LB exceeds target")

    ap.add_argument("--selection", type=str, default="eq")
    ap.add_argument("--idx-shifted", type=str, default="0,1")
    ap.add_argument("--vector-block", type=str, default="32,16,8")
    ap.add_argument("--extra-vecs", type=str, default="1,2,4")
    ap.add_argument("--reset-on-valu", type=str, default="0,1")
    ap.add_argument("--shifts-on-valu", type=str, default="0,1")
    ap.add_argument("--cached-nodes", type=str, default="none,7,15,31,63")
    ap.add_argument("--base-cached-presets", type=str, default="top4,skip_r3,skip_r3_r13")
    ap.add_argument("--depth4-rounds", type=str, default="4")
    ap.add_argument("--x4", type=str, default="8,12,15,24,32")
    ap.add_argument("--cache-rounds", type=str, default="base|depth4")
    ap.add_argument("--cache-depths", type=str, default="2,3")
    ap.add_argument("--cache-x", type=str, default="8,12,16,24,32")
    ap.add_argument("--offload-op1", type=str, default="0,200,400,448,600,800,1000,1200")
    ap.add_argument("--offload-hash-op1", type=str, default="0,1")
    ap.add_argument("--offload-hash-shift", type=str, default="0,1")
    ap.add_argument("--offload-hash-op2", type=str, default="0,1")
    ap.add_argument("--offload-parity", type=str, default="0,1")
    ap.add_argument("--offload-node-xor", type=str, default="0,1")
    ap.add_argument("--node-ptr-incremental", type=str, default="0,1")
    ap.add_argument("--valu-select", type=str, default="0,1")
    ap.add_argument("--ptr-setup-engine", type=str, default="flow,alu")
    ap.add_argument("--setup-style", type=str, default="packed,inline")
    args = ap.parse_args()

    rnd = random.Random(args.seed)
    presets = make_presets()

    selection_modes = parse_list(args.selection)
    idx_shifted_list = parse_bool_list(args.idx_shifted)
    vector_blocks = parse_int_list(args.vector_block)
    extra_vecs_list = parse_int_list(args.extra_vecs)
    reset_on_valu_list = parse_bool_list(args.reset_on_valu)
    shifts_on_valu_list = parse_bool_list(args.shifts_on_valu)
    cached_nodes_list = []
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
    cache_round_choices = parse_round_choices(args.cache_rounds) if args.cache_rounds else [("base", None)]
    if args.cache_depths in {"none", ""}:
        cache_depths = []
    else:
        cache_depths = parse_int_list(args.cache_depths) if args.cache_depths else []
    if args.cache_x in {"none", ""}:
        cache_x_list = []
    else:
        cache_x_list = parse_int_list(args.cache_x) if args.cache_x else []
    offload_op1_list = parse_int_list(args.offload_op1)
    offload_hash_op1_list = parse_bool_list(args.offload_hash_op1)
    offload_hash_shift_list = parse_bool_list(args.offload_hash_shift)
    offload_hash_op2_list = parse_bool_list(args.offload_hash_op2)
    offload_parity_list = parse_bool_list(args.offload_parity)
    offload_node_xor_list = parse_bool_list(args.offload_node_xor)
    node_ptr_inc_list = parse_bool_list(args.node_ptr_incremental)
    valu_select_list = parse_bool_list(args.valu_select)
    ptr_engines = parse_list(args.ptr_setup_engine)
    setup_styles = parse_list(args.setup_style)

    def _resolve_cache_rounds(
        choice: tuple[str, tuple[int, ...] | None],
        base_preset: tuple[int, ...],
        depth4_rounds: tuple[int, ...],
    ) -> tuple[int, ...]:
        kind, payload = choice
        if kind == "base":
            return base_preset
        if kind == "depth4":
            return depth4_rounds
        if kind == "all":
            return tuple(range(SPEC_BASE.rounds))
        return payload or tuple()

    def random_spec() -> Any:
        selection = rnd.choice(selection_modes)
        base_preset = rnd.choice(base_presets)
        depth4_rounds = rnd.choice(depth4_sets) if depth4_sets else tuple()
        cache_choice = rnd.choice(cache_round_choices)
        cache_rounds = _resolve_cache_rounds(cache_choice, base_preset, depth4_rounds)
        cache_depth = rnd.choice(cache_depths) if cache_depths else None
        cache_x = rnd.choice(cache_x_list) if cache_x_list else None
        cached_round_depth = {r: cache_depth for r in cache_rounds} if cache_depth is not None else {}
        cached_round_x = {r: cache_x for r in cache_rounds} if cache_x is not None else {}
        extra_vecs = rnd.choice(extra_vecs_list)
        if selection == "mask_precompute" and extra_vecs < 4:
            extra_vecs = 4
        return replace(
            SPEC_BASE,
            selection_mode=selection,
            use_bitmask_selection=(selection == "bitmask"),
            idx_shifted=rnd.choice(idx_shifted_list),
            vector_block=rnd.choice(vector_blocks),
            extra_vecs=extra_vecs,
            reset_on_valu=rnd.choice(reset_on_valu_list),
            shifts_on_valu=rnd.choice(shifts_on_valu_list),
            cached_nodes=rnd.choice(cached_nodes_list),
            base_cached_rounds=base_preset,
            depth4_rounds=len(depth4_rounds),
            depth4_cached_rounds=depth4_rounds,
            x4=rnd.choice(x4_list),
            cached_round_depth=cached_round_depth,
            cached_round_x=cached_round_x,
            offload_op1=rnd.choice(offload_op1_list),
            offload_hash_op1=rnd.choice(offload_hash_op1_list),
            offload_hash_shift=rnd.choice(offload_hash_shift_list),
            offload_hash_op2=rnd.choice(offload_hash_op2_list),
            offload_parity=rnd.choice(offload_parity_list),
            offload_node_xor=rnd.choice(offload_node_xor_list),
            node_ptr_incremental=rnd.choice(node_ptr_inc_list),
            valu_select=rnd.choice(valu_select_list),
            ptr_setup_engine=rnd.choice(ptr_engines),
            setup_style=rnd.choice(setup_styles),
            include_setup=True,
        )

    def mutate_spec(spec) -> Any:
        knob = rnd.randint(0, 15)
        if knob == 0:
            selection = rnd.choice(selection_modes)
            return replace(spec, selection_mode=selection, use_bitmask_selection=(selection == "bitmask"))
        if knob == 1:
            return replace(spec, idx_shifted=rnd.choice(idx_shifted_list))
        if knob == 2:
            return replace(spec, vector_block=rnd.choice(vector_blocks))
        if knob == 3:
            return replace(spec, extra_vecs=rnd.choice(extra_vecs_list))
        if knob == 4:
            return replace(spec, offload_op1=rnd.choice(offload_op1_list))
        if knob == 5:
            return replace(spec, offload_parity=rnd.choice(offload_parity_list))
        if knob == 6:
            return replace(spec, offload_node_xor=rnd.choice(offload_node_xor_list))
        if knob == 7:
            return replace(spec, base_cached_rounds=rnd.choice(base_presets))
        if knob == 8:
            return replace(spec, x4=rnd.choice(x4_list))
        if knob == 9:
            return replace(spec, setup_style=rnd.choice(setup_styles))
        if knob == 10:
            return replace(spec, offload_hash_op1=rnd.choice(offload_hash_op1_list))
        if knob == 11:
            return replace(spec, offload_hash_shift=rnd.choice(offload_hash_shift_list))
        if knob == 12:
            return replace(spec, offload_hash_op2=rnd.choice(offload_hash_op2_list))
        if knob == 13:
            return replace(spec, node_ptr_incremental=rnd.choice(node_ptr_inc_list))
        if knob == 14:
            return replace(spec, valu_select=rnd.choice(valu_select_list))
        # mutate cache depth/x (uniform across chosen rounds)
        base_preset = rnd.choice(base_presets)
        depth4_rounds = rnd.choice(depth4_sets) if depth4_sets else tuple()
        cache_choice = rnd.choice(cache_round_choices)
        cache_rounds = _resolve_cache_rounds(cache_choice, base_preset, depth4_rounds)
        cache_depth = rnd.choice(cache_depths) if cache_depths else None
        cache_x = rnd.choice(cache_x_list) if cache_x_list else None
        cached_round_depth = {r: cache_depth for r in cache_rounds} if cache_depth is not None else {}
        cached_round_x = {r: cache_x for r in cache_rounds} if cache_x is not None else {}
        return replace(
            spec,
            base_cached_rounds=base_preset,
            depth4_rounds=len(depth4_rounds),
            depth4_cached_rounds=depth4_rounds,
            cached_round_depth=cached_round_depth,
            cached_round_x=cached_round_x,
        )

    frontier: list[tuple[int, Any]] = []

    def maybe_add(spec: Any) -> None:
        try:
            counts, lbs = engine_bounds(spec)
        except Exception:
            return
        if args.target:
            if any(v > args.target for v in lbs.values()):
                return
        est = max(lbs.values()) if lbs else 0
        frontier.append((est, spec))

    if args.mode == "random":
        for _ in range(args.samples):
            maybe_add(random_spec())
            frontier.sort(key=lambda x: x[0])
            frontier = frontier[: args.beam]

        for _ in range(args.mutations):
            if not frontier:
                break
            parent = rnd.choice(frontier)[1]
            maybe_add(mutate_spec(parent))
            frontier.sort(key=lambda x: x[0])
            frontier = frontier[: args.beam]
    elif args.mode == "sweep_offload":
        # sweep offload_op1 for sampled base specs (other knobs)
        base_specs: list[Any] = []
        seen_keys: set[tuple[tuple[str, Any], ...]] = set()
        while len(base_specs) < args.samples:
            base = random_spec()
            base = replace(base, offload_op1=offload_op1_list[0])
            key = _spec_key(base, ignore_offload=True)
            if key in seen_keys:
                continue
            seen_keys.add(key)
            base_specs.append(base)
        for base in base_specs:
            for off in offload_op1_list:
                maybe_add(replace(base, offload_op1=off))
            frontier.sort(key=lambda x: x[0])
            frontier = frontier[: args.beam]
    else:
        # full grid over provided knobs (can be large; keep beam-pruned)
        for selection in selection_modes:
            for idx_shifted in idx_shifted_list:
                for cached_nodes in cached_nodes_list:
                    for base_preset in base_presets:
                        for depth4_rounds in depth4_sets:
                            for cache_choice in cache_round_choices:
                                cache_rounds = _resolve_cache_rounds(cache_choice, base_preset, depth4_rounds)
                                for cache_depth in (cache_depths or [None]):
                                    for cache_x in (cache_x_list or [None]):
                                        cached_round_depth = {r: cache_depth for r in cache_rounds} if cache_depth is not None else {}
                                        cached_round_x = {r: cache_x for r in cache_rounds} if cache_x is not None else {}
                                        for x4 in x4_list:
                                            for vector_block in vector_blocks:
                                                for extra_vecs in extra_vecs_list:
                                                    if selection == "mask_precompute" and extra_vecs < 4:
                                                        continue
                                                    for ptr_engine in ptr_engines:
                                                        for setup_style in setup_styles:
                                                            for node_ptr_inc in node_ptr_inc_list:
                                                                for valu_select in valu_select_list:
                                                                    for off_hash1 in offload_hash_op1_list:
                                                                        for off_hash_shift in offload_hash_shift_list:
                                                                            for off_hash2 in offload_hash_op2_list:
                                                                                for off_parity in offload_parity_list:
                                                                                    for off_node_xor in offload_node_xor_list:
                                                                                        base = replace(
                                                                                    SPEC_BASE,
                                                                                    selection_mode=selection,
                                                                                    use_bitmask_selection=(selection == "bitmask"),
                                                                                    idx_shifted=idx_shifted,
                                                                                    vector_block=vector_block,
                                                                                    extra_vecs=extra_vecs,
                                                                                    cached_nodes=cached_nodes,
                                                                                    base_cached_rounds=base_preset,
                                                                                    depth4_rounds=len(depth4_rounds),
                                                                                    depth4_cached_rounds=depth4_rounds,
                                                                                    x4=x4,
                                                                                    cached_round_depth=cached_round_depth,
                                                                                    cached_round_x=cached_round_x,
                                                                                    node_ptr_incremental=node_ptr_inc,
                                                                                    valu_select=valu_select,
                                                                                    offload_hash_op1=off_hash1,
                                                                                    offload_hash_shift=off_hash_shift,
                                                                                    offload_hash_op2=off_hash2,
                                                                                    offload_parity=off_parity,
                                                                                    offload_node_xor=off_node_xor,
                                                                                    ptr_setup_engine=ptr_engine,
                                                                                    setup_style=setup_style,
                                                                                    include_setup=True,
                                                                                )
                                                                                for off in offload_op1_list:
                                                                                    maybe_add(replace(base, offload_op1=off))
                                                                                frontier.sort(key=lambda x: x[0])
                                                                                frontier = frontier[: args.beam]

    print(f"frontier size: {len(frontier)}")
    for i, (est, spec) in enumerate(frontier[: min(5, len(frontier))], 1):
        counts, lbs = engine_bounds(spec)
        print(
            f"  {i}. est={est} selection={spec.selection_mode} x4={spec.x4} offload_op1={spec.offload_op1} "
            f"lbs={lbs}"
        )

    best = None
    best_spec = None
    for est, spec in frontier[: min(args.schedule_top, len(frontier))]:
        try:
            if args.sched_mode == "bundled":
                instrs = build_base_instrs(spec)
                cycles = sum(1 for instr in instrs if any(k != "debug" for k in instr))
            else:
                ops = build_final_ops(spec)
                if args.sched_mode == "dep":
                    instrs = schedule_ops_dep(ops)
                    cycles = len(instrs)
                else:
                    cycles = schedule_graph_with_restarts(
                        ops,
                        restarts=max(1, args.sched_restarts),
                        seed=args.seed,
                        jitter=args.sched_jitter,
                        policy=args.sched_policy,
                    )
        except Exception:
            continue
        if best is None or cycles < best:
            best = cycles
            best_spec = spec
        print(f"scheduled cycles: {cycles} (est={est})")

    print(f"best_scheduled_cycles: {best}")
    if best_spec is not None:
        print("best_scheduled_spec:")
        print(best_spec)


if __name__ == "__main__":
    main()
