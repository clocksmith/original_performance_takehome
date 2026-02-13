from __future__ import annotations

import argparse
import json
import math
import random
from dataclasses import asdict, replace
from pathlib import Path
from typing import Any

import os
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(__file__)))
if ROOT not in sys.path:
    sys.path.insert(0, ROOT)

from generator.build_kernel_base import build_base_instrs
from generator.ub_energy_bundle_1291 import SPEC_UB_ENERGY_BUNDLE_1291
from generator.ub_energy_bundle_1299 import SPEC_UB_ENERGY_BUNDLE_1299

SWAP_CATS = ("parity", "node_xor", "hash_op2", "hash_shift", "hash_op1")


def bundle_cycles(spec) -> int:
    instrs = build_base_instrs(spec=spec)
    return sum(1 for b in instrs if any(k != "debug" and b.get(k) for k in b))


def normalize_swaps(raw: Any) -> dict[str, list[tuple[int, int]]]:
    out: dict[str, list[tuple[int, int]]] = {}
    if not isinstance(raw, dict):
        return out
    for cat in SWAP_CATS:
        pairs = raw.get(cat)
        if not isinstance(pairs, (list, tuple)):
            continue
        keep: list[tuple[int, int]] = []
        seen_src: set[int] = set()
        for p in pairs:
            if not isinstance(p, (list, tuple)) or len(p) != 2:
                continue
            try:
                src = int(p[0])
                dst = int(p[1])
            except (TypeError, ValueError):
                continue
            if src < 0 or dst < 0 or src in seen_src:
                continue
            seen_src.add(src)
            keep.append((src, dst))
        if keep:
            out[cat] = keep
    return out


def freeze_swaps(sw: dict[str, list[tuple[int, int]]]) -> dict[str, tuple[tuple[int, int], ...]]:
    return {k: tuple(v) for k, v in sw.items() if v}


def budget_by_cat(spec) -> dict[str, int]:
    return {
        "parity": int(getattr(spec, "offload_budget_parity", 0)),
        "node_xor": int(getattr(spec, "offload_budget_node_xor", 0)),
        "hash_op2": int(getattr(spec, "offload_budget_hash_op2", 0)),
        "hash_shift": int(getattr(spec, "offload_budget_hash_shift", 0)),
        "hash_op1": int(getattr(spec, "offload_budget_hash_op1", 0)),
    }


def mutate_offload_swaps(spec, rng: random.Random) -> Any:
    sw = {k: list(v) for k, v in normalize_swaps(getattr(spec, "offload_budget_swaps", {})).items()}
    budgets = budget_by_cat(spec)
    cats = [c for c in SWAP_CATS if budgets.get(c, 0) > 0]
    if not cats:
        return spec
    cat = rng.choice(cats)
    arr = list(sw.get(cat, []))
    if not arr:
        cap = budgets[cat]
        src = rng.randrange(cap)
        arr = [(src, rng.randrange(1800))]
        sw[cat] = arr
        return replace(spec, offload_budget_swaps=freeze_swaps(sw))

    i = rng.randrange(len(arr))
    src, dst = arr[i]
    roll = rng.random()
    if roll < 0.45:
        arr[i] = (src, max(0, dst + rng.randint(-192, 192)))
    elif roll < 0.8:
        cap = budgets[cat]
        used = {s for s, _ in arr}
        choices = [s for s in range(cap) if s not in used or s == src]
        if choices:
            arr[i] = (rng.choice(choices), dst)
    elif len(arr) >= 2:
        j = rng.randrange(len(arr))
        if i != j:
            si, di = arr[i]
            sj, dj = arr[j]
            arr[i] = (si, dj)
            arr[j] = (sj, di)
    else:
        arr[i] = (src, rng.randrange(1800))
    sw[cat] = arr
    return replace(spec, offload_budget_swaps=freeze_swaps(sw))


def mutate(spec, rng: random.Random):
    selection_templates = [
        spec.selection_mode_by_round,
        {11: "eq", 12: "eq", 13: "eq", 14: "eq"},
        {3: "eq", 14: "eq", 4: "mask_precompute", 5: "mask_precompute", 6: "mask_precompute", 7: "mask_precompute", 8: "mask_precompute", 9: "mask_precompute", 10: "mask_precompute"},
        {3: "eq", 14: "eq", 4: "bitmask", 5: "bitmask", 6: "bitmask", 7: "bitmask", 8: "bitmask", 9: "bitmask", 10: "bitmask"},
        {},
    ]
    cache_depth_templates = [
        spec.cached_round_depth,
        {},
        {11: 2, 12: 2, 13: 2, 14: 2},
    ]
    cache_x_templates = [
        spec.cached_round_x,
        {},
        {11: 8, 12: 8, 13: 8, 14: 8},
        {11: 16, 12: 16, 13: 16, 14: 16},
    ]
    hash_bw_stage_templates = [
        spec.hash_bitwise_style_by_stage,
        {},
        {1: "tmp_op1"},
        {3: "tmp_op1"},
        {5: "tmp_op1"},
        {1: "tmp_op1", 3: "tmp_op1", 5: "tmp_op1"},
    ]
    hash_xor_stage_templates = [
        spec.hash_xor_style_by_stage,
        {},
        {0: "swap", 2: "swap", 4: "swap"},
        {0: "tmp_xor_const", 2: "tmp_xor_const", 4: "tmp_xor_const"},
    ]

    move = rng.choice(
        [
            "selection_mode",
            "selection_round",
            "idx_ptr",
            "offload_budget",
            "offload_swaps",
            "hash_family",
            "hash_stage_family",
            "cache_family",
            "vector_family",
            "deps_family",
            "scheduler_family",
            "combo",
        ]
    )
    if move == "selection_mode":
        return replace(spec, selection_mode=rng.choice(["eq", "mask", "bitmask", "bitmask_valu", "mask_precompute"]))
    if move == "selection_round":
        return replace(spec, selection_mode_by_round=rng.choice(selection_templates))
    if move == "idx_ptr":
        return replace(
            spec,
            idx_shifted=rng.choice([True, False]),
            node_ptr_incremental=rng.choice([True, False]),
            ptr_setup_engine=rng.choice(["flow", "alu"]),
            setup_style=rng.choice(["inline", "packed"]),
        )
    if move == "offload_budget":
        return replace(
            spec,
            offload_mode="budgeted",
            offload_budget_parity=rng.choice([352, 384, 416, 448]),
            offload_budget_node_xor=rng.choice([320, 352, 384, 416]),
            offload_budget_hash_shift=rng.choice([8, 12, 16, 24]),
            offload_budget_hash_op2=rng.choice([8, 12, 16, 24]),
            offload_hash_shift=True,
            offload_hash_op2=True,
            offload_parity=True,
            offload_node_xor=True,
        )
    if move == "offload_swaps":
        return mutate_offload_swaps(spec, rng)
    if move == "hash_family":
        hv = rng.choice(["direct", "ir", "prog"])
        hpv = rng.choice(["none", "baseline", "swap_xor", "tmp_xor_const", "tmp_op1", "pingpong"])
        return replace(
            spec,
            hash_variant=hv,
            hash_prog=None,
            hash_prog_variant=hpv,
            hash_bitwise_style=rng.choice(["inplace", "tmp_op1"]),
            hash_xor_style=rng.choice(["baseline", "swap", "tmp_xor_const"]),
            hash_linear_style=rng.choice(["muladd", "shift_add"]),
        )
    if move == "hash_stage_family":
        return replace(
            spec,
            hash_bitwise_style_by_stage=rng.choice(hash_bw_stage_templates),
            hash_xor_style_by_stage=rng.choice(hash_xor_stage_templates),
        )
    if move == "cache_family":
        return replace(
            spec,
            cached_round_depth=rng.choice(cache_depth_templates),
            cached_round_x=rng.choice(cache_x_templates),
            cached_nodes=rng.choice([7, 15, 31]),
        )
    if move == "vector_family":
        return replace(
            spec,
            emit_order=rng.choice(["auto", "round_major", "block"]),
            vector_block=rng.choice([0, 4, 8, 16]),
            extra_vecs=rng.choice([2, 3, 4]),
            valu_select=rng.choice([True, False]),
            valu_select_leaf_pairs=rng.choice([True, False]),
            valu_select_precompute_diffs=rng.choice([True, False]),
        )
    if move == "deps_family":
        return replace(
            spec,
            use_temp_deps=rng.choice([True, False]),
            use_temp_deps_extras=rng.choice([True, False]),
            temp_rename_mode=rng.choice(["off", "round", "vec", "window"]),
            temp_rename_window=rng.choice([8, 12, 16, 24]),
            sched_deps_variant=rng.choice(["full", "waw0", "nowaw", "waw0_nowar"]),
        )
    if move == "scheduler_family":
        return replace(
            spec,
            sched_seed=rng.choice([0, 1, 5, 9, 17, 33, 65]),
            sched_jitter=rng.choice([0.0, 0.05, 0.1, 0.15]),
            sched_restarts=rng.choice([1, 2, 4]),
            sched_policy=rng.choice(["baseline", "valu_first", "bottleneck_valu", "global_greedy"]),
            sched_compact=rng.choice([True, False]),
            sched_repair_passes=rng.choice([0, 1, 2, 3]),
            sched_repair_try_swap=rng.choice([True, False]),
        )
    # combo
    return replace(
        mutate_offload_swaps(spec, rng),
        sched_seed=rng.choice([0, 1, 5, 9, 17]),
        sched_policy=rng.choice(["baseline", "bottleneck_valu", "global_greedy"]),
        hash_variant=rng.choice(["direct", "ir", "prog"]),
        hash_prog=None,
        hash_prog_variant=rng.choice(["none", "swap_xor", "tmp_xor_const", "tmp_op1", "pingpong"]),
    )


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--steps", type=int, default=1800)
    ap.add_argument("--seed", type=int, default=0)
    ap.add_argument("--restarts", type=int, default=3)
    ap.add_argument("--temp-start", type=float, default=2.2)
    ap.add_argument("--temp-decay", type=float, default=0.9988)
    ap.add_argument("--report-every", type=int, default=100)
    ap.add_argument("--out", type=str, default="tmp/json/search_ub_multifamily_best.json")
    args = ap.parse_args()

    rng = random.Random(args.seed)
    seeds = [SPEC_UB_ENERGY_BUNDLE_1291, SPEC_UB_ENERGY_BUNDLE_1299]
    while len(seeds) < args.restarts:
        seeds.append(seeds[len(seeds) % 2])

    global_best = SPEC_UB_ENERGY_BUNDLE_1291
    global_best_cycles = bundle_cycles(global_best)
    rows: list[dict[str, Any]] = []
    print(f"start global_best={global_best_cycles} steps={args.steps} restarts={args.restarts}", flush=True)

    for ridx in range(args.restarts):
        curr = seeds[ridx]
        curr_cycles = bundle_cycles(curr)
        temp = args.temp_start
        print(f"restart={ridx} seed_cycles={curr_cycles}", flush=True)
        for step in range(1, args.steps + 1):
            cand = mutate(curr, rng)
            try:
                cyc = bundle_cycles(cand)
            except Exception as exc:
                rows.append({"restart": ridx, "step": step, "status": "build_error", "error": str(exc)})
                temp *= args.temp_decay
                continue

            d = cyc - curr_cycles
            accept = d <= 0 or (temp > 1e-9 and rng.random() < math.exp(-d / temp))
            if accept:
                curr = cand
                curr_cycles = cyc
            if cyc < global_best_cycles:
                global_best = cand
                global_best_cycles = cyc
                print(f"NEW restart={ridx} step={step} cycles={global_best_cycles}", flush=True)
            if step % args.report_every == 0:
                print(
                    f"[restart={ridx} step={step}] curr={curr_cycles} best={global_best_cycles} temp={temp:.4f}",
                    flush=True,
                )
            temp *= args.temp_decay

    out = {
        "best_cycles": global_best_cycles,
        "spec": asdict(global_best),
        "rows": rows,
        "search_cfg": {
            "steps": args.steps,
            "seed": args.seed,
            "restarts": args.restarts,
            "temp_start": args.temp_start,
            "temp_decay": args.temp_decay,
        },
    }
    out_path = Path(args.out)
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(json.dumps(out, indent=2), encoding="utf-8")
    print(f"done best_cycles={global_best_cycles} out={out_path}", flush=True)


if __name__ == "__main__":
    main()
