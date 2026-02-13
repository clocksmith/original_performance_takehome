from __future__ import annotations

import argparse
import json
import math
import random
from dataclasses import asdict, replace
from pathlib import Path
import os
import sys
from typing import Any

_REPO_ROOT = os.path.dirname(os.path.dirname(os.path.dirname(__file__)))
if _REPO_ROOT not in sys.path:
    sys.path.insert(0, _REPO_ROOT)

from generator.build_kernel_base import build_base_instrs
from generator.spec_base import SpecBase
from generator.ub_energy_bundle_1291 import SPEC_UB_ENERGY_BUNDLE_1291


SCHED_POLICIES = [
    "baseline",
    "valu_first",
    "bottleneck_valu",
    "global_greedy",
    "baseline_gang_offload",
    "bottleneck_valu_gang_offload",
]
DEPS_VARIANTS = [
    "full",
    "nowar",
    "nowaw",
    "nowaw_nowar",
    "waw0",
    "waw0_nowar",
    "waw0all",
    "waw0all_nowar",
]
TEMP_RENAME_MODES = ["off", "round", "vec", "window", "op"]
JITTERS = [0.0, 0.02, 0.05, 0.08, 0.1, 0.12, 0.15, 0.2]
RESTARTS = [1, 2, 4, 8, 16, 32, 64, 128]
SEEDS = list(range(0, 128))
WINDOWS = [4, 8, 12, 16, 24, 32]
SWAP_CATS = ["parity", "node_xor", "hash_op2", "hash_shift", "hash_op1"]


def bundle_cycles(spec: SpecBase) -> int:
    instrs = build_base_instrs(spec=spec)
    cycles = 0
    for bundle in instrs:
        if any(engine != "debug" and bundle.get(engine) for engine in bundle):
            cycles += 1
    return cycles


def budget_by_cat(spec: SpecBase) -> dict[str, int]:
    return {
        "parity": int(getattr(spec, "offload_budget_parity", 0)),
        "node_xor": int(getattr(spec, "offload_budget_node_xor", 0)),
        "hash_op2": int(getattr(spec, "offload_budget_hash_op2", 0)),
        "hash_shift": int(getattr(spec, "offload_budget_hash_shift", 0)),
        "hash_op1": int(getattr(spec, "offload_budget_hash_op1", 0)),
    }


def normalize_swaps(value: Any) -> dict[str, tuple[tuple[int, int], ...]]:
    out: dict[str, tuple[tuple[int, int], ...]] = {}
    if not isinstance(value, dict):
        return out
    for cat, pairs in value.items():
        if cat not in SWAP_CATS:
            continue
        if not isinstance(pairs, (list, tuple)):
            continue
        per_cat: list[tuple[int, int]] = []
        seen_src: set[int] = set()
        for pair in pairs:
            if not isinstance(pair, (list, tuple)) or len(pair) != 2:
                continue
            try:
                src = int(pair[0])
                dst = int(pair[1])
            except (TypeError, ValueError):
                continue
            if src < 0 or dst < 0 or src in seen_src:
                continue
            seen_src.add(src)
            per_cat.append((src, dst))
        if per_cat:
            out[cat] = tuple(per_cat)
    return out


def mutate_swaps(
    rng: random.Random,
    spec: SpecBase,
    max_per_cat: int = 8,
    dst_hi: int = 1500,
) -> dict[str, tuple[tuple[int, int], ...]]:
    cur = {k: list(v) for k, v in normalize_swaps(getattr(spec, "offload_budget_swaps", {})).items()}
    budgets = budget_by_cat(spec)
    eligible = [c for c in SWAP_CATS if budgets.get(c, 0) > 0]
    if not eligible:
        return {}
    cat = rng.choice(eligible)
    arr = cur.get(cat, [])
    action = rng.random()

    if action < 0.2 and arr:
        arr.pop(rng.randrange(len(arr)))
    else:
        src = rng.randrange(budgets[cat])
        dst = rng.randrange(dst_hi)
        arr = [p for p in arr if p[0] != src]
        arr.append((src, dst))
        if len(arr) > max_per_cat:
            rng.shuffle(arr)
            arr = arr[:max_per_cat]

    if arr:
        cur[cat] = arr
    elif cat in cur:
        cur.pop(cat)
    return {k: tuple(v) for k, v in cur.items() if v}


def mutate_spec(rng: random.Random, spec: SpecBase) -> SpecBase:
    move = rng.choice(
        [
            "sched_seed",
            "sched_jitter",
            "sched_restarts",
            "sched_policy",
            "sched_compact",
            "sched_deps_variant",
            "sched_repair_passes",
            "sched_repair_try_swap",
            "temp_rename_mode",
            "temp_rename_window",
            "offload_budget_swaps",
            "combo_sched",
        ]
    )
    if move == "sched_seed":
        return replace(spec, sched_seed=rng.choice(SEEDS))
    if move == "sched_jitter":
        return replace(spec, sched_jitter=rng.choice(JITTERS))
    if move == "sched_restarts":
        return replace(spec, sched_restarts=rng.choice(RESTARTS))
    if move == "sched_policy":
        return replace(spec, sched_policy=rng.choice(SCHED_POLICIES))
    if move == "sched_compact":
        return replace(spec, sched_compact=bool(rng.getrandbits(1)))
    if move == "sched_deps_variant":
        return replace(spec, sched_deps_variant=rng.choice(DEPS_VARIANTS))
    if move == "sched_repair_passes":
        return replace(spec, sched_repair_passes=rng.choice([0, 1, 2, 3, 4]))
    if move == "sched_repair_try_swap":
        return replace(spec, sched_repair_try_swap=bool(rng.getrandbits(1)))
    if move == "temp_rename_mode":
        mode = rng.choice(TEMP_RENAME_MODES)
        if mode == "window":
            return replace(spec, temp_rename_mode=mode, temp_rename_window=rng.choice(WINDOWS))
        return replace(spec, temp_rename_mode=mode)
    if move == "temp_rename_window":
        return replace(spec, temp_rename_window=rng.choice(WINDOWS))
    if move == "offload_budget_swaps":
        swaps = mutate_swaps(rng, spec)
        return replace(spec, offload_budget_swaps=swaps)

    # combo_sched
    mode = rng.choice(TEMP_RENAME_MODES)
    return replace(
        spec,
        sched_seed=rng.choice(SEEDS),
        sched_jitter=rng.choice(JITTERS),
        sched_restarts=rng.choice(RESTARTS),
        sched_policy=rng.choice(SCHED_POLICIES),
        sched_compact=bool(rng.getrandbits(1)),
        sched_deps_variant=rng.choice(DEPS_VARIANTS),
        sched_repair_passes=rng.choice([0, 1, 2, 3]),
        sched_repair_try_swap=bool(rng.getrandbits(1)),
        temp_rename_mode=mode,
        temp_rename_window=rng.choice(WINDOWS),
    )


def spec_to_json(spec: SpecBase) -> dict[str, Any]:
    return asdict(spec)


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--steps", type=int, default=800)
    ap.add_argument("--seed", type=int, default=0)
    ap.add_argument("--temp-start", type=float, default=4.0)
    ap.add_argument("--temp-decay", type=float, default=0.997)
    ap.add_argument("--report-every", type=int, default=50)
    ap.add_argument("--out", type=str, default="tmp/json/search_under_1288_best.json")
    args = ap.parse_args()

    rng = random.Random(args.seed)
    curr = SPEC_UB_ENERGY_BUNDLE_1291
    curr_cyc = bundle_cycles(curr)
    best = curr
    best_cyc = curr_cyc
    temp = args.temp_start

    print(f"start cycles={curr_cyc} seed={args.seed} steps={args.steps}", flush=True)
    for step in range(1, args.steps + 1):
        cand = mutate_spec(rng, curr)
        cand_cyc = bundle_cycles(cand)
        delta = cand_cyc - curr_cyc
        accept = delta <= 0
        if not accept and temp > 1e-9:
            accept = rng.random() < math.exp(-(delta) / temp)
        if accept:
            curr = cand
            curr_cyc = cand_cyc
        if cand_cyc < best_cyc:
            best = cand
            best_cyc = cand_cyc
            print(f"NEW step={step} cycles={best_cyc}", flush=True)
            print(json.dumps(spec_to_json(best), sort_keys=True), flush=True)
        if step % args.report_every == 0:
            print(f"[{step}] curr={curr_cyc} best={best_cyc} temp={temp:.4f}", flush=True)
        temp *= args.temp_decay

    out_path = Path(args.out)
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out = {"cycles": best_cyc, "spec": spec_to_json(best)}
    out_path.write_text(json.dumps(out, indent=2), encoding="utf-8")
    print(f"done best_cycles={best_cyc} out={out_path}", flush=True)


if __name__ == "__main__":
    main()
