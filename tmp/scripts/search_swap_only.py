from __future__ import annotations

import argparse
import json
import math
import os
import random
import sys
from dataclasses import asdict, replace
from pathlib import Path
from typing import Any

_REPO_ROOT = os.path.dirname(os.path.dirname(os.path.dirname(__file__)))
if _REPO_ROOT not in sys.path:
    sys.path.insert(0, _REPO_ROOT)

from generator.build_kernel_base import build_base_instrs
from generator.ub_energy_bundle_1291 import SPEC_UB_ENERGY_BUNDLE_1291

SWAP_CATS = ["parity", "node_xor", "hash_op2", "hash_shift", "hash_op1"]


def bundle_cycles(spec) -> int:
    instrs = build_base_instrs(spec=spec)
    cycles = 0
    for bundle in instrs:
        if any(engine != "debug" and bundle.get(engine) for engine in bundle):
            cycles += 1
    return cycles


def normalize_swaps(raw: Any) -> dict[str, tuple[tuple[int, int], ...]]:
    out: dict[str, tuple[tuple[int, int], ...]] = {}
    if not isinstance(raw, dict):
        return out
    for cat, pairs in raw.items():
        if cat not in SWAP_CATS:
            continue
        if not isinstance(pairs, (list, tuple)):
            continue
        seen_src: set[int] = set()
        keep: list[tuple[int, int]] = []
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
            keep.append((src, dst))
        if keep:
            out[cat] = tuple(keep)
    return out


def budget_by_cat(spec) -> dict[str, int]:
    return {
        "parity": int(getattr(spec, "offload_budget_parity", 0)),
        "node_xor": int(getattr(spec, "offload_budget_node_xor", 0)),
        "hash_op2": int(getattr(spec, "offload_budget_hash_op2", 0)),
        "hash_shift": int(getattr(spec, "offload_budget_hash_shift", 0)),
        "hash_op1": int(getattr(spec, "offload_budget_hash_op1", 0)),
    }


def mutate_swaps(
    rng: random.Random,
    spec,
    *,
    max_per_cat: int,
    dst_hi: int,
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
    elif action < 0.35 and arr:
        # Retarget one existing source.
        i = rng.randrange(len(arr))
        src, _old = arr[i]
        arr[i] = (src, rng.randrange(dst_hi))
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


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--steps", type=int, default=1200)
    ap.add_argument("--seed", type=int, default=0)
    ap.add_argument("--temp-start", type=float, default=2.0)
    ap.add_argument("--temp-decay", type=float, default=0.998)
    ap.add_argument("--max-per-cat", type=int, default=10)
    ap.add_argument("--dst-hi", type=int, default=1500)
    ap.add_argument("--report-every", type=int, default=100)
    ap.add_argument("--out", type=str, default="tmp/json/search_swap_only_best.json")
    args = ap.parse_args()

    rng = random.Random(args.seed)
    base = SPEC_UB_ENERGY_BUNDLE_1291
    curr = base
    curr_cycles = bundle_cycles(curr)
    best = curr
    best_cycles = curr_cycles
    temp = args.temp_start

    print(f"start cycles={curr_cycles} steps={args.steps} seed={args.seed}", flush=True)
    for step in range(1, args.steps + 1):
        cand_swaps = mutate_swaps(
            rng,
            curr,
            max_per_cat=args.max_per_cat,
            dst_hi=args.dst_hi,
        )
        cand = replace(curr, offload_budget_swaps=cand_swaps)
        cand_cycles = bundle_cycles(cand)

        delta = cand_cycles - curr_cycles
        accept = delta <= 0
        if not accept and temp > 1e-9:
            accept = rng.random() < math.exp(-delta / temp)
        if accept:
            curr = cand
            curr_cycles = cand_cycles
        if cand_cycles < best_cycles:
            best = cand
            best_cycles = cand_cycles
            print(f"NEW step={step} cycles={best_cycles}", flush=True)
            print(json.dumps(asdict(best)["offload_budget_swaps"], sort_keys=True), flush=True)
        if step % args.report_every == 0:
            print(f"[{step}] curr={curr_cycles} best={best_cycles} temp={temp:.4f}", flush=True)
        temp *= args.temp_decay

    out = {
        "best_cycles": best_cycles,
        "best_swaps": asdict(best)["offload_budget_swaps"],
        "spec": asdict(best),
    }
    out_path = Path(args.out)
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(json.dumps(out, indent=2), encoding="utf-8")
    print(f"done best_cycles={best_cycles} out={out_path}", flush=True)


if __name__ == "__main__":
    main()
