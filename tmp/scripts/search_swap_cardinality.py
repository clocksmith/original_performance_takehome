from __future__ import annotations

import argparse
import json
import math
import random
import sys
from dataclasses import asdict, replace
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parents[2]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from generator.build_kernel_base import build_base_instrs
from generator.ub_energy_bundle_1291 import SPEC_UB_ENERGY_BUNDLE_1291

SWAP_CATS = ("parity", "node_xor", "hash_op2", "hash_shift", "hash_op1")


def bundle_cycles(spec) -> int:
    instrs = build_base_instrs(spec=spec)
    return sum(
        1
        for b in instrs
        if any(engine != "debug" and b.get(engine) for engine in b)
    )


def normalize_swaps(raw: Any) -> dict[str, list[tuple[int, int]]]:
    out: dict[str, list[tuple[int, int]]] = {}
    if not isinstance(raw, dict):
        return out
    for cat, pairs in raw.items():
        if cat not in SWAP_CATS or not isinstance(pairs, (list, tuple)):
            continue
        seen_src: set[int] = set()
        keep: list[tuple[int, int]] = []
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


def budget_by_cat(spec) -> dict[str, int]:
    return {
        "parity": int(getattr(spec, "offload_budget_parity", 0)),
        "node_xor": int(getattr(spec, "offload_budget_node_xor", 0)),
        "hash_op2": int(getattr(spec, "offload_budget_hash_op2", 0)),
        "hash_shift": int(getattr(spec, "offload_budget_hash_shift", 0)),
        "hash_op1": int(getattr(spec, "offload_budget_hash_op1", 0)),
    }


def as_swap_dict(sw: dict[str, list[tuple[int, int]]]) -> dict[str, tuple[tuple[int, int], ...]]:
    return {k: tuple(v) for k, v in sw.items() if v}


def mutate_preserve_counts(
    rng: random.Random,
    sw: dict[str, list[tuple[int, int]]],
    budgets: dict[str, int],
    dst_hi: int,
) -> dict[str, list[tuple[int, int]]]:
    out = {k: list(v) for k, v in sw.items()}
    cats = [c for c, v in out.items() if v and budgets.get(c, 0) > 0]
    if not cats:
        return out
    cat = rng.choice(cats)
    arr = out[cat]
    cap = budgets[cat]
    used = {src for src, _dst in arr}
    idx = rng.randrange(len(arr))
    src, dst = arr[idx]
    mode = rng.random()

    if mode < 0.45:
        delta = rng.randint(-256, 256)
        arr[idx] = (src, max(0, min(dst_hi - 1, dst + delta)))
    elif mode < 0.85:
        candidates = [s for s in range(cap) if s not in used or s == src]
        if candidates:
            nsrc = rng.choice(candidates)
            arr[idx] = (nsrc, rng.randrange(dst_hi))
    else:
        a = rng.randrange(len(arr))
        b = rng.randrange(len(arr))
        if a != b:
            sa, da = arr[a]
            sb, db = arr[b]
            arr[a] = (sa, db)
            arr[b] = (sb, da)

    out[cat] = arr
    return out


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--steps", type=int, default=1000)
    ap.add_argument("--seed", type=int, default=0)
    ap.add_argument("--temp-start", type=float, default=2.0)
    ap.add_argument("--temp-decay", type=float, default=0.999)
    ap.add_argument("--dst-hi", type=int, default=5000)
    ap.add_argument("--report-every", type=int, default=100)
    ap.add_argument("--out", type=str, default="tmp/json/search_swap_cardinality_best.json")
    args = ap.parse_args()

    rng = random.Random(args.seed)
    base = SPEC_UB_ENERGY_BUNDLE_1291
    budgets = budget_by_cat(base)
    curr_sw = normalize_swaps(getattr(base, "offload_budget_swaps", {}))
    curr = replace(base, offload_budget_swaps=as_swap_dict(curr_sw))
    curr_c = bundle_cycles(curr)
    best = curr
    best_c = curr_c
    temp = args.temp_start

    print(f"start cycles={curr_c} steps={args.steps} seed={args.seed}", flush=True)
    for step in range(1, args.steps + 1):
        cand_sw = mutate_preserve_counts(rng, curr_sw, budgets, args.dst_hi)
        cand = replace(curr, offload_budget_swaps=as_swap_dict(cand_sw))
        cand_c = bundle_cycles(cand)
        d = cand_c - curr_c
        accept = d <= 0 or (temp > 1e-9 and rng.random() < math.exp(-d / temp))
        if accept:
            curr_sw = cand_sw
            curr = cand
            curr_c = cand_c
        if cand_c < best_c:
            best = cand
            best_c = cand_c
            print(f"NEW step={step} cycles={best_c}", flush=True)
            print(json.dumps(asdict(best)["offload_budget_swaps"], sort_keys=True), flush=True)
        if step % args.report_every == 0:
            print(f"[{step}] curr={curr_c} best={best_c} temp={temp:.4f}", flush=True)
        temp *= args.temp_decay

    out = {"best_cycles": best_c, "best_swaps": asdict(best)["offload_budget_swaps"], "spec": asdict(best)}
    out_path = Path(args.out)
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(json.dumps(out, indent=2), encoding="utf-8")
    print(f"done best_cycles={best_c} out={out_path}", flush=True)


if __name__ == "__main__":
    main()
