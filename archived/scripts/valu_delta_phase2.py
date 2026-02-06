#!/usr/bin/env python3
"""Phase 2: sweep sched_seed/jitter/restarts for promising perturbations."""
from __future__ import annotations

import math
import os
import sys
import time
from dataclasses import replace

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
if ROOT not in sys.path:
    sys.path.insert(0, ROOT)

from generator.spec_base import SpecBase
from generator.ub_energy_bundle_1385 import SPEC_UB_ENERGY_BUNDLE_1385 as BASELINE
from generator.build_kernel_base import build_base_instrs
from scripts.graph_dp_auto_search import build_final_ops
from problem import SLOT_LIMITS

CAPS = {k: v for k, v in SLOT_LIMITS.items() if k != "debug"}


def count_ops(ops) -> dict[str, int]:
    counts = {k: 0 for k in CAPS}
    for op in ops:
        if op.engine == "debug":
            continue
        counts[op.engine] = counts.get(op.engine, 0) + 1
    return counts


def lb_per_engine(counts: dict[str, int]) -> dict[str, int]:
    return {eng: math.ceil(counts.get(eng, 0) / cap) for eng, cap in CAPS.items()}


def bundle_cycles(spec) -> int:
    instrs = build_base_instrs(spec)
    cycles = 0
    for bundle in instrs:
        if any(engine != "debug" and bundle.get(engine) for engine in bundle):
            cycles += 1
    return cycles


def sweep_seeds(base_spec, label, seed_range, jitters, restarts_list):
    best_cyc = None
    best_params = None
    for restarts in restarts_list:
        for jitter in jitters:
            for seed in seed_range:
                spec = replace(base_spec, sched_seed=seed, sched_jitter=jitter, sched_restarts=restarts)
                try:
                    cyc = bundle_cycles(spec)
                except Exception:
                    continue
                if best_cyc is None or cyc < best_cyc:
                    best_cyc = cyc
                    best_params = (seed, jitter, restarts)
    return best_cyc, best_params


def main():
    # Baseline reference
    print(f"Baseline bundle_cycles: {bundle_cycles(BASELINE)}")
    print()

    # Phase 2a: interesting single-knob perturbations — sweep seeds
    candidates = {
        "baseline": BASELINE,
        # The offload flags don't change counts but DO change scheduling quality
        # Try different offload_op1 levels near the sweet spot
        "offload=850": replace(BASELINE, offload_op1=850),
        "offload=750": replace(BASELINE, offload_op1=750),
        "offload=900": replace(BASELINE, offload_op1=900),
        "offload=700": replace(BASELINE, offload_op1=700),
        # selection=bitmask has same LB but different structure
        "bitmask,ev=3": replace(BASELINE, selection_mode="bitmask", use_bitmask_selection=True, extra_vecs=3),
        # ptr_setup=alu frees flow slots
        "ptr_setup=alu": replace(BASELINE, ptr_setup_engine="alu"),
        # Combined
        "ptr_alu+off850": replace(BASELINE, ptr_setup_engine="alu", offload_op1=850),
        "ptr_alu+off750": replace(BASELINE, ptr_setup_engine="alu", offload_op1=750),
        # x4 reductions with balanced offload
        "x4=20": replace(BASELINE, x4=20),
        "x4=20,off=850": replace(BASELINE, x4=20, offload_op1=850),
        "x4=20,off=900": replace(BASELINE, x4=20, offload_op1=900),
    }

    # Quick LB check first
    print("=" * 100)
    print("OP COUNTS + LBs")
    print("=" * 100)
    for label, spec in candidates.items():
        try:
            ops = build_final_ops(spec)
            counts = count_ops(ops)
            lbs = lb_per_engine(counts)
            max_lb = max(lbs.values())
            binding = [eng for eng, lb in lbs.items() if lb == max_lb]
            print(
                f"  {label:30s} | valu={counts['valu']:5d} alu={counts['alu']:5d} load={counts['load']:4d} flow={counts['flow']:4d} | "
                f"LB: v={lbs['valu']:4d} a={lbs['alu']:4d} l={lbs['load']:4d} f={lbs['flow']:4d} max={max_lb} [{','.join(binding)}]"
            )
        except Exception as e:
            print(f"  {label:30s} | BUILD FAILED: {e}")

    # Seed sweep
    seeds = list(range(0, 500, 1))
    jitters = [0.05, 0.1, 0.15, 0.2]
    restarts_list = [32, 64]

    print()
    print("=" * 100)
    print(f"SEED SWEEP: seeds 0..499, jitters {jitters}, restarts {restarts_list}")
    print("=" * 100)

    results = []
    for label, spec in candidates.items():
        t0 = time.time()
        best_cyc, best_params = sweep_seeds(spec, label, seeds, jitters, restarts_list)
        elapsed = time.time() - t0
        if best_cyc is not None:
            print(f"  {label:30s} | best={best_cyc:5d}  params={best_params}  ({elapsed:.1f}s)")
            results.append((best_cyc, label, best_params))
        else:
            print(f"  {label:30s} | FAILED")

    print()
    print("=" * 100)
    print("RANKED BY BUNDLE CYCLES")
    print("=" * 100)
    results.sort()
    for cyc, label, params in results:
        marker = " ***" if cyc < 1372 else ""
        print(f"  {cyc:5d}  {label:30s}  seed={params[0]} jitter={params[1]} restarts={params[2]}{marker}")


if __name__ == "__main__":
    main()
