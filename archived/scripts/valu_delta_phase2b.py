#!/usr/bin/env python3
"""Phase 2b: focused seed sweep — fewer seeds, only promising candidates."""
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


def sweep_seeds(base_spec, seeds, jitters, restarts_list):
    best_cyc = None
    best_params = None
    for restarts in restarts_list:
        for jitter in jitters:
            for seed in seeds:
                spec = replace(base_spec, sched_seed=seed, sched_jitter=jitter, sched_restarts=restarts)
                try:
                    cyc = bundle_cycles(spec)
                except Exception:
                    continue
                if best_cyc is None or cyc < best_cyc:
                    best_cyc = cyc
                    best_params = (seed, jitter, restarts)
    return best_cyc, best_params


def count_offloadable(spec):
    """Count how many ops are marked offloadable in the pre-offload stream."""
    from generator.scratch_layout import ScratchAlloc, build_layout
    from generator.op_list import build_ops
    scratch = ScratchAlloc()
    layout = build_layout(spec, scratch)
    spec_for_ops = replace(spec, include_setup=False) if spec.setup_style in ("packed", "none") else spec
    ordered_ops = []
    build_ops(spec_for_ops, layout, ordered_ops=ordered_ops)
    return sum(1 for op in ordered_ops if op.offloadable)


def main():
    print(f"Baseline: bundle_cycles={bundle_cycles(BASELINE)}, sched_seed={BASELINE.sched_seed}, jitter={BASELINE.sched_jitter}, restarts={BASELINE.sched_restarts}")

    # How many ops are offloadable?
    n_offloadable = count_offloadable(BASELINE)
    print(f"Offloadable ops in baseline: {n_offloadable} (cap={BASELINE.offload_op1})")
    print()

    # Focused candidates — only specs that are likely to help
    candidates = {
        # Offload tuning: find the sweet spot
        "off=780": replace(BASELINE, offload_op1=780),
        "off=790": replace(BASELINE, offload_op1=790),
        "off=800 (base)": BASELINE,
        "off=810": replace(BASELINE, offload_op1=810),
        "off=820": replace(BASELINE, offload_op1=820),
        "off=830": replace(BASELINE, offload_op1=830),
        "off=840": replace(BASELINE, offload_op1=840),
        "off=850": replace(BASELINE, offload_op1=850),
        # ptr_setup=alu (frees flow, adds alu — small impact)
        "ptr=alu": replace(BASELINE, ptr_setup_engine="alu"),
        "ptr=alu,off=810": replace(BASELINE, ptr_setup_engine="alu", offload_op1=810),
        "ptr=alu,off=820": replace(BASELINE, ptr_setup_engine="alu", offload_op1=820),
        # bitmask selection (same LB, different deps)
        "bitmask,ev=3": replace(BASELINE, selection_mode="bitmask", use_bitmask_selection=True, extra_vecs=3),
        "bitmask,ev=3,off=820": replace(BASELINE, selection_mode="bitmask", use_bitmask_selection=True, extra_vecs=3, offload_op1=820),
    }

    # Quick bundle check with original seed
    print("Quick check with original seed/jitter/restarts:")
    for label, spec in candidates.items():
        try:
            cyc = bundle_cycles(spec)
            ops = build_final_ops(spec)
            counts = count_ops(ops)
            lbs = lb_per_engine(counts)
            max_lb = max(lbs.values())
            print(f"  {label:30s} cyc={cyc:5d}  maxLB={max_lb:4d}  gap={cyc-max_lb:3d}")
        except Exception as e:
            print(f"  {label:30s} FAILED: {e}")

    # Focused seed sweep: 100 seeds, 3 jitters, 1 restarts level
    seeds = list(range(0, 500))
    jitters = [0.08, 0.1, 0.12, 0.15]
    restarts_list = [32]  # Keep restarts fixed to baseline value for speed

    print()
    print(f"Seed sweep: seeds 0..499, jitters={jitters}, restarts={restarts_list}")
    print("=" * 100)

    results = []
    for label, spec in candidates.items():
        t0 = time.time()
        best_cyc, best_params = sweep_seeds(spec, seeds, jitters, restarts_list)
        elapsed = time.time() - t0
        if best_cyc is not None:
            marker = " ***" if best_cyc < 1372 else ""
            print(f"  {label:30s} best={best_cyc:5d} (seed={best_params[0]}, j={best_params[1]}, r={best_params[2]}) [{elapsed:.1f}s]{marker}")
            results.append((best_cyc, label, best_params, spec))

    # For the top 3, do a wider sweep with restarts=64
    print()
    print("Extended sweep (restarts=64) for top 3:")
    results.sort()
    for best_cyc, label, best_params, spec in results[:3]:
        t0 = time.time()
        ext_cyc, ext_params = sweep_seeds(spec, seeds, jitters, [64])
        elapsed = time.time() - t0
        marker = " ***" if ext_cyc < 1372 else ""
        print(f"  {label:30s} best={ext_cyc:5d} (seed={ext_params[0]}, j={ext_params[1]}, r={ext_params[2]}) [{elapsed:.1f}s]{marker}")

    print()
    print("FINAL RANKING:")
    results.sort()
    for cyc, label, params, _ in results:
        marker = " <<<" if cyc < 1372 else ""
        print(f"  {cyc:5d}  {label:30s}  seed={params[0]} jitter={params[1]} restarts={params[2]}{marker}")


if __name__ == "__main__":
    main()
