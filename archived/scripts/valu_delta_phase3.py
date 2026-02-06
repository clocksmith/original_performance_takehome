#!/usr/bin/env python3
"""
Phase 3: Two-stage sweep done right.

Stage 1: Coarse screen — restarts=64, seed=0, jitter=0.1 per candidate.
          (restarts=64 already spans seeds 0..63 internally.)
Stage 2: Refine top candidates — small jitter grid, fixed seed=0, restarts=64.

Also: push offload_op1 below offloadable count to see real flag impact.
"""
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
from generator.scratch_layout import ScratchAlloc, build_layout
from generator.op_list import build_ops
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


def count_offloadable(spec):
    scratch = ScratchAlloc()
    layout = build_layout(spec, scratch)
    spec_for_ops = replace(spec, include_setup=False) if spec.setup_style in ("packed", "none") else spec
    ordered_ops = []
    build_ops(spec_for_ops, layout, ordered_ops=ordered_ops)
    return sum(1 for op in ordered_ops if op.offloadable)


def info(spec, label):
    try:
        ops = build_final_ops(spec)
    except Exception as e:
        print(f"  {label:45s} BUILD FAILED: {e}")
        return None
    counts = count_ops(ops)
    lbs = lb_per_engine(counts)
    max_lb = max(lbs.values())
    binding = [eng for eng, lb in lbs.items() if lb == max_lb]
    return counts, lbs, max_lb, binding


def main():
    # Baseline info
    base_info = info(BASELINE, "baseline")
    base_counts, base_lbs, base_max_lb, _ = base_info
    base_cyc = bundle_cycles(BASELINE)
    print(f"BASELINE: cyc={base_cyc}, maxLB={base_max_lb}, gap={base_cyc - base_max_lb}")
    print(f"  counts: valu={base_counts['valu']} alu={base_counts['alu']} load={base_counts['load']} flow={base_counts['flow']}")
    print(f"  LBs:    valu={base_lbs['valu']} alu={base_lbs['alu']} load={base_lbs['load']} flow={base_lbs['flow']}")

    # Count offloadable ops
    n_off = count_offloadable(BASELINE)
    print(f"  offloadable ops: {n_off} (cap={BASELINE.offload_op1})")

    # Also check with flags turned off
    base_no_flags = replace(BASELINE, offload_hash_op1=False, offload_hash_shift=False, offload_hash_op2=False, offload_node_xor=False, offload_parity=False)
    n_off_no_flags = count_offloadable(base_no_flags)
    print(f"  offloadable (all flags off): {n_off_no_flags}")
    print()

    # ==========================================
    # Build candidate specs
    # ==========================================
    candidates = {}

    # A. Offload tuning near sweet spot
    for off in range(780, 830, 5):
        candidates[f"off={off}"] = replace(BASELINE, offload_op1=off)

    # B. Push offload_op1 below offloadable count to unsaturate flags
    if n_off > 0:
        for off in (n_off - 50, n_off - 20, n_off - 10, n_off, n_off + 10):
            if off > 0:
                candidates[f"off={off}(near_cap)"] = replace(BASELINE, offload_op1=off)

    # C. With flags off + offload_op1 below old offloadable count
    for off in (n_off_no_flags - 10, n_off_no_flags, n_off_no_flags + 10):
        if off > 0:
            candidates[f"off={off},noflags"] = replace(base_no_flags, offload_op1=off)

    # D. ptr_setup=alu combos
    candidates["ptr=alu"] = replace(BASELINE, ptr_setup_engine="alu")
    candidates["ptr=alu,off=810"] = replace(BASELINE, ptr_setup_engine="alu", offload_op1=810)

    # E. bitmask selection
    candidates["bitmask,ev=3"] = replace(BASELINE, selection_mode="bitmask", use_bitmask_selection=True, extra_vecs=3)

    # F. x4 reductions (depth4 lever)
    candidates["x4=20"] = replace(BASELINE, x4=20)
    candidates["x4=22"] = replace(BASELINE, x4=22)

    # G. cached_round_x partial caching
    candidates["crx={14:24}"] = replace(BASELINE, cached_round_x={14: 24})
    candidates["crx={14:20}"] = replace(BASELINE, cached_round_x={14: 20})
    candidates["crx={13:28,14:24}"] = replace(BASELINE, cached_round_x={13: 28, 14: 24})

    # H. vector_block (pure scheduling effect)
    candidates["vb=16"] = replace(BASELINE, vector_block=16)
    candidates["vb=4"] = replace(BASELINE, vector_block=4)

    # I. extra_vecs (temp-tag relief)
    candidates["ev=2"] = replace(BASELINE, extra_vecs=2)

    # J. Combos
    candidates["x4=22,crx={14:24}"] = replace(BASELINE, x4=22, cached_round_x={14: 24})
    candidates["ptr=alu,ev=2"] = replace(BASELINE, ptr_setup_engine="alu", extra_vecs=2)
    candidates["vb=16,ev=2"] = replace(BASELINE, vector_block=16, extra_vecs=2)
    candidates["ptr=alu,vb=16"] = replace(BASELINE, ptr_setup_engine="alu", vector_block=16)

    # ==========================================
    # STAGE 1: Coarse screen — restarts=64, seed=0, jitter=0.1
    # ==========================================
    print("=" * 110)
    print("STAGE 1: Coarse screen (restarts=64, seed=0, jitter=0.1)")
    print("=" * 110)

    stage1_results = []
    for label, spec in candidates.items():
        coarse_spec = replace(spec, sched_seed=0, sched_jitter=0.1, sched_restarts=64)
        t0 = time.time()
        try:
            cyc = bundle_cycles(coarse_spec)
        except Exception as e:
            print(f"  {label:45s} FAILED: {e}")
            continue
        elapsed = time.time() - t0

        r = info(coarse_spec, label)
        if r is None:
            continue
        counts, lbs, max_lb, binding = r

        delta_cyc = cyc - base_cyc
        marker = " ***" if cyc < base_cyc else ""
        print(
            f"  {label:45s} cyc={cyc:5d} ({delta_cyc:+4d}) maxLB={max_lb:4d} gap={cyc-max_lb:3d} "
            f"[{','.join(binding)}] [{elapsed:.1f}s]{marker}"
        )
        stage1_results.append((cyc, label, spec, max_lb))

    stage1_results.sort()
    print()
    print("Top 10 by coarse screen:")
    for i, (cyc, label, _, max_lb) in enumerate(stage1_results[:10]):
        delta = cyc - base_cyc
        print(f"  {i+1:2d}. {cyc:5d} ({delta:+4d}) gap={cyc-max_lb:3d}  {label}")

    # ==========================================
    # STAGE 2: Refine top 5 — jitter grid, fixed seed=0, restarts=64
    # ==========================================
    print()
    print("=" * 110)
    print("STAGE 2: Refine top 5 (jitter grid [0.05..0.25], seed=0, restarts=64)")
    print("=" * 110)

    jitters = [0.05, 0.07, 0.08, 0.1, 0.12, 0.15, 0.2, 0.25]
    stage2_results = []
    for _, label, spec, max_lb in stage1_results[:5]:
        best_cyc = None
        best_j = None
        for j in jitters:
            s = replace(spec, sched_seed=0, sched_jitter=j, sched_restarts=64)
            try:
                cyc = bundle_cycles(s)
            except Exception:
                continue
            if best_cyc is None or cyc < best_cyc:
                best_cyc = cyc
                best_j = j
        delta = best_cyc - base_cyc if best_cyc else 999
        marker = " ***" if best_cyc and best_cyc < base_cyc else ""
        print(f"  {label:45s} best={best_cyc:5d} ({delta:+4d}) jitter={best_j}{marker}")
        if best_cyc:
            stage2_results.append((best_cyc, label, spec, best_j))

    # Stage 2b: Try a few different base seeds for the top 2
    print()
    print("STAGE 2b: Top 2 × seeds [0, 100, 200, 300, 364, 400] × jitters [0.08, 0.1, 0.12, 0.15]")
    stage2_results.sort()
    base_seeds = [0, 50, 100, 200, 300, 364, 400, 450]
    refine_jitters = [0.08, 0.1, 0.12, 0.15]
    for _, label, spec, _ in stage2_results[:2]:
        best_cyc = None
        best_params = None
        for seed in base_seeds:
            for j in refine_jitters:
                s = replace(spec, sched_seed=seed, sched_jitter=j, sched_restarts=64)
                try:
                    cyc = bundle_cycles(s)
                except Exception:
                    continue
                if best_cyc is None or cyc < best_cyc:
                    best_cyc = cyc
                    best_params = (seed, j)
        delta = best_cyc - base_cyc if best_cyc else 999
        marker = " ***" if best_cyc and best_cyc < base_cyc else ""
        print(f"  {label:45s} best={best_cyc:5d} ({delta:+4d}) seed={best_params[0]} jitter={best_params[1]}{marker}")


if __name__ == "__main__":
    main()
