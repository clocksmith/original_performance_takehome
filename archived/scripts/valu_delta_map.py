#!/usr/bin/env python3
"""Measure per-engine op counts and LBs for spec perturbations around the 1385 baseline."""
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
from scripts.graph_dp_auto_search import build_final_ops
from generator.build_kernel_base import build_base_instrs
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


def measure_spec(spec, label: str, baseline_counts: dict[str, int] | None = None):
    try:
        ops = build_final_ops(spec)
    except Exception as e:
        print(f"  {label}: BUILD FAILED ({e})")
        return None
    counts = count_ops(ops)
    lbs = lb_per_engine(counts)
    max_lb = max(lbs.values())
    binding = [eng for eng, lb in lbs.items() if lb == max_lb]

    deltas = {}
    if baseline_counts:
        for eng in CAPS:
            deltas[eng] = counts[eng] - baseline_counts[eng]

    delta_str = ""
    if deltas:
        parts = []
        for eng in ("valu", "alu", "load", "flow", "store"):
            d = deltas.get(eng, 0)
            if d != 0:
                parts.append(f"{eng}:{d:+d}")
        delta_str = f"  deltas=[{', '.join(parts)}]"

    print(
        f"  {label:45s} | "
        f"valu={counts['valu']:5d} alu={counts['alu']:5d} load={counts['load']:4d} flow={counts['flow']:4d} store={counts['store']:3d} | "
        f"LB: valu={lbs['valu']:4d} alu={lbs['alu']:4d} load={lbs['load']:4d} flow={lbs['flow']:4d} max={max_lb:4d} [{','.join(binding)}]"
        f"{delta_str}"
    )
    return counts, lbs, max_lb


def measure_bundle(spec, label: str, baseline_cycles: int | None = None):
    try:
        cyc = bundle_cycles(spec)
    except Exception as e:
        print(f"  {label}: BUNDLE FAILED ({e})")
        return None
    delta = ""
    if baseline_cycles is not None:
        delta = f"  delta={cyc - baseline_cycles:+d}"
    print(f"  {label:45s} | bundle_cycles={cyc:5d}{delta}")
    return cyc


def main():
    print("=" * 120)
    print("BASELINE: SPEC_UB_ENERGY_BUNDLE_1385")
    print("=" * 120)
    result = measure_spec(BASELINE, "baseline (1385)")
    if result is None:
        return
    base_counts, base_lbs, base_max_lb = result
    base_bundle = measure_bundle(BASELINE, "baseline (1385)")

    perturbations: list[tuple[str, SpecBase]] = []

    # --- x4 reductions (depth-4 caching on round 4) ---
    for x4 in (20, 16, 12, 8, 0):
        perturbations.append((f"x4={x4}", replace(BASELINE, x4=x4)))

    # --- offload_op1 ---
    for off in (600, 1000, 1200, 1600, 2000):
        perturbations.append((f"offload_op1={off}", replace(BASELINE, offload_op1=off)))

    # --- offload flags ---
    perturbations.append(("offload_hash_shift=False", replace(BASELINE, offload_hash_shift=False)))
    perturbations.append(("offload_hash_op2=False", replace(BASELINE, offload_hash_op2=False)))
    perturbations.append(("offload_hash_op1=False", replace(BASELINE, offload_hash_op1=False)))
    perturbations.append(("offload_node_xor=False", replace(BASELINE, offload_node_xor=False)))
    perturbations.append(("offload_parity=True", replace(BASELINE, offload_parity=True)))
    # Turn off all hash offloads
    perturbations.append((
        "offload_hash_all=False",
        replace(BASELINE, offload_hash_op1=False, offload_hash_shift=False, offload_hash_op2=False),
    ))

    # --- vector_block ---
    for vb in (4, 16, 32):
        perturbations.append((f"vector_block={vb}", replace(BASELINE, vector_block=vb)))

    # --- extra_vecs ---
    for ev in (2, 4):
        perturbations.append((f"extra_vecs={ev}", replace(BASELINE, extra_vecs=ev)))

    # --- base_cached_rounds variants ---
    perturbations.append((
        "drop_round14",
        replace(BASELINE, base_cached_rounds=(0, 1, 2, 11, 12, 13)),
    ))
    perturbations.append((
        "drop_round13_14",
        replace(BASELINE, base_cached_rounds=(0, 1, 2, 11, 12)),
    ))
    perturbations.append((
        "add_round3",
        replace(BASELINE, base_cached_rounds=(0, 1, 2, 3, 11, 12, 13, 14)),
    ))

    # --- selection_mode changes ---
    perturbations.append((
        "selection=bitmask,ev=3",
        replace(BASELINE, selection_mode="bitmask", use_bitmask_selection=True, extra_vecs=3),
    ))
    perturbations.append((
        "selection=mask,ev=2",
        replace(BASELINE, selection_mode="mask", extra_vecs=2),
    ))

    # --- reset_on_valu ---
    perturbations.append(("reset_on_valu=False", replace(BASELINE, reset_on_valu=False)))

    # --- shifts_on_valu ---
    perturbations.append(("shifts_on_valu=False", replace(BASELINE, shifts_on_valu=False)))

    # --- ptr_setup_engine ---
    perturbations.append(("ptr_setup=alu", replace(BASELINE, ptr_setup_engine="alu")))

    # --- Combined: reduce x4 + increase offload ---
    perturbations.append((
        "x4=16,offload=1000",
        replace(BASELINE, x4=16, offload_op1=1000),
    ))
    perturbations.append((
        "x4=8,offload=1200",
        replace(BASELINE, x4=8, offload_op1=1200),
    ))
    perturbations.append((
        "x4=16,offload=1200",
        replace(BASELINE, x4=16, offload_op1=1200),
    ))

    # --- cached_round_x: partial caching for heavy rounds ---
    perturbations.append((
        "cached_round_x={14:16}",
        replace(BASELINE, cached_round_x={14: 16}),
    ))
    perturbations.append((
        "cached_round_x={13:24,14:16}",
        replace(BASELINE, cached_round_x={13: 24, 14: 16}),
    ))

    # --- depth4_rounds=0 (disable depth-4 entirely) ---
    perturbations.append((
        "no_depth4",
        replace(BASELINE, depth4_rounds=0, depth4_cached_rounds=(), x4=0, cached_nodes=15),
    ))

    print()
    print("=" * 120)
    print("PER-ENGINE OP COUNTS + LBs  (deltas vs baseline)")
    print("=" * 120)
    results = []
    for label, spec in perturbations:
        r = measure_spec(spec, label, base_counts)
        if r is not None:
            results.append((label, spec, r))

    # Rank by max LB (lower is better)
    print()
    print("=" * 120)
    print("RANKED BY MAX LB (ascending) — top 12")
    print("=" * 120)
    ranked = sorted(results, key=lambda x: x[2][2])
    for i, (label, spec, (counts, lbs, max_lb)) in enumerate(ranked[:12]):
        binding = [eng for eng, lb in lbs.items() if lb == max_lb]
        print(
            f"  {i+1:2d}. {label:45s} max_LB={max_lb:4d} [{','.join(binding)}]  "
            f"valu_LB={lbs['valu']:4d} alu_LB={lbs['alu']:4d} load_LB={lbs['load']:4d} flow_LB={lbs['flow']:4d}"
        )

    # Now measure bundle cycles for the top candidates
    print()
    print("=" * 120)
    print("BUNDLE CYCLES for top-8 by max_LB  (+ baseline)")
    print("=" * 120)
    measure_bundle(BASELINE, "baseline (1385)", None)
    for i, (label, spec, _) in enumerate(ranked[:8]):
        measure_bundle(spec, label, base_bundle)


if __name__ == "__main__":
    main()
