#!/usr/bin/env python3
"""
Feasibility worksheet for <target cycles> under frozen caps.

We compute *exact op counts* for a structural SpecBase (before any scheduling),
then compute:
  - Throughput lower bound LB = max_e ceil(count_e / cap_e)
  - A relaxed best-case bound for VALU/ALU allowing arbitrary offload of any
    offloadable vector op:
        valu -> valu - 1
        alu  -> alu + 8

If even the relaxed bound is > target, that structural spec is infeasible
without changing the underlying op multiset (e.g. fewer hash ops).
"""

from __future__ import annotations

import os
import sys
from dataclasses import replace
from math import ceil
from typing import Any

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
if ROOT not in sys.path:
    sys.path.insert(0, ROOT)

from generator.spec_base import SPEC_BASE
from generator.scratch_layout import ScratchAlloc, build_layout
from generator.op_list import build_ops
from generator.offload import apply_offload_stream


CAPS = {"valu": 6, "alu": 12, "load": 2, "store": 2, "flow": 1}


def _count_ops(final_ops) -> dict[str, int]:
    counts = {k: 0 for k in CAPS}
    for op in final_ops:
        if op.engine == "debug":
            continue
        counts[op.engine] = counts.get(op.engine, 0) + 1
    return counts


def _lb(counts: dict[str, int]) -> dict[str, int]:
    out: dict[str, int] = {}
    for eng, cap in CAPS.items():
        c = counts.get(eng, 0)
        out[eng] = ceil(c / cap) if c else 0
    return out


def _load_breakdown(final_ops) -> dict[str, int]:
    out = {"const": 0, "load": 0, "vload": 0, "load_offset": 0}
    for op in final_ops:
        if op.engine != "load":
            continue
        name = op.slot[0]
        out[name] = out.get(name, 0) + 1
    return out


def _offloadable_inventory(ordered_ops) -> dict[str, int]:
    """
    Count offloadable VALU ops by category from meta["stage"] tags.
    Categories:
      - hash_shift/hash_op1/hash_op2 (bitwise stages only)
      - parity (idx update '&')
      - node_xor (val ^= node)
    """
    out = {"hash_shift": 0, "hash_op1": 0, "hash_op2": 0, "parity": 0, "node_xor": 0, "other": 0}
    for op in ordered_ops:
        if op.engine != "valu" or not op.offloadable:
            continue
        m = op.meta or {}
        st = m.get("stage")
        if st == "shift":
            out["hash_shift"] += 1
            continue
        if st == "op1":
            out["hash_op1"] += 1
            continue
        if st == "op2":
            out["hash_op2"] += 1
            continue

        # Non-hash offloadables don't carry a stage tag today.
        name = op.slot[0]
        if name == "&":
            out["parity"] += 1
        elif name == "^":
            out["node_xor"] += 1
        else:
            out["other"] += 1
    return out


def _best_valu_alu_bound(v0: int, a0: int, kmax: int) -> tuple[int, int]:
    """
    Compute min_k max(ceil((v0-k)/6), ceil((a0+8k)/12)) for integer k in [0,kmax].
    Return (best_cycles, best_k).
    """
    if kmax <= 0:
        return max(ceil(v0 / CAPS["valu"]), ceil(a0 / CAPS["alu"])), 0

    # Continuous optimum at intersection (v0-k)/6 == (a0+8k)/12:
    #   2*(v0-k) = a0 + 8k  =>  k = (2*v0 - a0)/10.
    k_star = int(round((2 * v0 - a0) / 10.0))
    candidates = {0, kmax, k_star}
    for dk in range(-256, 257, 8):
        candidates.add(k_star + dk)

    best = None
    best_k = 0
    for k in sorted(c for c in candidates if 0 <= c <= kmax):
        v = v0 - k
        a = a0 + 8 * k
        cyc = max(ceil(v / CAPS["valu"]), ceil(a / CAPS["alu"]))
        if best is None or cyc < best:
            best = cyc
            best_k = k
    assert best is not None
    return best, best_k


def analyze_spec(spec, *, target: int) -> dict[str, Any]:
    scratch = ScratchAlloc()
    layout = build_layout(spec, scratch)
    # Build ordered ops with *maximal* offloadable tagging so kmax reflects
    # what could be offloaded if the spec enabled it.
    spec_tag = replace(
        spec,
        offload_hash_shift=True,
        offload_hash_op1=True,
        offload_hash_op2=True,
        offload_parity=True,
        offload_node_xor=True,
    )
    ordered: list[Any] = []
    build_ops(spec_tag, layout, ordered_ops=ordered)

    # No-offload baseline counts (k=0). Offload does not change flow/load/store counts.
    spec_no = replace(
        spec_tag,
        offload_mode="budgeted",
        offload_op1=0,
        offload_budget_hash_shift=0,
        offload_budget_hash_op1=0,
        offload_budget_hash_op2=0,
        offload_budget_parity=0,
        offload_budget_node_xor=0,
        # Keep offloadable tags but do not actually offload anything.
    )
    final_no = apply_offload_stream(spec_no, ordered)
    counts_no = _count_ops(final_no)
    lb_no = _lb(counts_no)
    load_break = _load_breakdown(final_no)

    off_inv = _offloadable_inventory(ordered)
    kmax = off_inv["hash_shift"] + off_inv["hash_op1"] + off_inv["hash_op2"] + off_inv["parity"] + off_inv["node_xor"]

    best_va, best_k = _best_valu_alu_bound(counts_no["valu"], counts_no["alu"], kmax)
    other_lb = max(lb_no["load"], lb_no["flow"], lb_no["store"])
    relaxed_best = max(other_lb, best_va)

    return {
        "counts_no_offload": counts_no,
        "lb_no_offload": lb_no,
        "load_breakdown": load_break,
        "offloadable_inventory": off_inv,
        "kmax_total": kmax,
        "best_valu_alu_cycles_relaxed": best_va,
        "best_k_relaxed": best_k,
        "other_lb_cycles": other_lb,
        "relaxed_best_lb": relaxed_best,
        "target": target,
        "feasible_under_relaxed_lb": relaxed_best <= target,
        "scratch_used": scratch.ptr,
    }


def main() -> None:
    target = 1000
    base = replace(
        SPEC_BASE,
        rounds=16,
        vectors=32,
        vlen=8,
        idx_shifted=True,
        include_setup=True,
        setup_style="inline",
        extra_vecs=3,
        base_cached_rounds=(0, 1, 2, 3, 11, 12, 13, 14),
        # Scheduling knobs irrelevant for op counts.
        sched_seed=0,
        sched_jitter=0.0,
        sched_restarts=1,
    )

    Ds = [0, 8, 16, 20, 24, 32]
    sel_1114 = ["eq", "bitmask", "mask"]
    sel_15 = ["bitmask", "mask", "bitmask_valu"]
    ptr = ["flow", "alu"]
    vs_modes = [
        (False, None),
        (True, (15,)),
        (True, (11, 12, 13, 14, 15)),
        (True, None),
    ]

    rows = []
    for D in Ds:
        for s1114 in sel_1114:
            for s15 in sel_15:
                for p in ptr:
                    for valu_sel, rounds in vs_modes:
                        depth4_rounds = 1 if D > 0 else 0
                        depth4_cached = (15,) if D > 0 else ()
                        cached_nodes = 31 if D > 0 else 15

                        sel_by_round = {11: s1114, 12: s1114, 13: s1114, 14: s1114}
                        if D > 0:
                            sel_by_round[15] = s15

                        spec = replace(
                            base,
                            ptr_setup_engine=p,
                            cached_nodes=cached_nodes,
                            depth4_rounds=depth4_rounds,
                            depth4_cached_rounds=depth4_cached,
                            x4=D,
                            selection_mode="bitmask",
                            selection_mode_by_round=sel_by_round,
                            use_bitmask_selection=True,
                            valu_select=valu_sel,
                            valu_select_rounds=rounds,
                            valu_select_precompute_diffs=False,
                        )
                        try:
                            res = analyze_spec(spec, target=target)
                        except Exception:
                            continue
                        rows.append((res["relaxed_best_lb"], D, s1114, s15, p, valu_sel, rounds, res))

    rows.sort(key=lambda t: t[0])
    print(f"target={target} evaluated={len(rows)}")
    for i, (score, D, s1114, s15, p, valu_sel, rounds, res) in enumerate(rows[:30]):
        print(
            f"#{i:02d} relaxed_lb={score} "
            f"D={D} sel11-14={s1114} sel15={s15} ptr={p} "
            f"valu_select={valu_sel} rounds={rounds} "
            f"counts={res['counts_no_offload']} lb={res['lb_no_offload']} "
            f"load={res['load_breakdown']} off={res['offloadable_inventory']} "
            f"bestVA={res['best_valu_alu_cycles_relaxed']}@k={res['best_k_relaxed']} "
            f"otherLB={res['other_lb_cycles']} scratch={res['scratch_used']}"
        )


if __name__ == "__main__":
    main()
