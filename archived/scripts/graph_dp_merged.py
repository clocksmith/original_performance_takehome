#!/usr/bin/env python3
"""
Merged graph/DP search:
- Auto-generates per-round op-graph choices from SpecBase knobs.
- Runs Pareto DP (from scripts/pareto_dp.py) to compute the lowest
  feasible cycle bound under ISA caps.

This computes a *lower upper bound* (feasible under cap arithmetic),
not a full dependency-aware schedule.
"""
from __future__ import annotations

from dataclasses import replace
import argparse
import math
import os
import sys
from typing import Any

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
if ROOT not in sys.path:
    sys.path.insert(0, ROOT)

from generator.spec_base import SPEC_BASE
from generator.scratch_layout import ScratchAlloc, build_layout
from generator.op_list import build_ops
from generator.ops import OpLists
from problem import SLOT_LIMITS

import scripts.pareto_dp as pareto

CAPS = {k: v for k, v in SLOT_LIMITS.items() if k != "debug"}


def _count_ops(ops: OpLists, *, round_only: bool) -> dict[str, int]:
    counts = {"alu_base": 0, "valu_raw": 0, "flow": 0, "load": 0, "store": 0}
    def include(op):
        if op.meta is None:
            return not round_only
        if round_only:
            return "round" in op.meta
        return "round" not in op.meta

    for op in ops.alu_ops:
        if include(op):
            counts["alu_base"] += 1
    for op in ops.valu_ops:
        if include(op):
            counts["valu_raw"] += 1
    for op in ops.flow_ops:
        if include(op):
            counts["flow"] += 1
    for op in ops.load_ops:
        if include(op):
            counts["load"] += 1
    for op in ops.store_ops:
        if include(op):
            counts["store"] += 1
    return counts


def _count_offloadable(ops: OpLists, *, round_only: bool) -> int:
    total = 0
    def include(op):
        if op.meta is None:
            return not round_only
        if round_only:
            return "round" in op.meta
        return "round" not in op.meta

    for op in ops.valu_ops:
        if include(op) and getattr(op, "offloadable", False):
            total += 1
    return total


def _build_choice_counts(spec) -> tuple[dict[str, int], int, int]:
    scratch = ScratchAlloc()
    layout = build_layout(spec, scratch)
    ordered: list[Any] = []
    ops = build_ops(spec, layout, ordered_ops=ordered)

    round_counts = _count_ops(ops, round_only=True)
    round_offloadable = _count_offloadable(ops, round_only=True)

    setup_counts = _count_ops(ops, round_only=False)
    setup_offloadable = _count_offloadable(ops, round_only=False)

    scratch_abs = scratch.ptr

    return (round_counts | {"offloadable": round_offloadable}), scratch_abs, (setup_counts | {"offloadable": setup_offloadable})


def _choice_spec(base_spec, cache_depth: int | None, cache_x: int) -> Any:
    spec = replace(
        base_spec,
        rounds=1,
        base_cached_rounds=(),
        depth4_rounds=0,
        depth4_cached_rounds=(),
        cached_round_depth={},
        cached_round_x={},
    )
    if cache_depth is None:
        return spec
    if cache_depth in (0, 1, 2, 3):
        return replace(spec, cached_round_depth={0: cache_depth}, cached_round_x={0: cache_x})
    if cache_depth == 4:
        return replace(spec, depth4_rounds=1, depth4_cached_rounds=(0,), x4=cache_x)
    raise ValueError(f"unknown cache_depth {cache_depth}")


def _resource_lb(counts: dict[str, int]) -> int:
    lb = 0
    for eng, cap in CAPS.items():
        key = {
            "alu": "alu_base",
            "valu": "valu_raw",
            "flow": "flow",
            "load": "load",
            "store": "store",
        }[eng]
        total = counts.get(key, 0)
        if total:
            lb = max(lb, math.ceil(total / cap))
    return lb


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--selection", choices=["eq", "bitmask", "mask", "mask_precompute"], default="eq")
    ap.add_argument("--idx-shifted", type=int, default=1)
    ap.add_argument("--offload-hash-op1", type=int, default=0)
    ap.add_argument("--offload-hash-shift", type=int, default=0)
    ap.add_argument("--offload-hash-op2", type=int, default=0)
    ap.add_argument("--offload-parity", type=int, default=1)
    ap.add_argument("--offload-node-xor", type=int, default=0)
    ap.add_argument("--node-ptr-incremental", type=int, default=0)
    ap.add_argument("--ptr-setup-engine", choices=["flow", "alu"], default="flow")
    ap.add_argument("--include-setup", type=int, default=1)
    ap.add_argument("--cache-depths", type=str, default="none,0,1,2,3,4")
    ap.add_argument("--cache-x", type=str, default="8,12,15,24,32")
    ap.add_argument("--rounds", type=int, default=16)
    ap.add_argument("--max-states", type=int, default=20000)
    ap.add_argument("--offload-order-mode", choices=["unlocked", "vector_major"], default="unlocked")
    ap.add_argument("--offload-cap", type=int, default=0, help="optional global cap on offloadable (0 = no cap)")
    args = ap.parse_args()

    cache_depths = []
    for tok in args.cache_depths.split(","):
        tok = tok.strip()
        if not tok:
            continue
        if tok == "none":
            cache_depths.append(None)
        else:
            cache_depths.append(int(tok))
    cache_xs = [int(x) for x in args.cache_x.split(",") if x.strip()]

    base_spec = replace(
        SPEC_BASE,
        selection_mode=args.selection,
        use_bitmask_selection=(args.selection == "bitmask"),
        idx_shifted=bool(args.idx_shifted),
        offload_hash_op1=bool(args.offload_hash_op1),
        offload_hash_shift=bool(args.offload_hash_shift),
        offload_hash_op2=bool(args.offload_hash_op2),
        offload_parity=bool(args.offload_parity),
        offload_node_xor=bool(args.offload_node_xor),
        node_ptr_incremental=bool(args.node_ptr_incremental),
        ptr_setup_engine=args.ptr_setup_engine,
        include_setup=bool(args.include_setup),
    )

    # Build choices for a single round
    choices = []
    setup_profile = {"alu_base": 0, "valu_raw": 0, "flow": 0, "load": 0, "store": 0, "offloadable": 0, "offload_prefix": 0, "scratch": 0}

    for depth in cache_depths:
        xs = cache_xs if depth == 4 else [base_spec.vectors]
        for cx in xs:
            spec = _choice_spec(base_spec, depth, cx)
            counts, scratch_abs, setup_counts = _build_choice_counts(spec)

            # accumulate setup (take max across choices, as setup is global)
            for k in ("alu_base", "valu_raw", "flow", "load", "store", "offloadable"):
                setup_profile[k] = max(setup_profile[k], setup_counts.get(k, 0))
            setup_profile["scratch"] = max(setup_profile["scratch"], scratch_abs)

            choice = {
                "name": f"depth={depth}_x={cx}",
                "alu_base": counts["alu_base"],
                "valu_raw": counts["valu_raw"],
                "flow": counts["flow"],
                "load": counts["load"],
                "store": counts["store"],
                "offloadable": counts["offloadable"],
                "offload_prefix": counts["offloadable"],  # optimistic; meaningful for unlocked
                "scratch_abs": scratch_abs,
            }
            choices.append(choice)

    # Build DP config
    cfg = {
        "globals": {
            "selection_mode": args.selection,
            "offload_order_mode": args.offload_order_mode,
            "scratch_mode": "max",
            "setup_profile": "default",
        },
        "setup_profiles": {"default": setup_profile},
        "rounds": [{"round": r, "choices": choices} for r in range(args.rounds)],
        "caps": {"alu": CAPS["alu"], "valu": CAPS["valu"], "flow": CAPS["flow"], "load": CAPS["load"], "store": CAPS["store"]},
        "scratch_limit": 1536,
    }

    frontier = pareto._run_dp(
        cfg,
        include_setup=bool(args.include_setup),
        caps=cfg["caps"],
        max_states=args.max_states,
        offload_order_mode=args.offload_order_mode,
        max_T=None,
        progress_log=None,
        checkpoint=None,
        checkpoint_every=0,
        resume_state=None,
        log_every_seconds=0.0,
    )

    best_T = None
    best_state = None
    for s in frontier:
        # apply optional offload cap
        if args.offload_cap and s.offloadable > args.offload_cap:
            s = pareto._apply_suffix(s, {
                "alu_base": 0,
                "valu_raw": 0,
                "flow": 0,
                "load": 0,
                "store": 0,
                "offloadable": -(s.offloadable - args.offload_cap),
                "offload_prefix": -(s.offloadable - args.offload_cap),
            })
        T = pareto._min_T_for_state(
            s,
            offload_order_mode=args.offload_order_mode,
            caps=cfg["caps"],
            max_T=None,
        )
        if T is not None and (best_T is None or T < best_T):
            best_T = T
            best_state = s

    print(f"choices: {len(choices)}")
    print(f"setup_profile: {setup_profile}")
    print(f"best_T: {best_T}")
    if best_state is not None:
        print(f"best_path (first 8 rounds): {best_state.choice_path[:8]}")


if __name__ == "__main__":
    main()
