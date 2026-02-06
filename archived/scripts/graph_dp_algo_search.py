#!/usr/bin/env python3
"""
Graph/DP-style search over algorithmic spec knobs to compute a smaller upper bound
on cycles, without requiring a concrete pre-existing instruction bundle.

We generate candidate SpecBase configurations, build the op list, and use the
existing dependency scheduler to get a feasible cycle count (upper bound).
We also compute a cheap resource lower bound to prune candidates.
"""
from __future__ import annotations

from dataclasses import replace
from functools import lru_cache
import argparse
import math
import time

import os
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
if ROOT not in sys.path:
    sys.path.insert(0, ROOT)

from generator.spec_base import SPEC_BASE
from generator.scratch_layout import ScratchAlloc, build_layout
from generator.op_list import build_ops
from generator.offload import apply_offload
from generator.verify_counts import count_ops
from generator.build_kernel_base import build_base_instrs
from problem import SLOT_LIMITS

CAPS = {k: v for k, v in SLOT_LIMITS.items() if k != "debug"}


def resource_lb(counts: dict[str, int]) -> int:
    lb = 0
    for eng, cap in CAPS.items():
        total = counts.get(eng, 0)
        if total:
            lb = max(lb, math.ceil(total / cap))
    return lb


def count_cycles(instrs: list[dict]) -> int:
    # count only non-debug bundles
    return sum(1 for instr in instrs if any(k != "debug" for k in instr))


def cached_round_patterns(early_starts, late_starts, block_len=4):
    patterns = []
    for a in early_starts:
        r1 = set(range(a, a + block_len))
        for b in late_starts:
            r2 = set(range(b, b + block_len))
            if r1 & r2:
                continue
            rounds = tuple(sorted(r1 | r2))
            patterns.append(rounds)
    return patterns


def build_counts(spec) -> dict[str, int] | None:
    try:
        scratch = ScratchAlloc()
        layout = build_layout(spec, scratch)
        spec_for_ops = spec
        if getattr(spec, "setup_style", "inline") in {"packed", "none"} and getattr(spec, "include_setup", True):
            spec_for_ops = replace(spec, include_setup=False)
        ops = build_ops(spec_for_ops, layout)
        off = apply_offload(spec, ops)
        return count_ops(off)
    except Exception:
        return None


def schedule_cycles(spec) -> int | None:
    try:
        instrs = build_base_instrs(spec)
        return count_cycles(instrs)
    except Exception:
        return None


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--max-candidates", type=int, default=500)
    ap.add_argument("--time-limit", type=float, default=0.0, help="seconds; 0 = no limit")
    ap.add_argument("--offload-op1", type=str, default="0,200,400,600,800,1000,1200")
    ap.add_argument("--x4", type=str, default="8,12,15,24,32")
    ap.add_argument("--depth4-rounds", type=str, default="0,1")
    ap.add_argument("--depth4-round", type=str, default="4,5,6,7")
    ap.add_argument("--bitmask", type=str, default="0,1")
    ap.add_argument("--idx-shifted", type=str, default="0,1")
    ap.add_argument("--offload-parity", type=str, default="0,1")
    ap.add_argument("--offload-hash-op1", type=str, default="0,1")
    ap.add_argument("--offload-hash-shift", type=str, default="0,1")
    ap.add_argument("--offload-hash-op2", type=str, default="0,1")
    ap.add_argument("--offload-node-xor", type=str, default="0,1")
    ap.add_argument("--node-ptr-incremental", type=str, default="0,1")
    ap.add_argument("--ptr-setup-engine", type=str, default="flow,alu")
    ap.add_argument("--setup-style", type=str, default="packed,inline")
    ap.add_argument("--base-pattern", type=str, default="",
                    help="comma list of cached rounds, e.g. 0,1,2,11,12,13,14")
    ap.add_argument("--early-starts", type=str, default="0,1,2,3,4")
    ap.add_argument("--late-starts", type=str, default="8,9,10,11,12")
    args = ap.parse_args()

    def parse_int_list(s):
        return [int(x) for x in s.split(",") if x.strip() != ""]

    def parse_bool_list(s):
        return [bool(int(x)) for x in s.split(",") if x.strip() != ""]

    offload_list = parse_int_list(args.offload_op1)
    x4_list = parse_int_list(args.x4)
    depth4_rounds_list = parse_int_list(args.depth4_rounds)
    depth4_round_list = parse_int_list(args.depth4_round)
    bitmask_list = parse_bool_list(args.bitmask)
    idx_shifted_list = parse_bool_list(args.idx_shifted)
    offload_parity_list = parse_bool_list(args.offload_parity)
    offload_hash_op1_list = parse_bool_list(args.offload_hash_op1)
    offload_hash_shift_list = parse_bool_list(args.offload_hash_shift)
    offload_hash_op2_list = parse_bool_list(args.offload_hash_op2)
    offload_node_xor_list = parse_bool_list(args.offload_node_xor)
    node_ptr_inc_list = parse_bool_list(args.node_ptr_incremental)
    ptr_setup_engines = [x.strip() for x in args.ptr_setup_engine.split(",") if x.strip()]
    setup_styles = [x.strip() for x in args.setup_style.split(",") if x.strip()]

    if args.base_pattern:
        base_patterns = [tuple(parse_int_list(args.base_pattern))]
    else:
        early_starts = parse_int_list(args.early_starts)
        late_starts = parse_int_list(args.late_starts)
        # Cache-round patterns: two 4-round blocks, plus variants skipping one early round
        base_patterns = []
        base_patterns.extend(cached_round_patterns(early_starts, late_starts))
        # allow 7-round patterns by removing one early round (matches common \"skip r3\" variants)
        for pat in list(base_patterns):
            early = [r for r in pat if r < 8]
            late = [r for r in pat if r >= 8]
            for drop in early:
                reduced = tuple(sorted([r for r in early if r != drop] + late))
                if reduced not in base_patterns:
                    base_patterns.append(reduced)

    start = time.time()
    best = None
    best_spec = None
    tried = 0

    for base_cached in base_patterns:
        for depth4_rounds in depth4_rounds_list:
            depth4_rounds = int(depth4_rounds)
            if depth4_rounds == 0:
                depth4_choices = [()]
                x4_choices = [0]
            else:
                depth4_choices = [(r,) for r in depth4_round_list]
                x4_choices = x4_list

            for depth4_cached in depth4_choices:
                for x4 in x4_choices:
                    for bitmask in bitmask_list:
                        for idx_shifted in idx_shifted_list:
                            for offload_parity in offload_parity_list:
                                for offload_hash_op1 in offload_hash_op1_list:
                                    for offload_hash_shift in offload_hash_shift_list:
                                        for offload_hash_op2 in offload_hash_op2_list:
                                            for offload_node_xor in offload_node_xor_list:
                                                for node_ptr_inc in node_ptr_inc_list:
                                                    for ptr_engine in ptr_setup_engines:
                                                        for setup_style in setup_styles:
                                                            for offload_op1 in offload_list:
                                                                spec = replace(
                                                                    SPEC_BASE,
                                                                    base_cached_rounds=base_cached,
                                                                    depth4_rounds=depth4_rounds,
                                                                    depth4_cached_rounds=depth4_cached,
                                                                    x4=x4,
                                                                    use_bitmask_selection=bitmask,
                                                                    idx_shifted=idx_shifted,
                                                                    offload_parity=offload_parity,
                                                                    offload_hash_op1=offload_hash_op1,
                                                                    offload_hash_shift=offload_hash_shift,
                                                                    offload_hash_op2=offload_hash_op2,
                                                                    offload_node_xor=offload_node_xor,
                                                                    node_ptr_incremental=node_ptr_inc,
                                                                    ptr_setup_engine=ptr_engine,
                                                                    setup_style=setup_style,
                                                                    include_setup=True,
                                                                    offload_op1=offload_op1,
                                                                )

                                                counts = build_counts(spec)
                                                if counts is None:
                                                    continue
                                                lb = resource_lb(counts)
                                                if best is not None and lb >= best:
                                                    continue

                                                cycles = schedule_cycles(spec)
                                                if cycles is None:
                                                    continue
                                                tried += 1
                                                if best is None or cycles < best:
                                                    best = cycles
                                                    best_spec = spec
                                                    print(f"new best: {best} cycles (lb {lb})")

                                                if args.max_candidates and tried >= args.max_candidates:
                                                    print("reached max candidates")
                                                    break
                                                if args.time_limit and (time.time() - start) > args.time_limit:
                                                    print("reached time limit")
                                                    break
                                            if args.max_candidates and tried >= args.max_candidates:
                                                break
                                            if args.time_limit and (time.time() - start) > args.time_limit:
                                                break
                                        if args.max_candidates and tried >= args.max_candidates:
                                            break
                                        if args.time_limit and (time.time() - start) > args.time_limit:
                                            break
                                    if args.max_candidates and tried >= args.max_candidates:
                                        break
                                    if args.time_limit and (time.time() - start) > args.time_limit:
                                        break
                                if args.max_candidates and tried >= args.max_candidates:
                                    break
                                if args.time_limit and (time.time() - start) > args.time_limit:
                                    break
                            if args.max_candidates and tried >= args.max_candidates:
                                break
                            if args.time_limit and (time.time() - start) > args.time_limit:
                                break
                        if args.max_candidates and tried >= args.max_candidates:
                            break
                        if args.time_limit and (time.time() - start) > args.time_limit:
                            break
                    if args.max_candidates and tried >= args.max_candidates:
                        break
                    if args.time_limit and (time.time() - start) > args.time_limit:
                        break
                if args.max_candidates and tried >= args.max_candidates:
                    break
                if args.time_limit and (time.time() - start) > args.time_limit:
                    break
            if args.max_candidates and tried >= args.max_candidates:
                break
            if args.time_limit and (time.time() - start) > args.time_limit:
                break
        if args.max_candidates and tried >= args.max_candidates:
            break
        if args.time_limit and (time.time() - start) > args.time_limit:
            break

    print(f"candidates tried: {tried}")
    if best is None:
        print("no feasible spec found")
        return
    print(f"best cycles: {best}")
    print("best spec:")
    print(best_spec)


if __name__ == "__main__":
    main()
