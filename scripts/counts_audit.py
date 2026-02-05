#!/usr/bin/env python3
"""
Audit op counts for a spec and optionally compare to proof summary counts.
"""
from __future__ import annotations

import argparse
import importlib
import os
import re
import sys
from collections import Counter, defaultdict
from typing import Any

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
if ROOT not in sys.path:
    sys.path.insert(0, ROOT)


def _parse_md_counts(path: str) -> dict[str, int]:
    counts: dict[str, int] = {}
    pattern = re.compile(r"^[-*]\\s*([A-Za-z0-9_]+)\\s*=\\s*(\\d+)\\s*$")
    with open(path, "r", encoding="utf-8") as f:
        for line in f:
            m = pattern.match(line.strip())
            if m:
                counts[m.group(1)] = int(m.group(2))
    return counts


def _count_setup_from_prelude(spec) -> dict[str, int]:
    from generator.build_kernel_base import _build_setup_prelude
    from generator.scratch_layout import ScratchAlloc, build_layout

    scratch = ScratchAlloc()
    layout = build_layout(spec, scratch)
    instrs = _build_setup_prelude(spec, layout)
    counts: dict[str, int] = {}
    for instr in instrs:
        for eng, slots in instr.items():
            counts[eng] = counts.get(eng, 0) + len(slots)
    return counts


def _count_ops(spec) -> tuple[dict[str, int], dict[str, int], dict[str, list[int]]]:
    from generator.scratch_layout import ScratchAlloc, build_layout
    from generator.op_list import build_ops

    scratch = ScratchAlloc()
    layout = build_layout(spec, scratch)
    ordered: list[Any] = []
    build_ops(spec, layout, ordered_ops=ordered)

    round_counts = Counter()
    setup_counts = Counter()
    per_round: dict[str, list[int]] = defaultdict(lambda: [0] * spec.rounds)

    for op in ordered:
        meta = op.meta or {}
        if "round" in meta:
            round_counts[op.engine] += 1
            per_round[op.engine][meta["round"]] += 1
        else:
            setup_counts[op.engine] += 1

    return dict(round_counts), dict(setup_counts), per_round


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--spec-module", required=True)
    ap.add_argument("--spec-name", required=True)
    ap.add_argument("--proof-md", help="Optional LowerBound.md to compare against")
    args = ap.parse_args()

    mod = importlib.import_module(args.spec_module)
    spec = getattr(mod, args.spec_name)

    round_counts, setup_counts_inline, per_round = _count_ops(spec)
    setup_counts_packed = _count_setup_from_prelude(spec)

    print("Spec:", spec)
    print("Round counts:", round_counts)
    print("Setup counts (inline):", setup_counts_inline)
    print("Setup counts (packed prelude):", setup_counts_packed)

    total_counts = Counter(round_counts) + Counter(setup_counts_packed)
    print("Total counts (round + packed setup):", dict(total_counts))

    if "valu" in per_round:
        vals = per_round["valu"]
        print("Per-round valu min/max:", min(vals), max(vals))

    if args.proof_md:
        md_counts = _parse_md_counts(args.proof_md)
        if not md_counts:
            print("No counts found in proof md.")
        else:
            print("Proof md counts:", md_counts)
            for key, val in sorted(md_counts.items()):
                if key in total_counts:
                    delta = total_counts[key] - val
                    print(f"diff {key}: codegen {total_counts[key]} vs proof {val} (delta {delta})")


if __name__ == "__main__":
    main()
