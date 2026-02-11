from __future__ import annotations

"""
Compute counts from the *real* final op stream:
  build_ops(...) + apply_offload_stream(...)

This matches what build_kernel_base.build_base_instrs schedules, so it's the
right place to ground lower bounds and "hash vs non-hash" decomposition.
"""

import argparse
import importlib
import math
import os
import sys
from collections import Counter, defaultdict
from dataclasses import replace
from typing import Any

# Allow running as `python3 scripts/stream_stats.py ...` from repo root.
_REPO_ROOT = os.path.dirname(os.path.dirname(__file__))
if _REPO_ROOT not in sys.path:
    sys.path.insert(0, _REPO_ROOT)

from generator.offload import apply_offload_stream
from generator.op_list import build_ops
from generator.scratch_layout import ScratchAlloc, build_layout
from problem import SLOT_LIMITS, VLEN


def _load_spec(ref: str):
    """
    ref format:
      - module:ATTR  (ATTR is a SpecBase instance)
      - module       (expects SPEC_BASE or SPEC_UB_ENERGY_BUNDLE_1291)
    """
    if ":" in ref:
        mod, attr = ref.split(":", 1)
        m = importlib.import_module(mod)
        return getattr(m, attr)
    m = importlib.import_module(ref)
    for attr in ("SPEC_UB_ENERGY_BUNDLE_1291", "SPEC_BASE", "SPEC"):
        if hasattr(m, attr):
            return getattr(m, attr)
    raise SystemExit(f"can't find a spec in {ref!r} (expected module:ATTR)")


def _lb(counts: dict[str, int]) -> dict[str, int]:
    out: dict[str, int] = {}
    for eng, cap in SLOT_LIMITS.items():
        out[eng] = int(math.ceil(counts.get(eng, 0) / cap)) if cap else 0
    out["LB"] = max(out.values() or [0])
    return out


def _is_hash(op) -> bool:
    meta = op.meta or {}
    return "stage" in meta or "hash_stage" in meta


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument(
        "--spec",
        type=str,
        default="generator.ub_energy_bundle_1291:SPEC_UB_ENERGY_BUNDLE_1291",
        help="spec reference (module:ATTR)",
    )
    ap.add_argument(
        "--no-setup",
        action="store_true",
        help="force include_setup=False (useful to isolate steady-state work)",
    )
    ap.add_argument("--show-kinds", action="store_true")
    args = ap.parse_args()

    spec = _load_spec(args.spec)
    if args.no_setup:
        spec = replace(spec, include_setup=False)

    scratch = ScratchAlloc()
    layout = build_layout(spec, scratch)
    ordered_ops: list[Any] = []
    build_ops(spec, layout, ordered_ops=ordered_ops)
    final_ops = apply_offload_stream(spec, ordered_ops)

    def op_cost(op) -> int:
        if op.engine == "alu" and op.slot and op.slot[0] == "alu_vec":
            return VLEN
        return 1

    counts = Counter()
    for op in final_ops:
        if op.engine == "debug":
            continue
        counts[op.engine] += op_cost(op)
    lb_parts = _lb(counts)

    def fmt_counts(title: str, c: dict[str, int]) -> None:
        keys = ["valu", "alu", "load", "flow", "store"]
        print(title)
        for k in keys:
            print(f"  {k:5s} {c.get(k, 0)}")

    fmt_counts("Final Stream Counts", counts)
    print("LB Pieces (cycles at cap)")
    for eng in ["valu", "alu", "load", "flow", "store"]:
        print(f"  {eng:5s} {lb_parts[eng]}")
    print(f"  {'LB':5s} {lb_parts['LB']}")

    hash_counts = Counter()
    non_hash_counts = Counter()
    for op in final_ops:
        if op.engine == "debug":
            continue
        if _is_hash(op):
            hash_counts[op.engine] += op_cost(op)
        else:
            non_hash_counts[op.engine] += op_cost(op)
    print("Hash vs Non-Hash (by engine)")
    fmt_counts("  hash", hash_counts)
    fmt_counts("  nonhash", non_hash_counts)

    if args.show_kinds:
        by_engine_kind: dict[str, Counter[str]] = defaultdict(Counter)
        for op in final_ops:
            if op.engine == "debug":
                continue
            if op.engine == "alu" and op.slot and op.slot[0] == "alu_vec":
                _, op_name, _dest, _a, _b = op.slot
                by_engine_kind["alu"][op_name] += VLEN
            else:
                by_engine_kind[op.engine][op.slot[0]] += 1
        print("Kinds (top 20 per engine)")
        for eng in ["valu", "alu", "load", "flow", "store"]:
            if eng not in by_engine_kind:
                continue
            items = by_engine_kind[eng].most_common(20)
            s = ", ".join(f"{k}={v}" for k, v in items)
            print(f"  {eng}: {s}")


if __name__ == "__main__":
    main()
