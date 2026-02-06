#!/usr/bin/env python3
"""
Extract per-round op counts from generator build_ops output.

Outputs JSON with:
  - setup counts (includes setup-tagged ops + final tail ops without round)
  - per-round counts (alu/valu/flow/load/store, offloadable, offload_prefix, total_ops)
"""
from __future__ import annotations

import argparse
import importlib
import json
from dataclasses import is_dataclass
from pathlib import Path
from typing import Any

from generator.op_list import build_ops
from generator.scratch_layout import ScratchAlloc, build_layout


def _resolve_spec(module, spec_name: str | None):
    if spec_name:
        spec = getattr(module, spec_name, None)
        if spec is None:
            raise ValueError(f"Spec {spec_name!r} not found in {module.__name__}")
        return spec, spec_name

    spec_candidates: list[tuple[str, Any]] = []
    for name in dir(module):
        if not name.startswith("SPEC"):
            continue
        val = getattr(module, name)
        if is_dataclass(val):
            spec_candidates.append((name, val))
    if len(spec_candidates) == 1:
        return spec_candidates[0][1], spec_candidates[0][0]
    if len(spec_candidates) == 0:
        raise ValueError(f"No SPEC* dataclass found in {module.__name__}")
    names = ", ".join(n for n, _ in spec_candidates)
    raise ValueError(f"Multiple SPEC candidates in {module.__name__}: {names}")


def _empty_counts() -> dict[str, int]:
    return {
        "alu": 0,
        "valu": 0,
        "flow": 0,
        "load": 0,
        "store": 0,
        "offloadable": 0,
        "offload_prefix": 0,
        "total_ops": 0,
    }


def _count_ops(ordered_ops, rounds: int, *, include_per_vec: bool) -> dict[str, Any]:
    setup = _empty_counts()
    tail = _empty_counts()
    per_round = {r: _empty_counts() for r in range(rounds)}
    per_vec = {r: {v: _empty_counts() for v in range(32)} for r in range(rounds)} if include_per_vec else None
    prefix_open = {r: True for r in range(rounds)}

    for op in ordered_ops:
        meta = op.meta or {}
        if meta.get("setup"):
            bucket = setup
        elif "round" in meta:
            r = int(meta["round"])
            bucket = per_round[r]
        else:
            bucket = tail

        bucket[op.engine] += 1
        bucket["total_ops"] += 1
        if op.offloadable:
            bucket["offloadable"] += 1

        if "round" in meta:
            r = int(meta["round"])
            if prefix_open[r]:
                if op.offloadable:
                    per_round[r]["offload_prefix"] += 1
                else:
                    prefix_open[r] = False
            if include_per_vec and "vec" in meta:
                v = int(meta["vec"])
                vec_bucket = per_vec[r][v]
                vec_bucket[op.engine] += 1
                vec_bucket["total_ops"] += 1
                if op.offloadable:
                    vec_bucket["offloadable"] += 1

    out = {"setup": setup, "tail": tail, "rounds": per_round}
    if include_per_vec:
        out["rounds_vec"] = per_vec
    return out


def main() -> int:
    ap = argparse.ArgumentParser(description="Extract per-round op counts from a spec module.")
    ap.add_argument("module", help="Spec module path (e.g. generator.cache_top4_d4x15_reset_offload_1016_bitmask)")
    ap.add_argument("--spec-name", help="Explicit SPEC_* name to use")
    ap.add_argument("--selection-mode", help="Override selection_mode for extraction (eq/bitmask/mask/mask_precompute)")
    ap.add_argument("--out", type=Path, help="Output JSON path (defaults to stdout)")
    ap.add_argument("--per-vec", action="store_true", help="Include per-round per-vector counts")
    args = ap.parse_args()

    module = importlib.import_module(args.module)
    spec, spec_name = _resolve_spec(module, args.spec_name)
    if args.selection_mode:
        from dataclasses import replace
        if not hasattr(spec, "selection_mode"):
            raise ValueError("selection_mode override requested but spec has no selection_mode field")
        spec = replace(spec, selection_mode=args.selection_mode)

    scratch = ScratchAlloc()
    layout = build_layout(spec, scratch)
    ordered_ops = []
    build_ops(spec, layout, ordered_ops=ordered_ops)

    counts = _count_ops(ordered_ops, rounds=getattr(spec, "rounds", 16), include_per_vec=args.per_vec)
    selection_mode = getattr(spec, "selection_mode", None)
    if selection_mode is None:
        selection_mode = "bitmask" if getattr(spec, "use_bitmask_selection", False) else "eq"

    out = {
        "module": args.module,
        "spec_name": spec_name,
        "selection_mode": selection_mode,
        "rounds": counts["rounds"],
        "setup": counts["setup"],
        "tail": counts["tail"],
        "scratch_used": scratch.ptr,
        "rounds_total": getattr(spec, "rounds", 16),
        "base_cached_rounds": list(getattr(spec, "base_cached_rounds", ())),
        "depth4_cached_rounds": list(getattr(spec, "depth4_cached_rounds", ())),
        "x4": int(getattr(spec, "x4", 0)),
        "reset_round": 10,
        "skip_update_round": 15,
    }

    text = json.dumps(out, indent=2, sort_keys=True)
    if args.out:
        args.out.write_text(text, encoding="utf-8")
    else:
        print(text)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
