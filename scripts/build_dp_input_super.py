#!/usr/bin/env python3
"""
Build a wide DP input JSON by merging multiple per-round count files.

Each input JSON should match scripts/extract_round_costs.py output:
  - rounds: {round: {alu, valu, flow, load, store, offloadable, offload_prefix}}
  - setup: {alu, valu, flow, load, store, offloadable, offload_prefix} (optional)
  - selection_mode: "eq"|"bitmask"|"mask"|...

This produces a DP input with per-round choices drawn from every source.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any


def _load_counts(path: Path) -> dict[str, Any]:
    data = json.loads(path.read_text(encoding="utf-8"))
    data["_path"] = str(path)
    return data


def _setup_from_counts(data: dict[str, Any]) -> dict[str, int]:
    setup = dict(data.get("setup", {}))
    if "alu_base" not in setup and "alu" in setup:
        setup["alu_base"] = setup["alu"]
    if "valu_raw" not in setup and "valu" in setup:
        setup["valu_raw"] = setup["valu"]
    return {
        "alu_base": int(setup.get("alu_base", 0)),
        "valu_raw": int(setup.get("valu_raw", 0)),
        "flow": int(setup.get("flow", 0)),
        "load": int(setup.get("load", 0)),
        "store": int(setup.get("store", 0)),
        "offloadable": int(setup.get("offloadable", 0)),
        "offload_prefix": int(setup.get("offload_prefix", 0)),
        "scratch": int(setup.get("scratch", data.get("scratch_used", 0))),
    }


def _choice_from_round(source: dict[str, Any], round_idx: int) -> dict[str, Any]:
    counts = source["rounds"].get(str(round_idx), source["rounds"].get(round_idx))
    if counts is None:
        return {}
    choice = {
        "name": f"{source.get('selection_mode','unknown')}_r{round_idx}",
        "alu_base": int(counts.get("alu", 0)),
        "valu_raw": int(counts.get("valu", 0)),
        "flow": int(counts.get("flow", 0)),
        "load": int(counts.get("load", 0)),
        "store": int(counts.get("store", 0)),
        "offloadable": int(counts.get("offloadable", 0)),
        "offload_prefix": int(counts.get("offload_prefix", 0)),
        "selection_mode": source.get("selection_mode"),
        "source": source.get("_path"),
    }
    return choice


def main() -> int:
    ap = argparse.ArgumentParser(description="Build a wide DP input from count JSONs.")
    ap.add_argument("inputs", nargs="+", type=Path, help="Count JSON files")
    ap.add_argument("--out", type=Path, required=True, help="Output dp_input JSON")
    ap.add_argument("--selection-mode-default", default=None, help="Default global selection_mode")
    ap.add_argument("--allow-per-round-selection", action="store_true", help="Allow per-round mixing")
    ap.add_argument("--offload-order-mode", default="unlocked", choices=["round_major","vector_major","unlocked"])
    ap.add_argument("--setup-from", type=Path, default=None, help="Counts file to source setup profile")
    ap.add_argument("--scratch-limit", type=int, default=1536)
    ap.add_argument("--caps-T", type=int, default=None)
    ap.add_argument("--caps-alu", type=int, default=12)
    ap.add_argument("--caps-valu", type=int, default=6)
    ap.add_argument("--caps-flow", type=int, default=1)
    ap.add_argument("--caps-load", type=int, default=2)
    ap.add_argument("--caps-store", type=int, default=2)
    args = ap.parse_args()

    sources = [_load_counts(p) for p in args.inputs]
    rounds = max(int(s.get("rounds_total", 16)) for s in sources)

    setup_source = None
    if args.setup_from is not None:
        for s in sources:
            if Path(s["_path"]) == args.setup_from:
                setup_source = s
                break
        if setup_source is None:
            raise ValueError(f"setup-from {args.setup_from} not in inputs")
    else:
        setup_source = sources[0]

    setup_profile = _setup_from_counts(setup_source)

    dp_rounds = []
    for r in range(rounds):
        choices = []
        for s in sources:
            choice = _choice_from_round(s, r)
            if choice:
                choices.append(choice)
        dp_rounds.append({"round": r, "choices": choices})

    globals_cfg = {
        "selection_mode": args.selection_mode_default,
        "allow_per_round_selection": bool(args.allow_per_round_selection),
        "offload_order_mode": args.offload_order_mode,
    }

    out = {
        "globals": globals_cfg,
        "setup_profiles": {"default": setup_profile},
        "rounds": dp_rounds,
        "caps": {
            "T": args.caps_T,
            "alu": args.caps_alu,
            "valu": args.caps_valu,
            "flow": args.caps_flow,
            "load": args.caps_load,
            "store": args.caps_store,
        },
        "scratch_limit": args.scratch_limit,
        "sources": [s["_path"] for s in sources],
    }

    args.out.write_text(json.dumps(out, indent=2), encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
