#!/usr/bin/env python3
"""
Freeze a concrete instruction schedule to JSON so generator builds are deterministic.
"""
from __future__ import annotations

import argparse
import importlib
import json
import os
import sys
from typing import Any

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
if ROOT not in sys.path:
    sys.path.insert(0, ROOT)


def _to_jsonable(obj: Any) -> Any:
    if isinstance(obj, tuple):
        return [_to_jsonable(v) for v in obj]
    if isinstance(obj, list):
        return [_to_jsonable(v) for v in obj]
    if isinstance(obj, dict):
        return {k: _to_jsonable(v) for k, v in obj.items()}
    return obj


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument(
        "--spec-module",
        type=str,
        required=True,
        help="Python module path that exports the spec object",
    )
    ap.add_argument(
        "--spec-name",
        type=str,
        required=True,
        help="Name of the spec object in the module",
    )
    ap.add_argument(
        "--output",
        type=str,
        required=True,
        help="Output JSON path for the frozen schedule",
    )
    args = ap.parse_args()

    mod = importlib.import_module(args.spec_module)
    spec = getattr(mod, args.spec_name)

    from generator.build_kernel_base import build_base_instrs

    instrs = build_base_instrs(spec)
    payload = _to_jsonable(instrs)

    out_path = os.path.abspath(args.output)
    os.makedirs(os.path.dirname(out_path), exist_ok=True)
    with open(out_path, "w", encoding="utf-8") as f:
        json.dump(payload, f, separators=(",", ":"))
    print(f"Wrote {len(payload)} cycles to {out_path}")


if __name__ == "__main__":
    main()
