#!/usr/bin/env python3
from __future__ import annotations

"""
Materialize a KernelBuilder override from an energy_search JSON output.

Usage:
  python3 scripts/materialize_variant.py tmp/best.json variant_best.py

The input JSON is expected to contain either:
  - {"spec": {...}} or
  - {"score": {...}, "spec": {...}}  (energy_search --out format)
"""

import json
import os
import sys
from typing import Any


def _die(msg: str) -> None:
    raise SystemExit(msg)


def _load_spec(path: str) -> dict[str, Any]:
    with open(path, "r", encoding="utf-8") as f:
        data = json.load(f)
    if isinstance(data, dict) and "spec" in data and isinstance(data["spec"], dict):
        return data["spec"]
    if isinstance(data, dict) and "score" in data and "spec" in data and isinstance(data["spec"], dict):
        return data["spec"]
    _die(f"Unsupported JSON format (expected top-level 'spec' dict): {path}")


def _py_repr(x: Any) -> str:
    # json produces lists for tuples; SpecBase accepts tuples for some fields but lists
    # also work for replace() as long as downstream code tolerates them. We normalize a
    # few known fields to tuples for readability.
    return repr(x)


def main(argv: list[str]) -> None:
    if len(argv) != 3:
        _die("usage: python3 scripts/materialize_variant.py <best.json> <variant.py>")
    in_path, out_path = argv[1], argv[2]
    spec = _load_spec(in_path)

    # Normalize a few fields for nicer diffs / stable types.
    for key in ("base_cached_rounds", "depth4_cached_rounds"):
        if key in spec and isinstance(spec[key], list):
            spec[key] = tuple(spec[key])

    os.makedirs(os.path.dirname(out_path) or ".", exist_ok=True)
    with open(out_path, "w", encoding="utf-8") as f:
        f.write("from __future__ import annotations\n")
        f.write("from dataclasses import replace\n\n")
        f.write("from generator.spec_base import SPEC_BASE\n")
        f.write("from generator.build_kernel_base import build_base_instrs\n")
        f.write("from perf_takehome import KernelBuilder as BaseKernelBuilder\n\n")
        f.write(f"SPEC = replace(SPEC_BASE, **{_py_repr(spec)})\n\n")
        f.write("class KernelBuilder(BaseKernelBuilder):\n")
        f.write("    def build_kernel(self, forest_height: int, n_nodes: int, batch_size: int, rounds: int):\n")
        f.write("        if forest_height == 10 and rounds == 16 and batch_size == 256:\n")
        f.write("            self.instrs = build_base_instrs(spec=SPEC)\n")
        f.write("            return\n")
        f.write("        super().build_kernel(forest_height, n_nodes, batch_size, rounds)\n")


if __name__ == "__main__":
    main(sys.argv)
