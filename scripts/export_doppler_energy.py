#!/usr/bin/env python3
from __future__ import annotations

import argparse
import hashlib
import json
import sys
from dataclasses import asdict, fields, is_dataclass, replace
from importlib import util
from pathlib import Path
from typing import Any


def _load_spec_from_json(path: Path) -> dict[str, Any]:
    with path.open("r", encoding="utf-8") as f:
        data = json.load(f)
    if isinstance(data, dict) and "spec" in data:
        return data["spec"]
    if isinstance(data, dict):
        return data
    raise ValueError(f"Unexpected spec json format: {path}")


def _load_spec_from_module(path: Path) -> Any:
    module_name = f"energy_spec_{path.stem}"
    spec = util.spec_from_file_location(module_name, str(path))
    if spec is None or spec.loader is None:
        raise RuntimeError(f"Failed to load spec module: {path}")
    module = util.module_from_spec(spec)
    spec.loader.exec_module(module)
    for name in dir(module):
        if name.startswith("SPEC_"):
            return getattr(module, name)
    raise RuntimeError(f"No SPEC_* found in {path}")


def _build_spec(spec_dict: dict[str, Any]) -> Any:
    from generator.spec_base import SPEC_BASE, SpecBase

    field_names = {field.name for field in fields(SpecBase)}
    overrides: dict[str, Any] = {}
    for key, value in spec_dict.items():
        if key not in field_names:
            continue
        if key in {"base_cached_rounds", "depth4_cached_rounds"} and isinstance(value, list):
            overrides[key] = tuple(value)
        else:
            overrides[key] = value
    return replace(SPEC_BASE, **overrides)


def _build_deps(ops):
    from generator.schedule_dep import _reads_writes

    reads_list: list[list[int]] = []
    writes_list: list[list[int]] = []
    for op in ops:
        reads, writes = _reads_writes(op)
        reads_list.append(reads)
        writes_list.append(writes)

    deps: list[list[int]] = [[] for _ in ops]
    last_write: dict[int, int] = {}
    last_read: dict[int, int] = {}
    last_temp: dict[str, int] = {}

    for i, op in enumerate(ops):
        seen: set[int] = set()
        reads = reads_list[i]
        writes = writes_list[i]
        for addr in reads:
            if addr in last_write:
                src = last_write[addr]
                if src not in seen:
                    deps[i].append(src)
                    seen.add(src)
        for addr in writes:
            if addr in last_write:
                src = last_write[addr]
                if src not in seen:
                    deps[i].append(src)
                    seen.add(src)
            if addr in last_read:
                src = last_read[addr]
                if src not in seen:
                    deps[i].append(src)
                    seen.add(src)

        temps: list[str] = []
        if op.meta is not None:
            temp_meta = op.meta.get("temp")
            if temp_meta:
                if isinstance(temp_meta, str):
                    temps = [temp_meta]
                else:
                    temps = list(temp_meta)
        for key in temps:
            if key in last_temp:
                src = last_temp[key]
                if src not in seen:
                    deps[i].append(src)
                    seen.add(src)

        for addr in reads:
            last_read[addr] = i
        for addr in writes:
            last_write[addr] = i
            last_read.pop(addr, None)
        for key in temps:
            last_temp[key] = i

    return reads_list, writes_list, deps


def _build_baseline_bundles(ops):
    from generator.schedule_dep import schedule_ops_dep

    instrs = schedule_ops_dep(ops, return_ops=True)
    bundle_map: dict[int, int] = {}
    for cycle, bundle in enumerate(instrs):
        for op_list in bundle.values():
            for op in op_list:
                bundle_map[id(op)] = cycle
    return instrs, bundle_map


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--spec-json", type=Path, default=Path("/tmp/energy_best_bundle.json"))
    ap.add_argument(
        "--spec-module",
        type=Path,
        default=Path(__file__).resolve().parents[1] / "generator" / "ub_energy_bundle_1385.py",
    )
    ap.add_argument(
        "--output",
        type=Path,
        default=Path(__file__).resolve().parents[2]
        / "ouroboros"
        / "reploid"
        / "doppler"
        / "demo"
        / "data"
        / "vliw-simd-real.json",
    )
    ap.add_argument("--label", type=str, default="VLIW SIMD schedule (real spec)")
    args = ap.parse_args()

    repo_root = Path(__file__).resolve().parents[1]
    sys.path.insert(0, str(repo_root))

    spec_source = None
    spec = None
    spec_out = None
    if args.spec_json.exists():
        spec_dict = _load_spec_from_json(args.spec_json)
        spec = _build_spec(spec_dict)
        if is_dataclass(spec):
            spec_out = asdict(spec)
        else:
            spec_out = spec_dict
        spec_source = str(args.spec_json)
    else:
        spec = _load_spec_from_module(args.spec_module)
        if is_dataclass(spec):
            spec_out = asdict(spec)
        else:
            spec_out = spec
        spec_source = str(args.spec_module)

    from scripts.graph_dp_auto_search import build_final_ops
    from problem import SLOT_LIMITS

    ops = build_final_ops(spec)
    reads_list, writes_list, deps = _build_deps(ops)
    instrs, bundle_map = _build_baseline_bundles(ops)
    op_index_map = {id(op): idx for idx, op in enumerate(ops)}

    tasks = []
    for i, op in enumerate(ops):
        bundle = bundle_map.get(id(op))
        if bundle is None:
            raise RuntimeError(f"Op {i} not scheduled in baseline bundles")
        tasks.append(
            {
                "id": i,
                "engine": op.engine,
                "reads": reads_list[i],
                "writes": writes_list[i],
                "deps": deps[i],
                "bundle": bundle,
            }
        )

    caps = {k: v for k, v in SLOT_LIMITS.items() if k != "debug"}
    bundle_count = len(instrs)
    task_hash = hashlib.sha256(
        json.dumps(tasks, separators=(",", ":"), sort_keys=True).encode("utf-8")
    ).hexdigest()
    engine_order = ("valu", "alu", "flow", "load", "store", "debug")
    baseline_schedule = []
    for bundle in instrs:
        cycle_tasks = []
        for engine in engine_order:
            for op in bundle.get(engine, []):
                idx = op_index_map.get(id(op))
                if idx is not None:
                    cycle_tasks.append(idx)
        baseline_schedule.append(cycle_tasks)

    dependency_model = {
        "includes_raw": True,
        "includes_waw": True,
        "includes_war": True,
        "temp_hazard_tags": True,
        "read_after_read": False,
        "latency": {"default": 1},
    }

    payload = {
        "version": 2,
        "label": args.label,
        "source": spec_source,
        "spec": spec_out,
        "dag": {
            "taskCount": len(tasks),
            "caps": caps,
            "hash": task_hash,
        },
        "dependencyModel": dependency_model,
        "bundleCount": bundle_count,
        "taskCount": len(tasks),
        "baselineCycles": bundle_count,
        "caps": caps,
        "tasks": tasks,
        "baselineSchedule": baseline_schedule,
    }

    args.output.parent.mkdir(parents=True, exist_ok=True)
    with args.output.open("w", encoding="utf-8") as f:
        json.dump(payload, f)
    print(f"Wrote {args.output} bundles {bundle_count} tasks {len(tasks)}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
