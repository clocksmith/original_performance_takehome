from __future__ import annotations

import argparse
import importlib.util
import os
import sys
from pathlib import Path

_REPO_ROOT = os.path.dirname(os.path.dirname(os.path.dirname(__file__)))
if _REPO_ROOT not in sys.path:
    sys.path.insert(0, _REPO_ROOT)

from generator.build_kernel_base import build_base_instrs
from generator.spec_base import SpecBase


def bundle_cycles(spec: SpecBase) -> int:
    instrs = build_base_instrs(spec=spec)
    cycles = 0
    for bundle in instrs:
        if any(engine != "debug" and bundle.get(engine) for engine in bundle):
            cycles += 1
    return cycles


def load_module(path: Path):
    spec = importlib.util.spec_from_file_location(path.stem, str(path))
    if spec is None or spec.loader is None:
        raise RuntimeError(f"failed to load {path}")
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--max-restarts", type=int, default=64)
    ap.add_argument(
        "--glob",
        type=str,
        default="archived/top_level_experiments/variants/variant_*.py",
    )
    args = ap.parse_args()

    rows: list[tuple[int, str, str, int]] = []
    for path in sorted(Path(".").glob(args.glob)):
        try:
            mod = load_module(path)
        except Exception as exc:
            print(f"skip import {path}: {exc}", flush=True)
            continue

        found = False
        for name in dir(mod):
            if not name.startswith("SPEC"):
                continue
            obj = getattr(mod, name)
            if not isinstance(obj, SpecBase):
                continue
            found = True
            restarts = int(getattr(obj, "sched_restarts", 1))
            if restarts > args.max_restarts:
                print(f"skip heavy {path}:{name} restarts={restarts}", flush=True)
                continue
            try:
                cyc = bundle_cycles(obj)
            except Exception as exc:
                print(f"fail {path}:{name}: {exc}", flush=True)
                continue
            rows.append((cyc, str(path), name, restarts))
            print(f"ok {cyc} {path}:{name} restarts={restarts}", flush=True)
        if not found:
            print(f"no spec {path}", flush=True)

    rows.sort(key=lambda t: t[0])
    print("\nBEST:")
    for cyc, path, name, restarts in rows[:20]:
        print(f"{cyc:5d}  {path}:{name}  (restarts={restarts})")


if __name__ == "__main__":
    main()
