from __future__ import annotations

import argparse
import json
import os
import sys
from dataclasses import asdict, replace
from pathlib import Path
from typing import Any

_REPO_ROOT = os.path.dirname(os.path.dirname(os.path.dirname(__file__)))
if _REPO_ROOT not in sys.path:
    sys.path.insert(0, _REPO_ROOT)

from generator.build_kernel_base import build_base_instrs
from generator.ub_energy_bundle_1291 import SPEC_UB_ENERGY_BUNDLE_1291


def bundle_cycles(instrs: list[dict[str, list[Any]]]) -> int:
    cycles = 0
    for bundle in instrs:
        if any(engine != "debug" and bundle.get(engine) for engine in bundle):
            cycles += 1
    return cycles


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--max-seed", type=int, default=1024)
    ap.add_argument("--restarts", type=int, default=1)
    ap.add_argument("--jitter", type=float, default=0.1)
    ap.add_argument("--compact", action="store_true")
    ap.add_argument("--report-every", type=int, default=64)
    ap.add_argument("--out", type=str, default="tmp/json/sweep_seed_fast.json")
    args = ap.parse_args()

    base = SPEC_UB_ENERGY_BUNDLE_1291
    best_cycles = 10**9
    best_seed = None
    for seed in range(args.max_seed):
        spec = replace(
            base,
            sched_seed=seed,
            sched_restarts=args.restarts,
            sched_jitter=args.jitter,
            sched_compact=bool(args.compact),
        )
        cyc = bundle_cycles(build_base_instrs(spec=spec))
        if cyc < best_cycles:
            best_cycles = cyc
            best_seed = seed
            print(f"NEW seed={seed} cycles={cyc}", flush=True)
        if seed % args.report_every == 0 and seed > 0:
            print(f"[{seed}] best={best_cycles} at seed={best_seed}", flush=True)

    best_spec = replace(
        base,
        sched_seed=int(best_seed or 0),
        sched_restarts=args.restarts,
        sched_jitter=args.jitter,
        sched_compact=bool(args.compact),
    )
    out = {
        "best_cycles": best_cycles,
        "best_seed": best_seed,
        "restarts": args.restarts,
        "jitter": args.jitter,
        "compact": bool(args.compact),
        "spec": asdict(best_spec),
    }
    out_path = Path(args.out)
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(json.dumps(out, indent=2), encoding="utf-8")
    print(f"done best_cycles={best_cycles} best_seed={best_seed} out={out_path}", flush=True)


if __name__ == "__main__":
    main()
