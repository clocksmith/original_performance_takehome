#!/usr/bin/env python3
"""
Two-phase energy search driver.

Phase 1: fast screening (LB/graph) across multiple SA runs.
Phase 2: bundle refinement starting from top-K phase-1 specs.

This avoids mixing LB and bundle energies in a single SA chain.
"""
from __future__ import annotations

import argparse
import json
import os
import subprocess
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
ENERGY_SEARCH = ROOT / "scripts" / "energy_search.py"


@dataclass
class PhaseResult:
    path: Path
    score: dict[str, Any]
    spec: dict[str, Any]


def _load_result(path: Path) -> PhaseResult:
    with path.open("r", encoding="utf-8") as f:
        payload = json.load(f)
    return PhaseResult(path=path, score=payload.get("score", {}), spec=payload.get("spec", {}))


def _spec_key(spec: dict[str, Any]) -> str:
    return json.dumps(spec, sort_keys=True, separators=(",", ":"))


def _run_energy_search(args: list[str], *, out_path: Path, quiet: bool) -> None:
    cmd = [sys.executable, "-u", str(ENERGY_SEARCH)] + args + ["--out", str(out_path)]
    env = dict(os.environ)
    env["PYTHONUNBUFFERED"] = "1"
    if quiet:
        out_path.parent.mkdir(parents=True, exist_ok=True)
        log_path = out_path.with_suffix(".log")
        with log_path.open("w", encoding="utf-8") as handle:
            subprocess.run(cmd, stdout=handle, stderr=handle, check=True, env=env)
    else:
        subprocess.run(cmd, check=True, env=env)


def _build_phase_args(
    base_args: list[str],
    *,
    score_mode: str,
    steps: int,
    schedule_every: int,
    seed: int,
    report_every: int,
    seed_spec: Path | None,
    temp_start: float | None,
    temp_decay: float | None,
) -> list[str]:
    args = list(base_args)
    args += ["--score-mode", score_mode]
    args += ["--steps", str(steps)]
    args += ["--schedule-every", str(schedule_every)]
    args += ["--seed", str(seed)]
    args += ["--report-every", str(report_every)]
    if seed_spec is not None:
        args += ["--seed-spec", str(seed_spec)]
    if temp_start is not None:
        args += ["--temp-start", str(temp_start)]
    if temp_decay is not None:
        args += ["--temp-decay", str(temp_decay)]
    return args


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--phase1-steps", type=int, default=2000)
    ap.add_argument("--phase1-runs", type=int, default=4)
    ap.add_argument("--phase1-score-mode", type=str, default="bundle", choices=["lb", "graph", "bundle"])
    ap.add_argument("--phase1-seed", type=int, default=0)
    ap.add_argument("--phase1-report-every", type=int, default=100)
    ap.add_argument("--phase1-schedule-every", type=int, default=0)
    ap.add_argument("--phase1-seed-spec", type=str, default="")
    ap.add_argument("--phase1-temp-start", type=float, default=None)
    ap.add_argument("--phase1-temp-decay", type=float, default=None)

    ap.add_argument("--phase2-steps", type=int, default=800)
    ap.add_argument("--phase2-topk", type=int, default=5)
    ap.add_argument("--phase2-score-mode", type=str, default="bundle", choices=["bundle", "graph", "lb"])
    ap.add_argument("--phase2-seed", type=int, default=0)
    ap.add_argument("--phase2-report-every", type=int, default=50)
    ap.add_argument("--phase2-schedule-every", type=int, default=0)
    ap.add_argument("--phase2-temp-start", type=float, default=None)
    ap.add_argument("--phase2-temp-decay", type=float, default=None)

    ap.add_argument("--out-dir", type=str, default="tmp/two_phase")
    ap.add_argument("--quiet", action="store_true")

    args, passthrough = ap.parse_known_args()

    def flag_present(flag: str) -> bool:
        if flag in passthrough:
            return True
        return any(item.startswith(flag + "=") for item in passthrough)

    base_args = list(passthrough)
    if not flag_present("--mode"):
        base_args += ["--mode", "parity"]
    if not flag_present("--mutate-count"):
        base_args += ["--mutate-count", "2"]
    if not flag_present("--mutate-sched"):
        base_args += ["--mutate-sched"]
    if not flag_present("--unscheduled-score"):
        base_args += ["--unscheduled-score", "skip"]

    out_dir = Path(args.out_dir)
    out_dir.mkdir(parents=True, exist_ok=True)
    phase1_dir = out_dir / "phase1"
    phase2_dir = out_dir / "phase2"
    phase1_dir.mkdir(parents=True, exist_ok=True)
    phase2_dir.mkdir(parents=True, exist_ok=True)

    phase1_seed_spec = Path(args.phase1_seed_spec) if args.phase1_seed_spec else None

    print("two_phase: phase 1 (screen)")
    phase1_results: list[PhaseResult] = []
    for run_idx in range(args.phase1_runs):
        seed = args.phase1_seed + run_idx
        out_path = phase1_dir / f"phase1_run_{run_idx}.json"
        phase_args = _build_phase_args(
            base_args,
            score_mode=args.phase1_score_mode,
            steps=args.phase1_steps,
            schedule_every=args.phase1_schedule_every,
            seed=seed,
            report_every=args.phase1_report_every,
            seed_spec=phase1_seed_spec,
            temp_start=args.phase1_temp_start,
            temp_decay=args.phase1_temp_decay,
        )
        _run_energy_search(phase_args, out_path=out_path, quiet=args.quiet)
        phase1_results.append(_load_result(out_path))

    dedup: dict[str, PhaseResult] = {}
    for res in phase1_results:
        key = _spec_key(res.spec)
        prev = dedup.get(key)
        if prev is None or res.score.get("energy", float("inf")) < prev.score.get("energy", float("inf")):
            dedup[key] = res

    candidates = sorted(
        dedup.values(), key=lambda r: r.score.get("energy", float("inf"))
    )
    if args.phase2_topk > 0:
        candidates = candidates[: args.phase2_topk]

    print(f"two_phase: phase 1 done (candidates={len(candidates)})")

    print("two_phase: phase 2 (bundle refine)")
    phase2_results: list[PhaseResult] = []
    for idx, cand in enumerate(candidates):
        seed = args.phase2_seed + idx
        out_path = phase2_dir / f"phase2_run_{idx}.json"
        phase_args = _build_phase_args(
            base_args,
            score_mode=args.phase2_score_mode,
            steps=args.phase2_steps,
            schedule_every=args.phase2_schedule_every,
            seed=seed,
            report_every=args.phase2_report_every,
            seed_spec=cand.path,
            temp_start=args.phase2_temp_start,
            temp_decay=args.phase2_temp_decay,
        )
        _run_energy_search(phase_args, out_path=out_path, quiet=args.quiet)
        phase2_results.append(_load_result(out_path))

    if not phase2_results:
        print("two_phase: no phase2 results")
        return

    best = min(phase2_results, key=lambda r: r.score.get("energy", float("inf")))
    print("two_phase: best result")
    print(f"  energy={best.score.get('energy')} cycles={best.score.get('cycles')} lb={best.score.get('lb')}")
    print(f"  out={best.path}")


if __name__ == "__main__":
    main()
