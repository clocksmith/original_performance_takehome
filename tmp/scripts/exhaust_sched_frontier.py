from __future__ import annotations

import argparse
import json
import os
import random
import sys
from dataclasses import asdict, replace
from pathlib import Path
from typing import Any

_REPO_ROOT = os.path.dirname(os.path.dirname(os.path.dirname(__file__)))
if _REPO_ROOT not in sys.path:
    sys.path.insert(0, _REPO_ROOT)

from generator.build_kernel_base import (
    _apply_sched_dep_variant,
    _build_setup_prelude,
    _rewrite_temp_tags,
)
from generator.offload import apply_offload_stream
from generator.op_list import build_ops
from generator.scratch_layout import ScratchAlloc, build_layout
from generator.schedule_dep import schedule_ops_dep
from generator.ub_energy_bundle_1291 import SPEC_UB_ENERGY_BUNDLE_1291


def _count_cycles(instrs: list[dict[str, list[Any]]]) -> int:
    c = 0
    for b in instrs:
        if any(e != "debug" and b.get(e) for e in b):
            c += 1
    return c


def build_ops_and_setup(spec):
    scratch = ScratchAlloc()
    layout = build_layout(spec, scratch)
    setup_instrs: list[dict[str, list[tuple]]] = []
    setup_style = getattr(spec, "setup_style", "inline")
    if setup_style == "packed":
        setup_instrs = _build_setup_prelude(spec, layout)

    spec_for_ops = spec
    if setup_style in {"packed", "none"} and getattr(spec, "include_setup", True):
        spec_for_ops = replace(spec, include_setup=False)

    ordered_ops = []
    build_ops(spec_for_ops, layout, ordered_ops=ordered_ops)
    final_ops = apply_offload_stream(spec, ordered_ops)
    final_ops = _rewrite_temp_tags(spec, final_ops)
    return final_ops, _count_cycles(setup_instrs)


def eval_cfg(final_ops, setup_cycles: int, spec, cfg: dict[str, Any]) -> int:
    policy = _apply_sched_dep_variant(cfg["policy"], cfg["deps"])
    instrs = schedule_ops_dep(
        final_ops,
        return_ops=False,
        seed=cfg["seed"],
        jitter=cfg["jitter"],
        restarts=cfg["restarts"],
        compact=cfg["compact"],
        repair_passes=cfg["repair_passes"],
        repair_try_swap=cfg["repair_swap"],
        policy=policy,
        target_cycles=cfg["target"],
    )
    return setup_cycles + _count_cycles(instrs)


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--seed", type=int, default=0)
    ap.add_argument("--limit", type=int, default=1200)
    ap.add_argument("--report-every", type=int, default=50)
    ap.add_argument("--max-restarts", type=int, default=4)
    ap.add_argument("--seed-cap", type=int, default=24)
    ap.add_argument("--out", type=str, default="tmp/json/exhaust_sched_frontier.json")
    args = ap.parse_args()

    rnd = random.Random(args.seed)
    base = SPEC_UB_ENERGY_BUNDLE_1291
    final_ops, setup_cycles = build_ops_and_setup(base)

    policies = [
        "baseline",
        "valu_first",
        "bottleneck_valu",
        "global_greedy",
        "baseline_gang_offload",
        "bottleneck_valu_gang_offload",
        "global_greedy_gang_offload",
        "slack",
        "global_greedy_slack",
        "slack_gang_offload",
        "global_greedy_slack_gang_offload",
    ]
    deps = [
        "full",
        "nowar",
        "nowaw",
        "nowaw_nowar",
        "waw0",
        "waw0_nowar",
        "waw0all",
        "waw0all_nowar",
    ]
    jitters = [0.0, 0.02, 0.05, 0.08, 0.1, 0.12, 0.15]
    restarts = [r for r in [1, 2, 4, 8, 16] if r <= max(1, args.max_restarts)]
    compacts = [False, True]
    repair_passes = [0, 1, 2, 3, 4]
    repair_swap = [False, True]
    targets = [None, 1260, 1270, 1280, 1290]
    seeds = list(range(0, max(1, args.seed_cap)))

    base_cfg = {
        "policy": str(getattr(base, "sched_policy", "baseline")),
        "deps": str(getattr(base, "sched_deps_variant", "full")),
        "seed": int(getattr(base, "sched_seed", 0)),
        "jitter": float(getattr(base, "sched_jitter", 0.0)),
        "restarts": int(getattr(base, "sched_restarts", 1)),
        "compact": bool(getattr(base, "sched_compact", False)),
        "repair_passes": int(getattr(base, "sched_repair_passes", 0)),
        "repair_swap": bool(getattr(base, "sched_repair_try_swap", False)),
        "target": getattr(base, "sched_target_cycles", None),
    }
    base_cycles = eval_cfg(final_ops, setup_cycles, base, base_cfg)
    best_cycles = base_cycles
    best_cfg = dict(base_cfg)
    print(f"base_cycles={base_cycles} cfg={base_cfg}", flush=True)

    # Weighted frontier: emphasize new policies and low restart deterministic runs.
    frontier: list[dict[str, Any]] = []
    for p in policies:
        for d in deps:
            for cpt in compacts:
                for rp in repair_passes:
                    for rs in repair_swap:
                        for j in jitters:
                            # keep frontier bounded but broad: seed slices by jitter
                            seed_slice = seeds if j == 0.0 else seeds[: max(1, len(seeds) // 2)]
                            for s in seed_slice:
                                for r in restarts:
                                    if "slack" in p:
                                        for t in targets:
                                            if t is None:
                                                continue
                                            frontier.append(
                                                {
                                                    "policy": p,
                                                    "deps": d,
                                                    "seed": s,
                                                    "jitter": j,
                                                    "restarts": r,
                                                    "compact": cpt,
                                                    "repair_passes": rp,
                                                    "repair_swap": rs,
                                                    "target": t,
                                                }
                                            )
                                    else:
                                        frontier.append(
                                            {
                                                "policy": p,
                                                "deps": d,
                                                "seed": s,
                                                "jitter": j,
                                                "restarts": r,
                                                "compact": cpt,
                                                "repair_passes": rp,
                                                "repair_swap": rs,
                                                "target": None,
                                            }
                                        )

    rnd.shuffle(frontier)
    if args.limit > 0:
        frontier = frontier[: args.limit]
    print(f"evaluating={len(frontier)}", flush=True)

    tested = 0
    top_rows: list[dict[str, Any]] = []
    for cfg in frontier:
        tested += 1
        try:
            cyc = eval_cfg(final_ops, setup_cycles, base, cfg)
        except Exception as exc:
            if tested % args.report_every == 0:
                print(f"[{tested}] err={exc}", flush=True)
            continue
        row = dict(cfg)
        row["cycles"] = cyc
        top_rows.append(row)
        if cyc < best_cycles:
            best_cycles = cyc
            best_cfg = dict(cfg)
            print(f"NEW tested={tested} cycles={cyc} cfg={cfg}", flush=True)
        if tested % args.report_every == 0:
            print(f"[{tested}] best={best_cycles} frontier={len(frontier)}", flush=True)

    top_rows = sorted(top_rows, key=lambda r: r["cycles"])[:50]
    best_spec = replace(
        base,
        sched_policy=best_cfg["policy"],
        sched_deps_variant=best_cfg["deps"],
        sched_seed=best_cfg["seed"],
        sched_jitter=best_cfg["jitter"],
        sched_restarts=best_cfg["restarts"],
        sched_compact=best_cfg["compact"],
        sched_repair_passes=best_cfg["repair_passes"],
        sched_repair_try_swap=best_cfg["repair_swap"],
        sched_target_cycles=best_cfg["target"],
    )
    out = {
        "base_cycles": base_cycles,
        "tested": tested,
        "best_cycles": best_cycles,
        "best_cfg": best_cfg,
        "top_rows": top_rows,
        "spec": asdict(best_spec),
    }
    out_path = Path(args.out)
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(json.dumps(out, indent=2), encoding="utf-8")
    print(f"done tested={tested} best={best_cycles} out={out_path}", flush=True)


if __name__ == "__main__":
    main()
