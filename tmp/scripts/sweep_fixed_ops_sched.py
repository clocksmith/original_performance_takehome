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
from generator.spec_base import SpecBase
from generator.ub_energy_bundle_1291 import SPEC_UB_ENERGY_BUNDLE_1291


POLICIES = [
    "baseline",
    "valu_first",
    "bottleneck_valu",
    "global_greedy",
    "baseline_gang_offload",
    "bottleneck_valu_gang_offload",
]
DEPS = [
    "full",
    "nowar",
    "nowaw",
    "nowaw_nowar",
    "waw0",
    "waw0_nowar",
    "waw0all",
    "waw0all_nowar",
]
JITTERS = [0.0, 0.02, 0.05, 0.08, 0.1, 0.12, 0.15, 0.2]
RESTARTS = [1, 2, 4, 8]
SEEDS = list(range(0, 64))


def _count_cycles(instrs: list[dict[str, list[Any]]]) -> int:
    cycles = 0
    for bundle in instrs:
        if any(engine != "debug" and bundle.get(engine) for engine in bundle):
            cycles += 1
    return cycles


def build_final_ops(spec: SpecBase):
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


def score_spec(
    ops,
    setup_cycles: int,
    *,
    seed: int,
    jitter: float,
    restarts: int,
    compact: bool,
    repair_passes: int,
    repair_swap: bool,
    policy: str,
    deps_variant: str,
) -> int:
    policy2 = _apply_sched_dep_variant(policy, deps_variant)
    instrs = schedule_ops_dep(
        ops,
        seed=seed,
        jitter=jitter,
        restarts=restarts,
        compact=compact,
        repair_passes=repair_passes,
        repair_try_swap=repair_swap,
        policy=policy2,
        return_ops=False,
        target_cycles=None,
    )
    return setup_cycles + _count_cycles(instrs)


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--seed", type=int, default=0)
    ap.add_argument("--samples", type=int, default=4000)
    ap.add_argument("--report-every", type=int, default=200)
    ap.add_argument("--out", type=str, default="tmp/json/sweep_fixed_ops_sched_best.json")
    args = ap.parse_args()

    rng = random.Random(args.seed)
    base = SPEC_UB_ENERGY_BUNDLE_1291
    ops, setup_cycles = build_final_ops(base)
    base_cycles = score_spec(
        ops,
        setup_cycles,
        seed=base.sched_seed,
        jitter=base.sched_jitter,
        restarts=base.sched_restarts,
        compact=base.sched_compact,
        repair_passes=getattr(base, "sched_repair_passes", 0),
        repair_swap=getattr(base, "sched_repair_try_swap", False),
        policy=base.sched_policy,
        deps_variant=getattr(base, "sched_deps_variant", "full"),
    )
    print(f"start base_cycles={base_cycles} samples={args.samples}", flush=True)

    best_cycles = base_cycles
    best_cfg = {
        "sched_seed": base.sched_seed,
        "sched_jitter": base.sched_jitter,
        "sched_restarts": base.sched_restarts,
        "sched_compact": base.sched_compact,
        "sched_repair_passes": getattr(base, "sched_repair_passes", 0),
        "sched_repair_try_swap": getattr(base, "sched_repair_try_swap", False),
        "sched_policy": base.sched_policy,
        "sched_deps_variant": getattr(base, "sched_deps_variant", "full"),
    }

    for i in range(1, args.samples + 1):
        cfg = {
            "sched_seed": rng.choice(SEEDS),
            "sched_jitter": rng.choice(JITTERS),
            "sched_restarts": rng.choice(RESTARTS),
            "sched_compact": bool(rng.getrandbits(1)),
            "sched_repair_passes": rng.choice([0, 1, 2, 3, 4]),
            "sched_repair_try_swap": bool(rng.getrandbits(1)),
            "sched_policy": rng.choice(POLICIES),
            "sched_deps_variant": rng.choice(DEPS),
        }
        cyc = score_spec(
            ops,
            setup_cycles,
            seed=cfg["sched_seed"],
            jitter=cfg["sched_jitter"],
            restarts=cfg["sched_restarts"],
            compact=cfg["sched_compact"],
            repair_passes=cfg["sched_repair_passes"],
            repair_swap=cfg["sched_repair_try_swap"],
            policy=cfg["sched_policy"],
            deps_variant=cfg["sched_deps_variant"],
        )
        if cyc < best_cycles:
            best_cycles = cyc
            best_cfg = cfg
            print(f"NEW i={i} cycles={best_cycles} cfg={best_cfg}", flush=True)
        if i % args.report_every == 0:
            print(f"[{i}] best={best_cycles}", flush=True)

    best_spec = replace(base, **best_cfg)
    out = {
        "base_cycles": base_cycles,
        "best_cycles": best_cycles,
        "best_cfg": best_cfg,
        "spec": asdict(best_spec),
    }
    out_path = Path(args.out)
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(json.dumps(out, indent=2), encoding="utf-8")
    print(f"done best_cycles={best_cycles} out={out_path}", flush=True)


if __name__ == "__main__":
    main()
