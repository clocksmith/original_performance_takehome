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


def bundle_cycles(spec) -> int:
    instrs = build_base_instrs(spec=spec)
    cycles = 0
    for bundle in instrs:
        if any(engine != "debug" and bundle.get(engine) for engine in bundle):
            cycles += 1
    return cycles


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--top-k", type=int, default=8)
    ap.add_argument("--report-every", type=int, default=64)
    ap.add_argument("--out", type=str, default="tmp/json/sweep_hash_cache_index_micro.json")
    args = ap.parse_args()

    base = SPEC_UB_ENERGY_BUNDLE_1291
    best_cycles = bundle_cycles(base)
    best_spec = base
    print(f"start base_cycles={best_cycles}", flush=True)

    bitwise_stage_opts = [
        {},
        {1: "tmp_op1"},
        {3: "tmp_op1"},
        {5: "tmp_op1"},
        {1: "tmp_op1", 3: "tmp_op1", 5: "tmp_op1"},
    ]
    xor_stage_opts = [
        {},
        {0: "swap"},
        {2: "swap"},
        {4: "swap"},
        {0: "tmp_xor_const"},
        {2: "tmp_xor_const"},
        {4: "tmp_xor_const"},
        {0: "swap", 2: "swap", 4: "swap"},
    ]

    phase1: list[tuple[int, Any]] = []
    phase1_count = 0
    for hv in ["direct", "ir"]:
        for hb in ["inplace", "tmp_op1"]:
            for hx in ["baseline", "swap", "tmp_xor_const"]:
                for hb_stage in bitwise_stage_opts:
                    for hx_stage in xor_stage_opts:
                        spec = replace(
                            base,
                            hash_variant=hv,
                            hash_bitwise_style=hb,
                            hash_xor_style=hx,
                            hash_bitwise_style_by_stage=hb_stage,
                            hash_xor_style_by_stage=hx_stage,
                        )
                        try:
                            cyc = bundle_cycles(spec)
                        except Exception:
                            continue
                        phase1_count += 1
                        phase1.append((cyc, spec))
                        if phase1_count % args.report_every == 0:
                            print(f"phase1 [{phase1_count}] best={best_cycles}", flush=True)
                        if cyc < best_cycles:
                            best_cycles = cyc
                            best_spec = spec
                            print(f"NEW phase1 cycles={cyc}", flush=True)

    phase1.sort(key=lambda x: x[0])
    top_specs = [s for _, s in phase1[: max(1, args.top_k)]]
    print(f"phase1_done tested={phase1_count} top_k={len(top_specs)} best={best_cycles}", flush=True)

    phase2_count = 0
    for seed_spec in top_specs:
        for node_ptr_incremental in [False, True]:
            for emit_order in ["auto", "block"]:
                for vector_block in [0, 4]:
                    for extra_vecs in [3, 4]:
                        for use_temp_deps_extras in [True, False]:
                            spec = replace(
                                seed_spec,
                                node_ptr_incremental=node_ptr_incremental,
                                emit_order=emit_order,
                                vector_block=vector_block,
                                extra_vecs=extra_vecs,
                                use_temp_deps_extras=use_temp_deps_extras,
                            )
                            try:
                                cyc = bundle_cycles(spec)
                            except Exception:
                                continue
                            phase2_count += 1
                            if phase2_count % args.report_every == 0:
                                print(f"phase2 [{phase2_count}] best={best_cycles}", flush=True)
                            if cyc < best_cycles:
                                best_cycles = cyc
                                best_spec = spec
                                print(f"NEW phase2 cycles={cyc}", flush=True)

    out = {
        "base_cycles": bundle_cycles(base),
        "best_cycles": best_cycles,
        "phase1_tested": phase1_count,
        "phase2_tested": phase2_count,
        "spec": asdict(best_spec),
    }
    out_path = Path(args.out)
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(json.dumps(out, indent=2), encoding="utf-8")
    print(
        f"done best_cycles={best_cycles} phase1_tested={phase1_count} phase2_tested={phase2_count} out={out_path}",
        flush=True,
    )


if __name__ == "__main__":
    main()
