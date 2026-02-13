from __future__ import annotations

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


def eval_grid(name: str, base_spec, updates: list[dict[str, Any]]):
    best_spec = base_spec
    best_cycles = bundle_cycles(base_spec)
    print(f"{name}: start={best_cycles} n={len(updates)}", flush=True)
    for i, upd in enumerate(updates, 1):
        spec = replace(base_spec, **upd)
        try:
            cyc = bundle_cycles(spec)
        except Exception:
            continue
        if cyc < best_cycles:
            best_cycles = cyc
            best_spec = spec
            print(f"{name}: NEW i={i} cycles={cyc} upd={upd}", flush=True)
    print(f"{name}: best={best_cycles}", flush=True)
    return best_spec, best_cycles


def main() -> None:
    base = SPEC_UB_ENERGY_BUNDLE_1291
    c0 = bundle_cycles(base)
    print(f"base_cycles={c0}", flush=True)

    # Phase 1: load-bottleneck operator (uncached node loads)
    load_updates: list[dict[str, Any]] = []
    depth_sets = [
        (),
        (4,),
        (4, 5),
        (4, 5, 6),
        (4, 5, 6, 7),
        (4, 5, 6, 7, 8),
        (4, 5, 6, 7, 8, 9, 10),
    ]
    for ds in depth_sets:
        if not ds:
            load_updates.append(
                {
                    "depth4_cached_rounds": (),
                    "x4": 0,
                    "cached_nodes": 15,
                }
            )
            continue
        for x4 in (8, 16, 24, 32):
            load_updates.append(
                {
                    "depth4_cached_rounds": ds,
                    "x4": x4,
                    "cached_nodes": 31,
                }
            )
    best1, c1 = eval_grid("phase1_load", base, load_updates)

    # Phase 2: flow-bottleneck operator (round-local selection rewrites)
    flow_updates: list[dict[str, Any]] = []
    modes = ["eq", "bitmask", "bitmask_valu", "mask", "mask_precompute"]
    for m3 in modes:
        for m14 in modes:
            for extra in (3, 4):
                flow_updates.append(
                    {
                        "selection_mode_by_round": {
                            **dict(getattr(best1, "selection_mode_by_round", {})),
                            3: m3,
                            14: m14,
                        },
                        "extra_vecs": extra,
                    }
                )
    best2, c2 = eval_grid("phase2_flow", best1, flow_updates)

    # Phase 3: hash-stage operator (stage-wise style overrides)
    hash_updates: list[dict[str, Any]] = []
    bitwise_sets = [
        {},
        {1: "tmp_op1"},
        {3: "tmp_op1"},
        {5: "tmp_op1"},
        {1: "tmp_op1", 3: "tmp_op1", 5: "tmp_op1"},
    ]
    xor_sets = [
        {},
        {0: "swap"},
        {2: "swap"},
        {4: "swap"},
        {0: "tmp_xor_const"},
        {2: "tmp_xor_const"},
        {4: "tmp_xor_const"},
        {0: "swap", 2: "swap", 4: "swap"},
    ]
    for hv in ("direct", "ir"):
        for hb in ("inplace", "tmp_op1"):
            for hx in ("baseline", "swap", "tmp_xor_const"):
                for hb_stage in bitwise_sets:
                    for hx_stage in xor_sets:
                        hash_updates.append(
                            {
                                "hash_variant": hv,
                                "hash_bitwise_style": hb,
                                "hash_xor_style": hx,
                                "hash_bitwise_style_by_stage": hb_stage,
                                "hash_xor_style_by_stage": hx_stage,
                            }
                        )
    best3, c3 = eval_grid("phase3_hash", best2, hash_updates)

    out = {
        "base_cycles": c0,
        "phase1_cycles": c1,
        "phase2_cycles": c2,
        "phase3_cycles": c3,
        "best_cycles": c3,
        "spec": asdict(best3),
    }
    out_path = Path("tmp/json/campaign_motif_rewrites.json")
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(json.dumps(out, indent=2), encoding="utf-8")
    print(f"done best={c3} out={out_path}", flush=True)


if __name__ == "__main__":
    main()
