from __future__ import annotations

import argparse
import json
import os
import random
import sys
from dataclasses import asdict, replace
from pathlib import Path

_REPO_ROOT = os.path.dirname(os.path.dirname(os.path.dirname(__file__)))
if _REPO_ROOT not in sys.path:
    sys.path.insert(0, _REPO_ROOT)

from generator.ub_energy_bundle_1291 import SPEC_UB_ENERGY_BUNDLE_1291
from scripts.energy_search import bundle_cycles


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--seed", type=int, default=0)
    ap.add_argument("--max-tests", type=int, default=6000)
    ap.add_argument("--report-every", type=int, default=250)
    ap.add_argument("--out", type=str, default="tmp/json/sweep_flow_bottleneck_rounds.json")
    args = ap.parse_args()

    rnd = random.Random(args.seed)
    base = SPEC_UB_ENERGY_BUNDLE_1291
    base_cycles = bundle_cycles(base)
    best_cycles = base_cycles
    best_spec = base
    rows = []

    m_opts = ["eq", "bitmask", "bitmask_valu", "mask", "mask_precompute"]
    extra_opts = [3, 4, 5, 6]
    valu_select_opts = [False, True]
    leaf_opts = [False, True]
    precompute_opts = [False, True]
    temp_dep_opts = [False, True]
    temp_extra_opts = [False, True]
    emit_opts = ["auto", "block", "round_major"]
    vector_block_opts = [0, 4, 8]
    policies = ["baseline", "bottleneck_valu", "valu_first"]
    jitters = [0.0, 0.05, 0.1]
    restarts = [1, 2, 4]
    seeds = [0, 1, 2, 3, 4, 7, 9, 11, 17, 23, 31]

    seen = set()
    tested = 0
    print(f"base={base_cycles}", flush=True)
    while tested < args.max_tests:
        cand = (
            rnd.choice(m_opts),
            rnd.choice(m_opts),
            rnd.choice(extra_opts),
            rnd.choice(valu_select_opts),
            rnd.choice(leaf_opts),
            rnd.choice(precompute_opts),
            rnd.choice(temp_dep_opts),
            rnd.choice(temp_extra_opts),
            rnd.choice(emit_opts),
            rnd.choice(vector_block_opts),
            rnd.choice(policies),
            rnd.choice(jitters),
            rnd.choice(restarts),
            rnd.choice(seeds),
        )
        if cand in seen:
            continue
        seen.add(cand)
        (
            m3,
            m14,
            ev,
            vs,
            leaf,
            pre,
            td,
            tdx,
            emit,
            vb,
            pol,
            j,
            r,
            s,
        ) = cand
        sel_map = dict(getattr(base, "selection_mode_by_round", {}))
        sel_map[3] = m3
        sel_map[14] = m14
        spec = replace(
            base,
            selection_mode_by_round=sel_map,
            extra_vecs=ev,
            valu_select=vs,
            valu_select_leaf_pairs=leaf,
            valu_select_precompute_diffs=pre,
            use_temp_deps=td,
            use_temp_deps_extras=tdx,
            emit_order=emit,
            vector_block=vb,
            sched_policy=pol,
            sched_jitter=j,
            sched_restarts=r,
            sched_seed=s,
        )
        tested += 1
        try:
            cyc = bundle_cycles(spec)
        except Exception:
            continue

        if cyc <= best_cycles + 2:
            rows.append(
                {
                    "cycles": cyc,
                    "m3": m3,
                    "m14": m14,
                    "extra_vecs": ev,
                    "valu_select": vs,
                    "leaf_pairs": leaf,
                    "precompute": pre,
                    "use_temp_deps": td,
                    "use_temp_deps_extras": tdx,
                    "emit_order": emit,
                    "vector_block": vb,
                    "sched_policy": pol,
                    "sched_jitter": j,
                    "sched_restarts": r,
                    "sched_seed": s,
                }
            )
        if cyc < best_cycles:
            best_cycles = cyc
            best_spec = spec
            print(
                f"NEW tested={tested} cycles={cyc} "
                f"m3={m3} m14={m14} ev={ev} vs={vs} leaf={leaf} "
                f"pre={pre} td={td}/{tdx} emit={emit} vb={vb} "
                f"pol={pol} j={j} r={r} s={s}",
                flush=True,
            )
        if tested % args.report_every == 0:
            print(f"[{tested}] best={best_cycles}", flush=True)

    out = {
        "base_cycles": base_cycles,
        "tested": tested,
        "best_cycles": best_cycles,
        "top_rows": sorted(rows, key=lambda x: x["cycles"])[:200],
        "spec": asdict(best_spec),
    }
    out_path = Path(args.out)
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(json.dumps(out, indent=2), encoding="utf-8")
    print(f"done tested={tested} best={best_cycles} out={out_path}", flush=True)


if __name__ == "__main__":
    main()
