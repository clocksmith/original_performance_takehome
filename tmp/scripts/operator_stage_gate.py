from __future__ import annotations

import argparse
import importlib
import json
import os
import random
import statistics
import sys
from collections import Counter, defaultdict
from dataclasses import asdict, replace
from pathlib import Path
from typing import Any

_REPO_ROOT = os.path.dirname(os.path.dirname(os.path.dirname(__file__)))
if _REPO_ROOT not in sys.path:
    sys.path.insert(0, _REPO_ROOT)

from generator.build_kernel_base import _apply_sched_dep_variant, build_base_instrs
from generator.offload import apply_offload_stream
from generator.op_list import build_ops
from generator.scratch_layout import ScratchAlloc, build_layout
from generator.schedule_dep import schedule_ops_dep
from problem import (
    DebugInfo,
    Input,
    Machine,
    N_CORES,
    SLOT_LIMITS,
    Tree,
    build_mem_image,
    reference_kernel2,
)
from scripts.energy_search import _fast_bundle_precheck, _spec_from_dict


def parse_int_list(s: str) -> list[int]:
    return [int(x) for x in s.split(",") if x.strip()]


def parse_str_list(s: str) -> list[str]:
    return [x.strip() for x in s.split(",") if x.strip()]


def load_spec(ref: str):
    if ref.endswith(".json"):
        payload = json.loads(Path(ref).read_text(encoding="utf-8"))
        spec_dict = payload.get("spec", payload)
        return _spec_from_dict(spec_dict)
    if ":" in ref:
        mod, attr = ref.split(":", 1)
        m = importlib.import_module(mod)
        return getattr(m, attr)
    m = importlib.import_module(ref)
    for attr in ("SPEC", "SPEC_UB_ENERGY_BUNDLE_1291", "SPEC_BASE"):
        if hasattr(m, attr):
            return getattr(m, attr)
    raise SystemExit(f"cannot load spec from {ref!r}")


def build_final_ops(spec):
    scratch = ScratchAlloc()
    layout = build_layout(spec, scratch)
    ordered_ops = []
    build_ops(spec, layout, ordered_ops=ordered_ops)
    return apply_offload_stream(spec, ordered_ops)


def op_cost(op) -> int:
    if op.engine == "alu" and op.slot and op.slot[0] == "alu_vec":
        return 8
    return 1


def engine_mix(spec) -> dict[str, int]:
    counts = Counter()
    for op in build_final_ops(spec):
        if op.engine == "debug":
            continue
        counts[op.engine] += op_cost(op)
    return {k: int(v) for k, v in counts.items()}


def schedule_metrics(spec, *, policy: str, seed: int, jitter: float, restarts: int) -> dict[str, Any]:
    policy_eff = _apply_sched_dep_variant(
        str(policy),
        str(getattr(spec, "sched_deps_variant", "full")),
    )
    instrs = schedule_ops_dep(
        build_final_ops(spec),
        return_ops=False,
        seed=seed,
        jitter=jitter,
        restarts=restarts,
        compact=bool(getattr(spec, "sched_compact", False)),
        repair_passes=int(getattr(spec, "sched_repair_passes", 0)),
        repair_try_swap=bool(getattr(spec, "sched_repair_try_swap", False)),
        policy=policy_eff,
        target_cycles=getattr(spec, "sched_target_cycles", None),
    )
    cycles = 0
    hist = Counter()
    peak_sat = 0.0
    for b in instrs:
        active_engs = [e for e, slots in b.items() if e != "debug" and slots]
        if not active_engs:
            continue
        cycles += 1
        hist[len(active_engs)] += 1
        for e in active_engs:
            sat = len(b[e]) / float(SLOT_LIMITS[e])
            if sat > peak_sat:
                peak_sat = sat

    pre = _fast_bundle_precheck(build_final_ops(spec), caps=None)
    return {
        "policy_effective": policy_eff,
        "cycles": int(cycles),
        "bundle_hist": {str(k): int(v) for k, v in sorted(hist.items())},
        "peak_engine_saturation": float(peak_sat),
        "critical_path_proxy": int(pre["critical_path"]),
    }


def equivalence_oracle(spec, seeds: list[int]) -> dict[str, Any]:
    """
    Mechanized semantic check vs reference_kernel2 on deterministic seeds.
    """
    instrs = build_base_instrs(spec=spec)
    failures = []
    for seed in seeds:
        random.seed(seed)
        forest = Tree.generate(10)
        inp = Input.generate(forest, 256, 16)
        mem = build_mem_image(forest, inp)
        machine = Machine(mem, instrs, DebugInfo(scratch_map={}), n_cores=N_CORES)
        machine.enable_pause = False
        machine.enable_debug = False
        machine.run()
        ref_mem = None
        for r in reference_kernel2(mem):
            ref_mem = r
        assert ref_mem is not None
        inp_values_p = ref_mem[6]
        got = machine.mem[inp_values_p : inp_values_p + len(inp.values)]
        want = ref_mem[inp_values_p : inp_values_p + len(inp.values)]
        if got != want:
            failures.append(seed)
    return {"pass": len(failures) == 0, "failed_seeds": failures}


def aggregate(run_rows: list[dict[str, Any]]) -> dict[str, Any]:
    cycles = [r["cycles"] for r in run_rows]
    peaks = [r["peak_engine_saturation"] for r in run_rows]
    cps = [r["critical_path_proxy"] for r in run_rows]
    return {
        "mean_cycles": float(statistics.fmean(cycles)),
        "min_cycles": int(min(cycles)),
        "max_cycles": int(max(cycles)),
        "schedule_variance": float(statistics.pvariance(cycles) if len(cycles) > 1 else 0.0),
        "mean_peak_saturation": float(statistics.fmean(peaks)),
        "max_peak_saturation": float(max(peaks)),
        "mean_critical_path_proxy": float(statistics.fmean(cps)),
    }


def compare_metrics(base: dict[str, Any], cand: dict[str, Any]) -> dict[str, Any]:
    # Lower is better for all three.
    improve_cycles = cand["mean_cycles"] < base["mean_cycles"]
    improve_peak = cand["mean_peak_saturation"] < base["mean_peak_saturation"]
    improve_var = cand["schedule_variance"] < base["schedule_variance"]
    score = int(improve_cycles) + int(improve_peak) + int(improve_var)
    return {
        "improve_cycles": improve_cycles,
        "improve_peak_saturation": improve_peak,
        "improve_schedule_variance": improve_var,
        "improved_metric_count": score,
        "accept": score >= 2,
    }


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--base-spec", type=str, required=True)
    ap.add_argument("--cand-spec", type=str, required=True)
    ap.add_argument("--fixed-seeds", type=str, default="0,1,2,3,4")
    ap.add_argument("--adversarial-seed", type=int, default=127)
    ap.add_argument("--equiv-seeds", type=str, default="11,29,53")
    ap.add_argument("--policies", type=str, default="baseline,valu_first,bottleneck_valu")
    ap.add_argument("--jitter", type=float, default=0.1)
    ap.add_argument("--restarts", type=int, default=2)
    ap.add_argument("--ab", action="store_true", help="print run-by-run A/B rows")
    ap.add_argument("--out", type=str, default="tmp/json/operator_stage_gate.json")
    args = ap.parse_args()

    base = load_spec(args.base_spec)
    cand = load_spec(args.cand_spec)

    fixed = parse_int_list(args.fixed_seeds)
    seeds = fixed + [int(args.adversarial_seed)]
    policies = parse_str_list(args.policies)
    eq_seeds = parse_int_list(args.equiv_seeds)

    base_mix = engine_mix(base)
    cand_mix = engine_mix(cand)
    mix_delta = {k: int(cand_mix.get(k, 0) - base_mix.get(k, 0)) for k in set(base_mix) | set(cand_mix)}

    base_eq = equivalence_oracle(base, eq_seeds)
    cand_eq = equivalence_oracle(cand, eq_seeds)

    base_rows = []
    cand_rows = []
    for p in policies:
        for s in seeds:
            base_rows.append(
                {
                    "policy": p,
                    "seed": s,
                    **schedule_metrics(base, policy=p, seed=s, jitter=args.jitter, restarts=args.restarts),
                }
            )
            cand_rows.append(
                {
                    "policy": p,
                    "seed": s,
                    **schedule_metrics(cand, policy=p, seed=s, jitter=args.jitter, restarts=args.restarts),
                }
            )

    base_agg = aggregate(base_rows)
    cand_agg = aggregate(cand_rows)
    gate = compare_metrics(base_agg, cand_agg)

    out = {
        "config": {
            "fixed_seeds": fixed,
            "adversarial_seed": int(args.adversarial_seed),
            "all_seeds": seeds,
            "policies": policies,
            "jitter": args.jitter,
            "restarts": args.restarts,
        },
        "equivalence_oracle": {"base": base_eq, "candidate": cand_eq},
        "engine_mix": {"base": base_mix, "candidate": cand_mix, "delta_candidate_minus_base": mix_delta},
        "aggregates": {"base": base_agg, "candidate": cand_agg},
        "stage_gate": gate,
        "runs": {"base": base_rows, "candidate": cand_rows},
        "candidate_spec": asdict(cand),
    }

    out_path = Path(args.out)
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(json.dumps(out, indent=2), encoding="utf-8")

    print("stage_gate:")
    print(json.dumps(gate, sort_keys=True))
    print("aggregate_base:", json.dumps(base_agg, sort_keys=True))
    print("aggregate_candidate:", json.dumps(cand_agg, sort_keys=True))
    if args.ab:
        print("ab_rows:")
        for b, c in zip(base_rows, cand_rows):
            print(
                f"  policy={b['policy']} seed={b['seed']} "
                f"base_cycles={b['cycles']} cand_cycles={c['cycles']} "
                f"base_peak={b['peak_engine_saturation']:.3f} cand_peak={c['peak_engine_saturation']:.3f}"
            )
    print(f"wrote {out_path}")


if __name__ == "__main__":
    main()
