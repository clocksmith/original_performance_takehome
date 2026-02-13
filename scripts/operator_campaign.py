#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import os
import random
import sys
from dataclasses import asdict, dataclass, replace
from itertools import product
from pathlib import Path
from statistics import mean, median, pstdev
from typing import Any, Callable

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
if ROOT not in sys.path:
    sys.path.insert(0, ROOT)

from generator.build_kernel_base import build_base_instrs
from generator.offload import apply_offload_stream
from generator.op_list import build_ops
from generator.scratch_layout import ScratchAlloc, build_layout
from generator.spec_base import SPEC_BASE, SpecBase
from tests.frozen_problem import (
    DebugInfo,
    Input,
    Machine,
    N_CORES,
    Tree,
    build_mem_image,
    reference_kernel2,
)


def parse_int_list(s: str) -> list[int]:
    out: list[int] = []
    for token in s.split(","):
        token = token.strip()
        if not token:
            continue
        out.append(int(token))
    return out


def parse_str_list(s: str) -> list[str]:
    return [x.strip() for x in s.split(",") if x.strip()]


def sanitize_name(name: str) -> str:
    out = []
    for ch in name:
        if ch.isalnum() or ch in {"_", "-", "."}:
            out.append(ch)
        else:
            out.append("_")
    return "".join(out)


def bundle_cycles(spec: SpecBase) -> int:
    instrs = build_base_instrs(spec=spec)
    return sum(1 for b in instrs if any(k != "debug" and b.get(k) for k in b))


def load_seed_spec(path: str) -> SpecBase:
    with open(path, "r", encoding="utf-8") as f:
        payload = json.load(f)
    spec_dict = payload.get("spec", payload)
    if not isinstance(spec_dict, dict):
        raise ValueError(f"invalid seed-spec payload: {path}")

    merged = dict(SPEC_BASE.__dict__)
    for k, v in spec_dict.items():
        if k not in merged:
            continue
        if k in {"base_cached_rounds", "depth4_cached_rounds"} and isinstance(v, list):
            merged[k] = tuple(v)
            continue
        if k == "valu_select_rounds" and isinstance(v, list):
            merged[k] = tuple(v)
            continue
        if k in {"selection_mode_by_round", "cached_round_depth", "cached_round_x", "cached_round_aliases"} and isinstance(v, dict):
            fixed: dict[int, Any] = {}
            for rk, rv in v.items():
                try:
                    ik = int(rk)
                except (TypeError, ValueError):
                    continue
                if k in {"cached_round_depth", "cached_round_x", "cached_round_aliases"}:
                    try:
                        fixed[ik] = int(rv)
                    except (TypeError, ValueError):
                        continue
                else:
                    fixed[ik] = rv
            merged[k] = fixed
            continue
        if k == "offload_budget_swaps" and isinstance(v, dict):
            swaps: dict[str, tuple[tuple[int, int], ...]] = {}
            for cat, pairs in v.items():
                if not isinstance(pairs, (list, tuple)):
                    continue
                fixed_pairs: list[tuple[int, int]] = []
                for p in pairs:
                    if not isinstance(p, (list, tuple)) or len(p) != 2:
                        continue
                    try:
                        a = int(p[0])
                        b = int(p[1])
                    except (TypeError, ValueError):
                        continue
                    fixed_pairs.append((a, b))
                swaps[cat] = tuple(fixed_pairs)
            merged[k] = swaps
            continue
        merged[k] = v
    return SpecBase(**merged)


def check_equivalence(spec: SpecBase, seeds: list[int]) -> tuple[bool, str]:
    try:
        instrs = build_base_instrs(spec=spec)
    except Exception as exc:
        return False, f"build failed: {exc}"

    for seed in seeds:
        random.seed(seed)
        forest = Tree.generate(10)
        inp = Input.generate(forest, 256, 16)
        mem0 = build_mem_image(forest, inp)
        mem_machine = list(mem0)
        mem_ref = list(mem0)

        machine = Machine(
            mem_machine,
            instrs,
            DebugInfo(scratch_map={}),
            n_cores=N_CORES,
        )
        machine.enable_pause = False
        machine.enable_debug = False

        try:
            machine.run()
        except Exception as exc:
            return False, f"machine run failed (seed={seed}): {exc}"

        ref_mem = None
        try:
            for ref_mem in reference_kernel2(mem_ref):
                pass
        except Exception as exc:
            return False, f"reference failed (seed={seed}): {exc}"
        if ref_mem is None:
            return False, f"reference produced no terminal memory (seed={seed})"

        out_ptr = ref_mem[6]
        out_machine = machine.mem[out_ptr : out_ptr + 256]
        out_ref = ref_mem[out_ptr : out_ptr + 256]
        if out_machine != out_ref:
            return False, f"output mismatch (seed={seed})"
    return True, "ok"


def engine_mix(spec: SpecBase) -> dict[str, int]:
    scratch = ScratchAlloc()
    layout = build_layout(spec, scratch)

    ordered_ops = []
    spec_for_ops = spec
    if getattr(spec, "setup_style", "inline") in {"packed", "none"} and getattr(spec, "include_setup", True):
        spec_for_ops = replace(spec, include_setup=False)
    build_ops(spec_for_ops, layout, ordered_ops=ordered_ops)
    final_ops = apply_offload_stream(spec, ordered_ops)

    counts = {"alu": 0, "valu": 0, "flow": 0, "load": 0, "store": 0}
    for op in final_ops:
        eng = getattr(op, "engine", "")
        if eng == "alu_vec":
            counts["alu"] += 1
        elif eng in counts:
            counts[eng] += 1
    return counts


@dataclass
class Stats:
    min_cycles: int
    median_cycles: float
    mean_cycles: float
    stddev_cycles: float
    max_cycles: int
    wins: int
    losses: int
    ties: int
    total: int


def robust_stats(
    spec: SpecBase,
    baseline_map: dict[tuple[str, int], int],
    sched_policies: list[str],
    sched_seeds: list[int],
    sched_jitter: float,
    sched_restarts: int,
) -> tuple[Stats, dict[tuple[str, int], int]]:
    cycles_map: dict[tuple[str, int], int] = {}
    vals: list[int] = []
    wins = losses = ties = 0
    for policy in sched_policies:
        for seed in sched_seeds:
            k = (policy, seed)
            s = replace(
                spec,
                sched_policy=policy,
                sched_seed=seed,
                sched_jitter=sched_jitter,
                sched_restarts=sched_restarts,
            )
            c = bundle_cycles(s)
            cycles_map[k] = c
            vals.append(c)
            base = baseline_map[k]
            if c < base:
                wins += 1
            elif c > base:
                losses += 1
            else:
                ties += 1
    stats = Stats(
        min_cycles=min(vals),
        median_cycles=float(median(vals)),
        mean_cycles=float(mean(vals)),
        stddev_cycles=float(pstdev(vals)),
        max_cycles=max(vals),
        wins=wins,
        losses=losses,
        ties=ties,
        total=len(vals),
    )
    return stats, cycles_map


def op_dep_split_round(spec: SpecBase) -> SpecBase:
    return replace(
        spec,
        use_temp_deps=True,
        use_temp_deps_extras=False,
        temp_rename_mode="round",
    )


def op_dep_split_window4(spec: SpecBase) -> SpecBase:
    return replace(
        spec,
        use_temp_deps=True,
        use_temp_deps_extras=False,
        temp_rename_mode="window",
        temp_rename_window=4,
    )


def op_round_template_block(spec: SpecBase) -> SpecBase:
    return replace(spec, emit_order="block", vector_block=4, extra_vecs=max(3, spec.extra_vecs))


def op_round_template_round_major(spec: SpecBase) -> SpecBase:
    return replace(spec, emit_order="round_major", vector_block=0)


def op_select_load_fusion_leaf(spec: SpecBase) -> SpecBase:
    return replace(
        spec,
        valu_select=True,
        valu_select_leaf_pairs=True,
        valu_select_precompute_diffs=True,
        valu_select_rounds=(4, 5, 6, 7, 8, 9, 10),
    )


def op_select_load_fusion_sparse(spec: SpecBase) -> SpecBase:
    return replace(
        spec,
        valu_select=True,
        valu_select_leaf_pairs=False,
        valu_select_precompute_diffs=False,
        valu_select_rounds=(4, 15),
    )


def op_hash_tmp_style(spec: SpecBase) -> SpecBase:
    return replace(spec, hash_variant="ir", hash_bitwise_style="tmp_op1", hash_xor_style="swap")


def op_hash_prog_tmp(spec: SpecBase) -> SpecBase:
    return replace(spec, hash_variant="prog", hash_prog_variant="tmp_op1")


def op_cache_alias_mid(spec: SpecBase) -> SpecBase:
    alias = dict(spec.cached_round_aliases)
    alias.update({4: 0, 5: 1, 6: 2, 7: 3, 8: 0, 9: 1, 10: 2})
    return replace(spec, cached_round_aliases=alias)


OP_LIBRARY: dict[str, Callable[[SpecBase], SpecBase]] = {
    "dep_split_round": op_dep_split_round,
    "dep_split_window4": op_dep_split_window4,
    "round_template_block": op_round_template_block,
    "round_template_round_major": op_round_template_round_major,
    "select_load_fusion_leaf": op_select_load_fusion_leaf,
    "select_load_fusion_sparse": op_select_load_fusion_sparse,
    "hash_tmp_style": op_hash_tmp_style,
    "hash_prog_tmp": op_hash_prog_tmp,
    "cache_alias_mid": op_cache_alias_mid,
}


def legacy_variants(spec: SpecBase) -> list[tuple[str, SpecBase]]:
    out: list[tuple[str, SpecBase]] = []
    for delta in (-32, 32):
        out.append(
            (
                f"legacy_budget_parity_{delta:+d}",
                replace(spec, offload_budget_parity=max(0, spec.offload_budget_parity + delta)),
            )
        )
        out.append(
            (
                f"legacy_budget_node_xor_{delta:+d}",
                replace(spec, offload_budget_node_xor=max(0, spec.offload_budget_node_xor + delta)),
            )
        )
    out.append(("legacy_hash_shift_off", replace(spec, offload_hash_shift=False)))
    out.append(("legacy_hash_op2_off", replace(spec, offload_hash_op2=False)))
    out.append(("legacy_ptr_setup_alu", replace(spec, ptr_setup_engine="alu")))
    out.append(("legacy_node_ptr_inc", replace(spec, node_ptr_incremental=True)))
    return out


def promote(baseline: Stats, candidate: Stats, equiv_ok: bool) -> tuple[bool, str]:
    if not equiv_ok:
        return False, "equivalence_failed"
    if candidate.median_cycles >= baseline.median_cycles:
        return False, "median_not_better"
    if candidate.losses > candidate.wins:
        return False, "win_rate_not_better"
    if candidate.max_cycles > baseline.max_cycles + 1:
        return False, "tail_regression"
    return True, "promote"


def evaluate_candidate(
    *,
    name: str,
    track: str,
    cand: SpecBase,
    out_dir: Path,
    base_mix: dict[str, int],
    baseline_map: dict[tuple[str, int], int],
    baseline_stats: Stats,
    sched_policies: list[str],
    sched_seeds: list[int],
    sched_jitter: float,
    sched_restarts: int,
    equiv_seeds: list[int],
) -> dict[str, Any]:
    row: dict[str, Any] = {"name": name, "track": track}
    eq_ok, eq_msg = check_equivalence(cand, equiv_seeds)
    cand_mix = engine_mix(cand)
    stats, cycles_map = robust_stats(
        cand,
        baseline_map,
        sched_policies,
        sched_seeds,
        sched_jitter,
        sched_restarts,
    )
    ok, decision = promote(baseline_stats, stats, eq_ok)
    failures = []
    for k, c in cycles_map.items():
        b = baseline_map[k]
        if c > b:
            failures.append({"policy": k[0], "seed": k[1], "base": b, "cand": c, "delta": c - b})
    failures = sorted(failures, key=lambda x: x["delta"], reverse=True)[:8]

    safe_name = sanitize_name(name)
    spec_path = out_dir / f"{safe_name}.json"
    spec_path.write_text(json.dumps({"spec": asdict(cand)}, indent=2), encoding="utf-8")
    replay_cmd = (
        f"python3 scripts/materialize_variant.py {spec_path} tmp/scripts/replay_{safe_name}.py "
        f"&& python3 tests/submission_tests.py --kernel-builder tmp/scripts/replay_{safe_name}.py"
    )
    row.update(
        {
            "equiv_ok": eq_ok,
            "equiv_msg": eq_msg,
            "decision": decision,
            "promoted": ok,
            "stats": asdict(stats),
            "engine_mix_delta": {k: cand_mix[k] - base_mix.get(k, 0) for k in cand_mix},
            "failure_cases": failures,
            "spec_json": str(spec_path),
            "replay_cmd": replay_cmd,
        }
    )
    return row


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--seed-spec", type=str, default="tmp/json/seed_1288_current.json")
    ap.add_argument("--equiv-seeds", type=str, default="101,202")
    ap.add_argument("--sched-seeds", type=str, default="0,9,17,33,65")
    ap.add_argument("--sched-policies", type=str, default="baseline,valu_first,bottleneck_valu")
    ap.add_argument("--sched-jitter", type=float, default=0.1)
    ap.add_argument("--sched-restarts", type=int, default=2)
    ap.add_argument("--enable-pairs", action="store_true")
    ap.add_argument("--pair-allow-self", action="store_true")
    ap.add_argument("--pair-max", type=int, default=0, help="0 means no limit")
    ap.add_argument("--out", type=str, default="tmp/json/operator_campaign_report.json")
    args = ap.parse_args()

    equiv_seeds = parse_int_list(args.equiv_seeds)
    sched_seeds = parse_int_list(args.sched_seeds)
    sched_policies = parse_str_list(args.sched_policies)
    if not sched_seeds or not sched_policies:
        raise SystemExit("sched-seeds and sched-policies must be non-empty")

    base = load_seed_spec(args.seed_spec)
    base_equiv_ok, base_equiv_msg = check_equivalence(base, equiv_seeds)
    base_mix = engine_mix(base)

    baseline_map: dict[tuple[str, int], int] = {}
    for policy in sched_policies:
        for seed in sched_seeds:
            s = replace(
                base,
                sched_policy=policy,
                sched_seed=seed,
                sched_jitter=args.sched_jitter,
                sched_restarts=args.sched_restarts,
            )
            baseline_map[(policy, seed)] = bundle_cycles(s)
    baseline_stats, _ = robust_stats(
        base,
        baseline_map,
        sched_policies,
        sched_seeds,
        args.sched_jitter,
        args.sched_restarts,
    )

    out_dir = Path("tmp/json/operator_specs")
    out_dir.mkdir(parents=True, exist_ok=True)
    results: list[dict[str, Any]] = []

    for name, op in OP_LIBRARY.items():
        try:
            cand = op(base)
            row = evaluate_candidate(
                name=name,
                track="transform",
                cand=cand,
                out_dir=out_dir,
                base_mix=base_mix,
                baseline_map=baseline_map,
                baseline_stats=baseline_stats,
                sched_policies=sched_policies,
                sched_seeds=sched_seeds,
                sched_jitter=args.sched_jitter,
                sched_restarts=args.sched_restarts,
                equiv_seeds=equiv_seeds,
            )
        except Exception as exc:
            row = {"name": name, "track": "transform", "equiv_ok": False, "equiv_msg": f"operator failed: {exc}", "promoted": False}
        results.append(row)

    pair_count = 0
    if args.enable_pairs:
        ops_items = list(OP_LIBRARY.items())
        for (name_a, op_a), (name_b, op_b) in product(ops_items, ops_items):
            if not args.pair_allow_self and name_a == name_b:
                continue
            if args.pair_max > 0 and pair_count >= args.pair_max:
                break
            name = f"{name_a}__then__{name_b}"
            try:
                cand = op_b(op_a(base))
                row = evaluate_candidate(
                    name=name,
                    track="transform_pair",
                    cand=cand,
                    out_dir=out_dir,
                    base_mix=base_mix,
                    baseline_map=baseline_map,
                    baseline_stats=baseline_stats,
                    sched_policies=sched_policies,
                    sched_seeds=sched_seeds,
                    sched_jitter=args.sched_jitter,
                    sched_restarts=args.sched_restarts,
                    equiv_seeds=equiv_seeds,
                )
            except Exception as exc:
                row = {"name": name, "track": "transform_pair", "equiv_ok": False, "equiv_msg": f"pair failed: {exc}", "promoted": False}
            results.append(row)
            pair_count += 1

    for name, cand in legacy_variants(base):
        try:
            row = evaluate_candidate(
                name=name,
                track="legacy",
                cand=cand,
                out_dir=out_dir,
                base_mix=base_mix,
                baseline_map=baseline_map,
                baseline_stats=baseline_stats,
                sched_policies=sched_policies,
                sched_seeds=sched_seeds,
                sched_jitter=args.sched_jitter,
                sched_restarts=args.sched_restarts,
                equiv_seeds=equiv_seeds,
            )
        except Exception as exc:
            row = {"name": name, "track": "legacy", "equiv_ok": False, "equiv_msg": f"legacy failed: {exc}", "promoted": False}
        results.append(row)

    promoted = [r for r in results if r.get("promoted")]
    promoted_sorted = sorted(promoted, key=lambda r: r["stats"]["median_cycles"])

    report = {
        "baseline": {
            "equiv_ok": base_equiv_ok,
            "equiv_msg": base_equiv_msg,
            "stats": asdict(baseline_stats),
            "engine_mix": base_mix,
            "seed_spec": args.seed_spec,
        },
        "campaign_policy": {
            "dual_track": ["transform", "legacy"],
            "pair_search": {
                "enabled": bool(args.enable_pairs),
                "pair_allow_self": bool(args.pair_allow_self),
                "pair_evaluated": pair_count,
                "pair_max": args.pair_max,
            },
            "promotion_criteria": [
                "equivalence pass",
                "median cycles < baseline median",
                "wins >= losses across fixed replay grid",
                "max cycles <= baseline max + 1",
            ],
            "rollback_trigger": "if two consecutive batches have zero promoted candidates, roll back to baseline-only replay and expand mechanism set before next run",
        },
        "results": results,
        "promoted_count": len(promoted_sorted),
        "top_promoted": promoted_sorted[:5],
    }

    out_path = Path(args.out)
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(json.dumps(report, indent=2), encoding="utf-8")

    print(f"baseline_median={baseline_stats.median_cycles} baseline_max={baseline_stats.max_cycles}")
    print(f"promoted={len(promoted_sorted)}")
    for row in promoted_sorted[:5]:
        print(
            f"PROMOTE {row['name']} track={row['track']} median={row['stats']['median_cycles']} "
            f"wins={row['stats']['wins']} losses={row['stats']['losses']}"
        )
    print(f"report={out_path}")


if __name__ == "__main__":
    main()
