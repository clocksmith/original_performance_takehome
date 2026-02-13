from __future__ import annotations

import argparse
import json
import math
import os
import sys
from dataclasses import asdict, fields, replace
from itertools import product
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parents[2]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from generator.build_kernel_base import build_base_instrs
from generator.spec_base import SPEC_BASE, SpecBase
from generator.ub_energy_bundle_1299 import SPEC_UB_ENERGY_BUNDLE_1299

SWAP_CATS = ("parity", "node_xor", "hash_op2", "hash_shift", "hash_op1")


def bundle_cycles(spec: SpecBase) -> int:
    instrs = build_base_instrs(spec=spec)
    return sum(1 for b in instrs if any(k != "debug" and b.get(k) for k in b))


def budget_by_cat(spec: SpecBase) -> dict[str, int]:
    return {
        "parity": int(getattr(spec, "offload_budget_parity", 0)),
        "node_xor": int(getattr(spec, "offload_budget_node_xor", 0)),
        "hash_op2": int(getattr(spec, "offload_budget_hash_op2", 0)),
        "hash_shift": int(getattr(spec, "offload_budget_hash_shift", 0)),
        "hash_op1": int(getattr(spec, "offload_budget_hash_op1", 0)),
    }


def normalize_swaps(raw: Any) -> dict[str, list[tuple[int, int]]]:
    out: dict[str, list[tuple[int, int]]] = {}
    if not isinstance(raw, dict):
        return out
    for cat in SWAP_CATS:
        pairs = raw.get(cat)
        if not isinstance(pairs, (list, tuple)):
            continue
        keep: list[tuple[int, int]] = []
        seen_src: set[int] = set()
        for p in pairs:
            if not isinstance(p, (list, tuple)) or len(p) != 2:
                continue
            try:
                src = int(p[0])
                dst = int(p[1])
            except (TypeError, ValueError):
                continue
            if src < 0 or dst < 0 or src in seen_src:
                continue
            seen_src.add(src)
            keep.append((src, dst))
        if keep:
            out[cat] = keep
    return out


def freeze_swaps(swaps: dict[str, list[tuple[int, int]]]) -> dict[str, tuple[tuple[int, int], ...]]:
    return {k: tuple(v) for k, v in swaps.items() if v}


def canonicalize_spec_payload(payload: dict[str, Any]) -> dict[str, Any]:
    out = dict(payload)
    tuple_fields = {"base_cached_rounds", "depth4_cached_rounds", "valu_select_rounds"}
    int_key_dict_fields = {
        "selection_mode_by_round",
        "hash_xor_style_by_stage",
        "hash_bitwise_style_by_stage",
        "cached_round_aliases",
        "cached_round_depth",
        "cached_round_x",
    }
    int_value_dict_fields = {"cached_round_aliases", "cached_round_depth", "cached_round_x"}

    for f in tuple_fields:
        if f in out and isinstance(out[f], list):
            out[f] = tuple(out[f])
    for f in int_key_dict_fields:
        val = out.get(f)
        if not isinstance(val, dict):
            continue
        fixed: dict[int, Any] = {}
        for k, v in val.items():
            try:
                ik = int(k)
            except (TypeError, ValueError):
                continue
            if f in int_value_dict_fields:
                try:
                    fixed[ik] = int(v)
                except (TypeError, ValueError):
                    continue
            else:
                fixed[ik] = v
        out[f] = fixed
    out["offload_budget_swaps"] = freeze_swaps(normalize_swaps(out.get("offload_budget_swaps")))
    return out


def load_seed_spec(path: str) -> SpecBase:
    payload = json.loads(Path(path).read_text(encoding="utf-8"))
    spec_dict = payload.get("spec", payload)
    if not isinstance(spec_dict, dict):
        raise ValueError(f"bad seed spec payload: {path}")
    allowed = {f.name for f in fields(SPEC_BASE)}
    merged = {k: v for k, v in SPEC_BASE.__dict__.items()}
    for k, v in canonicalize_spec_payload(spec_dict).items():
        if k in allowed:
            merged[k] = v
    return SpecBase(**merged)


def _pick_stride(total: int, limit: int) -> int:
    if total <= 0 or limit <= 0:
        return 1
    return max(1, math.ceil(total / float(limit)))


def run_swap_geometry(
    seed: SpecBase,
    incumbent_cycles: int,
    max_tests: int,
) -> tuple[SpecBase, int, dict[str, Any]]:
    budgets = budget_by_cat(seed)
    base_swaps = normalize_swaps(getattr(seed, "offload_budget_swaps", {}))
    tested = 0
    improved = 0
    best_spec = seed
    best_cycles = incumbent_cycles
    rejected: list[dict[str, Any]] = []

    # Deterministic local neighborhood over destination and source coordinates.
    deltas = (-128, -64, -32, -16, -8, -4, -2, -1, 1, 2, 4, 8, 16, 32, 64, 128)
    for cat in SWAP_CATS:
        pairs = list(base_swaps.get(cat, []))
        if not pairs:
            continue
        cap = budgets.get(cat, 0)
        if cap <= 0:
            continue

        for i, (src, dst) in enumerate(pairs):
            for d in deltas:
                if tested >= max_tests:
                    break
                cand_swaps = {k: list(v) for k, v in base_swaps.items()}
                cand_pairs = list(cand_swaps.get(cat, []))
                cand_pairs[i] = (src, max(0, dst + d))
                cand_swaps[cat] = cand_pairs
                cand = replace(seed, offload_budget_swaps=freeze_swaps(cand_swaps))
                tested += 1
                try:
                    cyc = bundle_cycles(cand)
                except Exception as exc:
                    rejected.append(
                        {
                            "reason": "build_error",
                            "family": "swap_geometry",
                            "mutated_keys": ["offload_budget_swaps"],
                            "detail": str(exc),
                        }
                    )
                    continue
                if cyc < best_cycles:
                    improved += 1
                    best_cycles = cyc
                    best_spec = cand
                    print(f"[swap_geometry] new_best={best_cycles} tested={tested}", flush=True)
                elif tested % 200 == 0:
                    print(f"[swap_geometry] tested={tested} best={best_cycles}", flush=True)

            used = {s for s, _ in pairs}
            for d in deltas:
                if tested >= max_tests:
                    break
                nsrc = src + d
                if nsrc < 0 or nsrc >= cap:
                    continue
                if nsrc in used and nsrc != src:
                    continue
                cand_swaps = {k: list(v) for k, v in base_swaps.items()}
                cand_pairs = list(cand_swaps.get(cat, []))
                cand_pairs[i] = (nsrc, dst)
                cand_swaps[cat] = cand_pairs
                cand = replace(seed, offload_budget_swaps=freeze_swaps(cand_swaps))
                tested += 1
                try:
                    cyc = bundle_cycles(cand)
                except Exception as exc:
                    rejected.append(
                        {
                            "reason": "build_error",
                            "family": "swap_geometry",
                            "mutated_keys": ["offload_budget_swaps"],
                            "detail": str(exc),
                        }
                    )
                    continue
                if cyc < best_cycles:
                    improved += 1
                    best_cycles = cyc
                    best_spec = cand
                    print(f"[swap_geometry] new_best={best_cycles} tested={tested}", flush=True)
                elif tested % 200 == 0:
                    print(f"[swap_geometry] tested={tested} best={best_cycles}", flush=True)
            if tested >= max_tests:
                break

        # Deterministic dst swaps inside one category, preserving cardinality.
        for i in range(len(pairs)):
            for j in range(i + 1, len(pairs)):
                if tested >= max_tests:
                    break
                cand_swaps = {k: list(v) for k, v in base_swaps.items()}
                cand_pairs = list(cand_swaps.get(cat, []))
                si, di = cand_pairs[i]
                sj, dj = cand_pairs[j]
                cand_pairs[i] = (si, dj)
                cand_pairs[j] = (sj, di)
                cand_swaps[cat] = cand_pairs
                cand = replace(seed, offload_budget_swaps=freeze_swaps(cand_swaps))
                tested += 1
                try:
                    cyc = bundle_cycles(cand)
                except Exception as exc:
                    rejected.append(
                        {
                            "reason": "build_error",
                            "family": "swap_geometry",
                            "mutated_keys": ["offload_budget_swaps"],
                            "detail": str(exc),
                        }
                    )
                    continue
                if cyc < best_cycles:
                    improved += 1
                    best_cycles = cyc
                    best_spec = cand
                    print(f"[swap_geometry] new_best={best_cycles} tested={tested}", flush=True)
                elif tested % 200 == 0:
                    print(f"[swap_geometry] tested={tested} best={best_cycles}", flush=True)
            if tested >= max_tests:
                break
        if tested >= max_tests:
            break

    return best_spec, best_cycles, {
        "family": "swap_geometry",
        "tested": tested,
        "improved_candidates": improved,
        "mutated_keys": ["offload_budget_swaps"],
        "swap_cardinalities": {k: len(v) for k, v in normalize_swaps(asdict(best_spec).get("offload_budget_swaps", {})).items()},
        "rejected_hypotheses": rejected[:64],
    }


def run_scheduler_grid(
    seed: SpecBase,
    incumbent_cycles: int,
    max_tests: int,
) -> tuple[SpecBase, int, dict[str, Any]]:
    policies = [seed.sched_policy, "bottleneck_valu", "global_greedy", "valu_first"]
    deps_variants = [seed.sched_deps_variant, "waw0", "nowaw", "waw0_nowar"]
    rename_cfgs = [
        ("off", seed.temp_rename_window, seed.use_temp_deps_extras),
        ("round", seed.temp_rename_window, seed.use_temp_deps_extras),
        ("vec", seed.temp_rename_window, seed.use_temp_deps_extras),
        ("window", 16, False),
    ]
    sched_seeds = [seed.sched_seed, 0, 1, 5, 9, 17, 33, 65]
    jitters = [seed.sched_jitter, 0.0, 0.05, 0.1, 0.15]
    restarts = [seed.sched_restarts, 1, 2, 4]
    compacts = [seed.sched_compact, not seed.sched_compact]
    repair_passes = [seed.sched_repair_passes, 0, 1, 2]
    repair_swaps = [seed.sched_repair_try_swap, False, True]

    # Preserve order and remove duplicates.
    def _unique(xs: list[Any]) -> list[Any]:
        out = []
        seen = set()
        for x in xs:
            if x in seen:
                continue
            seen.add(x)
            out.append(x)
        return out

    policies = _unique(policies)
    deps_variants = _unique(deps_variants)
    rename_cfgs = _unique(rename_cfgs)
    sched_seeds = _unique(sched_seeds)
    jitters = _unique(jitters)
    restarts = _unique(restarts)
    compacts = _unique(compacts)
    repair_passes = _unique(repair_passes)
    repair_swaps = _unique(repair_swaps)

    total = (
        len(policies)
        * len(deps_variants)
        * len(rename_cfgs)
        * len(sched_seeds)
        * len(jitters)
        * len(restarts)
        * len(compacts)
        * len(repair_passes)
        * len(repair_swaps)
    )
    stride = _pick_stride(total, max_tests)

    tested = 0
    seen = 0
    improved = 0
    best_spec = seed
    best_cycles = incumbent_cycles
    rejected: list[dict[str, Any]] = []

    for (
        policy,
        deps,
        (rename_mode, rename_window, deps_extra),
        sched_seed,
        jitter,
        nrestart,
        compact,
        repair_n,
        repair_swap,
    ) in product(
        policies,
        deps_variants,
        rename_cfgs,
        sched_seeds,
        jitters,
        restarts,
        compacts,
        repair_passes,
        repair_swaps,
    ):
        if seen % stride != 0:
            seen += 1
            continue
        seen += 1
        if tested >= max_tests:
            break
        cand = replace(
            seed,
            sched_policy=policy,
            sched_deps_variant=deps,
            temp_rename_mode=rename_mode,
            temp_rename_window=rename_window,
            use_temp_deps_extras=deps_extra,
            sched_seed=sched_seed,
            sched_jitter=jitter,
            sched_restarts=nrestart,
            sched_compact=compact,
            sched_repair_passes=repair_n,
            sched_repair_try_swap=repair_swap,
        )
        tested += 1
        try:
            cyc = bundle_cycles(cand)
        except Exception as exc:
            rejected.append(
                {
                    "reason": "build_error",
                    "family": "scheduler_grid",
                    "mutated_keys": [
                        "sched_policy",
                        "sched_deps_variant",
                        "temp_rename_mode",
                        "temp_rename_window",
                        "use_temp_deps_extras",
                        "sched_seed",
                        "sched_jitter",
                        "sched_restarts",
                        "sched_compact",
                        "sched_repair_passes",
                        "sched_repair_try_swap",
                    ],
                    "detail": str(exc),
                }
            )
            continue
        if cyc < best_cycles:
            improved += 1
            best_cycles = cyc
            best_spec = cand
            print(f"[scheduler_grid] new_best={best_cycles} tested={tested}", flush=True)
        elif tested % 200 == 0:
            print(f"[scheduler_grid] tested={tested} best={best_cycles}", flush=True)

    return best_spec, best_cycles, {
        "family": "scheduler_grid",
        "tested": tested,
        "improved_candidates": improved,
        "grid_total": total,
        "sample_stride": stride,
        "mutated_keys": [
            "sched_policy",
            "sched_deps_variant",
            "temp_rename_mode",
            "temp_rename_window",
            "use_temp_deps_extras",
            "sched_seed",
            "sched_jitter",
            "sched_restarts",
            "sched_compact",
            "sched_repair_passes",
            "sched_repair_try_swap",
        ],
        "rejected_hypotheses": rejected[:64],
    }


def run_structural_hash_cache(
    seed: SpecBase,
    incumbent_cycles: int,
    max_tests: int,
) -> tuple[SpecBase, int, dict[str, Any]]:
    hash_variants = [seed.hash_variant, "direct", "ir", "prog"]
    hash_prog_variants = ["none", "baseline", "swap_xor", "tmp_xor_const", "tmp_op1", "pingpong"]
    hash_bitwise_styles = [seed.hash_bitwise_style, "inplace", "tmp_op1"]
    hash_xor_styles = [seed.hash_xor_style, "baseline", "swap", "tmp_xor_const"]
    hash_linear_styles = [seed.hash_linear_style, "muladd", "shift_add"]
    bitwise_stage_opts = [
        seed.hash_bitwise_style_by_stage,
        {},
        {1: "tmp_op1"},
        {3: "tmp_op1"},
        {5: "tmp_op1"},
        {1: "tmp_op1", 3: "tmp_op1", 5: "tmp_op1"},
    ]
    xor_stage_opts = [
        seed.hash_xor_style_by_stage,
        {},
        {0: "swap"},
        {2: "swap"},
        {4: "swap"},
        {0: "tmp_xor_const"},
        {2: "tmp_xor_const"},
        {4: "tmp_xor_const"},
        {0: "swap", 2: "swap", 4: "swap"},
    ]
    cache_depth_opts = [{}, {11: 2, 12: 2, 13: 2, 14: 2}]
    cache_x_opts = [{}, {11: 16, 12: 16, 13: 16, 14: 16}, {11: 8, 12: 8, 13: 8, 14: 8}]
    idx_opts = [seed.idx_shifted, True, False]
    node_ptr_opts = [seed.node_ptr_incremental, True, False]

    # Preserve order and remove duplicates where hashability allows.
    def _unique_json(xs: list[Any]) -> list[Any]:
        out: list[Any] = []
        seen: set[str] = set()
        for x in xs:
            key = json.dumps(x, sort_keys=True)
            if key in seen:
                continue
            seen.add(key)
            out.append(x)
        return out

    hash_variants = _unique_json(hash_variants)
    hash_prog_variants = _unique_json(hash_prog_variants)
    hash_bitwise_styles = _unique_json(hash_bitwise_styles)
    hash_xor_styles = _unique_json(hash_xor_styles)
    hash_linear_styles = _unique_json(hash_linear_styles)
    bitwise_stage_opts = _unique_json(bitwise_stage_opts)
    xor_stage_opts = _unique_json(xor_stage_opts)
    cache_depth_opts = _unique_json(cache_depth_opts)
    cache_x_opts = _unique_json(cache_x_opts)
    idx_opts = _unique_json(idx_opts)
    node_ptr_opts = _unique_json(node_ptr_opts)

    total = (
        len(hash_variants)
        * len(hash_prog_variants)
        * len(hash_bitwise_styles)
        * len(hash_xor_styles)
        * len(hash_linear_styles)
        * len(bitwise_stage_opts)
        * len(xor_stage_opts)
        * len(cache_depth_opts)
        * len(cache_x_opts)
        * len(idx_opts)
        * len(node_ptr_opts)
    )
    stride = _pick_stride(total, max_tests)

    tested = 0
    seen = 0
    improved = 0
    best_spec = seed
    best_cycles = incumbent_cycles
    rejected: list[dict[str, Any]] = []

    for (
        hv,
        hpv,
        hbw,
        hxor,
        hlin,
        hbw_by_stage,
        hxor_by_stage,
        cache_depth,
        cache_x,
        idx_shifted,
        node_ptr_inc,
    ) in product(
        hash_variants,
        hash_prog_variants,
        hash_bitwise_styles,
        hash_xor_styles,
        hash_linear_styles,
        bitwise_stage_opts,
        xor_stage_opts,
        cache_depth_opts,
        cache_x_opts,
        idx_opts,
        node_ptr_opts,
    ):
        if seen % stride != 0:
            seen += 1
            continue
        seen += 1
        if tested >= max_tests:
            break
        cand = replace(
            seed,
            hash_variant=hv,
            hash_prog_variant=hpv,
            hash_prog=None,
            hash_bitwise_style=hbw,
            hash_xor_style=hxor,
            hash_linear_style=hlin,
            hash_bitwise_style_by_stage=hbw_by_stage,
            hash_xor_style_by_stage=hxor_by_stage,
            cached_round_depth=cache_depth,
            cached_round_x=cache_x,
            idx_shifted=idx_shifted,
            node_ptr_incremental=node_ptr_inc,
        )
        tested += 1
        try:
            cyc = bundle_cycles(cand)
        except Exception as exc:
            rejected.append(
                {
                    "reason": "build_error",
                    "family": "structural_hash_cache",
                    "mutated_keys": [
                        "hash_variant",
                        "hash_prog_variant",
                        "hash_bitwise_style",
                        "hash_xor_style",
                        "hash_linear_style",
                        "hash_bitwise_style_by_stage",
                        "hash_xor_style_by_stage",
                        "cached_round_depth",
                        "cached_round_x",
                        "idx_shifted",
                        "node_ptr_incremental",
                    ],
                    "detail": str(exc),
                }
            )
            continue
        if cyc < best_cycles:
            improved += 1
            best_cycles = cyc
            best_spec = cand
            print(f"[structural_hash_cache] new_best={best_cycles} tested={tested}", flush=True)
        elif tested % 200 == 0:
            print(f"[structural_hash_cache] tested={tested} best={best_cycles}", flush=True)

    return best_spec, best_cycles, {
        "family": "structural_hash_cache",
        "tested": tested,
        "improved_candidates": improved,
        "grid_total": total,
        "sample_stride": stride,
        "mutated_keys": [
            "hash_variant",
            "hash_prog_variant",
            "hash_bitwise_style",
            "hash_xor_style",
            "hash_linear_style",
            "hash_bitwise_style_by_stage",
            "hash_xor_style_by_stage",
            "cached_round_depth",
            "cached_round_x",
            "idx_shifted",
            "node_ptr_incremental",
        ],
        "rejected_hypotheses": rejected[:64],
    }


def run_out_of_basin(seed: SpecBase, incumbent_cycles: int, max_tests: int) -> tuple[SpecBase, int, dict[str, Any]]:
    # One forced out-of-basin seed, then short scheduler sweep.
    base = replace(
        SPEC_UB_ENERGY_BUNDLE_1299,
        offload_budget_swaps=seed.offload_budget_swaps,
        sched_seed=seed.sched_seed,
        sched_jitter=seed.sched_jitter,
        sched_restarts=seed.sched_restarts,
    )
    tested = 0
    best_spec = base
    best_cycles = incumbent_cycles
    improved = 0
    rejected: list[dict[str, Any]] = []
    for sched_seed in [0, 1, 5, 9, 17, 33, 65]:
        for jitter in [0.0, 0.05, 0.1, 0.15]:
            for restarts in [1, 2, 4]:
                for policy in ["baseline", "bottleneck_valu", "global_greedy"]:
                    if tested >= max_tests:
                        break
                    cand = replace(
                        base,
                        sched_seed=sched_seed,
                        sched_jitter=jitter,
                        sched_restarts=restarts,
                        sched_policy=policy,
                    )
                    tested += 1
                    try:
                        cyc = bundle_cycles(cand)
                    except Exception as exc:
                        rejected.append(
                            {
                                "reason": "build_error",
                                "family": "out_of_basin",
                                "mutated_keys": ["seed_spec", "sched_seed", "sched_jitter", "sched_restarts", "sched_policy"],
                                "detail": str(exc),
                            }
                        )
                        continue
                    if cyc < best_cycles:
                        improved += 1
                        best_cycles = cyc
                        best_spec = cand
                        print(f"[out_of_basin] new_best={best_cycles} tested={tested}", flush=True)
                    elif tested % 100 == 0:
                        print(f"[out_of_basin] tested={tested} best={best_cycles}", flush=True)
                if tested >= max_tests:
                    break
            if tested >= max_tests:
                break
        if tested >= max_tests:
            break

    return best_spec, best_cycles, {
        "family": "out_of_basin",
        "tested": tested,
        "improved_candidates": improved,
        "mutated_keys": ["seed_spec", "sched_seed", "sched_jitter", "sched_restarts", "sched_policy"],
        "rejected_hypotheses": rejected[:64],
    }


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--seed-spec", type=str, default="tmp/json/seed_1288_current.json")
    ap.add_argument("--swap-tests", type=int, default=2200)
    ap.add_argument("--sched-tests", type=int, default=2400)
    ap.add_argument("--struct-tests", type=int, default=2600)
    ap.add_argument("--oob-tests", type=int, default=320)
    ap.add_argument("--out", type=str, default="tmp/json/strategy_first_campaign.json")
    args = ap.parse_args()

    incumbent = load_seed_spec(args.seed_spec)
    incumbent_cycles = bundle_cycles(incumbent)
    best_spec = incumbent
    best_cycles = incumbent_cycles

    report: dict[str, Any] = {
        "seed_spec": args.seed_spec,
        "incumbent_cycles": incumbent_cycles,
        "batches": [],
        "discarded_hypotheses": [],
        "stuck_protocol": {
            "batch_non_improving_limit_per_family": 2,
            "global_non_improving_trigger": 4,
        },
    }
    non_improving_total = 0

    families = [
        ("swap_geometry", run_swap_geometry, args.swap_tests),
        ("scheduler_grid", run_scheduler_grid, args.sched_tests),
        ("structural_hash_cache", run_structural_hash_cache, args.struct_tests),
    ]

    for family_name, fn, max_tests in families:
        print(f"batch_start family={family_name} max_tests={max_tests} current_best={best_cycles}", flush=True)
        cand_spec, cand_cycles, meta = fn(best_spec, best_cycles, max_tests)
        improved = cand_cycles < best_cycles
        batch_row = {
            "family": family_name,
            "max_tests": max_tests,
            "best_cycles_before": best_cycles,
            "best_cycles_after": cand_cycles if improved else best_cycles,
            "improved": improved,
            **meta,
        }
        report["batches"].append(batch_row)
        report["discarded_hypotheses"].extend(meta.get("rejected_hypotheses", []))
        if improved:
            best_spec = cand_spec
            best_cycles = cand_cycles
            non_improving_total = 0
        else:
            non_improving_total += 1
        print(
            f"batch_done family={family_name} tested={meta.get('tested', 0)} "
            f"improved={improved} best={best_cycles}",
            flush=True,
        )

    if non_improving_total >= 3:
        print("batch_start family=out_of_basin process_pivot=1", flush=True)
        # Process pivot: out-of-basin reseed + bounded deterministic scheduler sweep.
        cand_spec, cand_cycles, meta = run_out_of_basin(best_spec, best_cycles, args.oob_tests)
        improved = cand_cycles < best_cycles
        batch_row = {
            "family": "out_of_basin",
            "max_tests": args.oob_tests,
            "best_cycles_before": best_cycles,
            "best_cycles_after": cand_cycles if improved else best_cycles,
            "improved": improved,
            **meta,
            "reason": "process_pivot_after_non_improving_batches",
        }
        report["batches"].append(batch_row)
        report["discarded_hypotheses"].extend(meta.get("rejected_hypotheses", []))
        if improved:
            best_spec = cand_spec
            best_cycles = cand_cycles
        print(
            f"batch_done family=out_of_basin tested={meta.get('tested', 0)} "
            f"improved={improved} best={best_cycles}",
            flush=True,
        )

    report["best_cycles"] = best_cycles
    report["best_spec"] = asdict(best_spec)
    report["best_spec_json"] = args.out
    report["replay_cmd"] = (
        "python3 scripts/materialize_variant.py "
        f"{args.out} tmp/scripts/replay_strategy_first.py "
        "&& python3 tests/submission_tests.py --kernel-builder tmp/scripts/replay_strategy_first.py"
    )

    out_path = Path(args.out)
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(json.dumps(report, indent=2), encoding="utf-8")
    print(f"start={incumbent_cycles} best={best_cycles} out={out_path}", flush=True)


if __name__ == "__main__":
    main()
