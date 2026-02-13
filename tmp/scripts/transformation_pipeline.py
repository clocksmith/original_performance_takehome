from __future__ import annotations

import argparse
import json
import random
from dataclasses import asdict, replace
from pathlib import Path
from typing import Any, Callable, Iterable

from generator.build_kernel_base import build_base_instrs
from generator.ub_energy_bundle_1291 import SPEC_UB_ENERGY_BUNDLE_1291
from frozen_problem import (
    Machine,
    N_CORES,
    Tree,
    Input,
    build_mem_image,
    reference_kernel2,
)


INT_KEY_DICT_FIELDS = (
    "selection_mode_by_round",
    "hash_xor_style_by_stage",
    "hash_bitwise_style_by_stage",
    "cached_round_aliases",
    "cached_round_depth",
    "cached_round_x",
)
TUPLE_FIELDS = ("valu_select_rounds", "base_cached_rounds", "depth4_cached_rounds")
STRUCTURE_SEED = 0
STRUCTURE_MUTANTS = 0


def bundle_cycles(spec) -> int:
    instrs = build_base_instrs(spec=spec)
    return sum(1 for b in instrs if any(k != "debug" and b.get(k) for k in b))


def verify_equivalence_once(spec, *, seed: int = 123) -> tuple[bool, int]:
    random.seed(seed)
    forest = Tree.generate(10)
    inp = Input.generate(forest, 256, 16)
    mem = build_mem_image(forest, inp)
    instrs = build_base_instrs(spec=spec)
    machine = Machine(mem, instrs, None, n_cores=N_CORES)
    machine.enable_pause = False
    machine.enable_debug = False
    machine.run()
    for ref_mem in reference_kernel2(mem):
        pass
    inp_values_p = ref_mem[6]
    ok = (
        machine.mem[inp_values_p : inp_values_p + len(inp.values)]
        == ref_mem[inp_values_p : inp_values_p + len(inp.values)]
    )
    return ok, machine.cycle


def spec_to_payload(spec) -> dict[str, Any]:
    payload = asdict(spec)
    for field_name in INT_KEY_DICT_FIELDS:
        items = payload.get(field_name, {})
        payload[field_name] = [[int(k), v] for k, v in sorted(items.items())]
    for field_name in TUPLE_FIELDS:
        value = payload.get(field_name)
        if value is not None:
            payload[field_name] = list(value)
    payload["offload_budget_swaps"] = {
        str(cat): [[int(a), int(b)] for a, b in pairs]
        for cat, pairs in sorted(payload.get("offload_budget_swaps", {}).items())
    }
    return payload


def payload_to_spec(payload: dict[str, Any]):
    kwargs = dict(payload)
    for field_name in INT_KEY_DICT_FIELDS:
        pairs = kwargs.get(field_name, [])
        kwargs[field_name] = {int(k): v for k, v in pairs}
    for field_name in TUPLE_FIELDS:
        value = kwargs.get(field_name)
        kwargs[field_name] = None if value is None else tuple(int(x) for x in value)
    kwargs["offload_budget_swaps"] = {
        str(cat): tuple((int(a), int(b)) for a, b in pairs)
        for cat, pairs in kwargs.get("offload_budget_swaps", {}).items()
    }
    return replace(SPEC_UB_ENERGY_BUNDLE_1291, **kwargs)


def spec_key(spec) -> str:
    return json.dumps(spec_to_payload(spec), sort_keys=True, separators=(",", ":"))


def op_dependency_splitting(spec) -> list[tuple[str, object]]:
    out: list[tuple[str, object]] = []
    variants = (
        ("tmpop1_vec8", "tmp_op1", "vec", 8, True, "direct", "none"),
        ("tmpop1_window16", "tmp_op1", "window", 16, True, "direct", "none"),
        ("tmpop1_nodepsx", "tmp_op1", "window", 12, False, "direct", "none"),
        ("prog_pingpong_vec8", "inplace", "vec", 8, True, "prog", "pingpong"),
        ("prog_pingpong_window16", "inplace", "window", 16, True, "prog", "pingpong"),
        ("inplace_window16", "inplace", "window", 16, False, "direct", "none"),
    )
    for label, bitwise, rename_mode, window, deps_extra, hv, hv_prog in variants:
        out.append(
            (
                label,
                replace(
                    spec,
                    hash_bitwise_style=bitwise,
                    temp_rename_mode=rename_mode,
                    temp_rename_window=window,
                    use_temp_deps_extras=deps_extra,
                    sched_repair_passes=max(spec.sched_repair_passes, 2),
                    hash_variant=hv,
                    hash_prog=None if hv == "prog" else spec.hash_prog,
                    hash_prog_variant=hv_prog,
                ),
            )
        )
    if STRUCTURE_MUTANTS > 0:
        rng = random.Random(STRUCTURE_SEED + 101)
        for i in range(STRUCTURE_MUTANTS):
            bitwise = rng.choice(("inplace", "tmp_op1"))
            rename_mode = rng.choice(("off", "vec", "window"))
            window = rng.choice((8, 12, 16, 24))
            deps_extra = rng.choice((True, False))
            hv = rng.choice(("direct", "prog"))
            hv_prog = rng.choice(("none", "pingpong", "tmp_op1"))
            out.append(
                (
                    f"struct_mut_{i}",
                    replace(
                        spec,
                        hash_bitwise_style=bitwise,
                        temp_rename_mode=rename_mode,
                        temp_rename_window=window,
                        use_temp_deps_extras=deps_extra,
                        sched_repair_passes=max(spec.sched_repair_passes, 1),
                        hash_variant=hv,
                        hash_prog=None if hv == "prog" else spec.hash_prog,
                        hash_prog_variant=hv_prog,
                    ),
                )
            )
    return [
        *out
    ]


def op_round_local_templates(spec) -> list[tuple[str, object]]:
    out: list[tuple[str, object]] = []
    round_3_14_eq = {3: "eq", 14: "eq"}
    round_4_10_mask = {4: "mask_precompute", 5: "mask_precompute", 6: "mask_precompute", 7: "mask_precompute", 8: "mask_precompute", 9: "mask_precompute", 10: "mask_precompute"}
    round_4_10_bitmask = {4: "bitmask", 5: "bitmask", 6: "bitmask", 7: "bitmask", 8: "bitmask", 9: "bitmask", 10: "bitmask"}
    variants = (
        ("template_a", "round_major", 4, "bottleneck_valu", "waw0", True, 2, round_3_14_eq | round_4_10_mask),
        ("template_b", "round_major", 8, "baseline", "nowaw", True, 2, round_3_14_eq | round_4_10_mask),
        ("template_c", "block", 8, "global_greedy", "waw0_nowar", True, 3, round_3_14_eq | round_4_10_bitmask),
        ("template_d", "block", 16, "global_greedy", "nowaw", False, 3, round_3_14_eq | round_4_10_mask),
        ("template_e", "auto", 0, "bottleneck_valu", "waw0", True, 2, round_3_14_eq | round_4_10_bitmask),
    )
    for label, emit_order, vec_block, policy, deps_variant, try_swap, repair_passes, per_round_sel in variants:
        out.append(
            (
                label,
                replace(
                    spec,
                    emit_order=emit_order,
                    vector_block=vec_block,
                    sched_policy=policy,
                    sched_deps_variant=deps_variant,
                    sched_repair_passes=repair_passes,
                    sched_repair_try_swap=try_swap,
                    selection_mode_by_round={**spec.selection_mode_by_round, **per_round_sel},
                ),
            )
        )
    if STRUCTURE_MUTANTS > 0:
        rng = random.Random(STRUCTURE_SEED + 202)
        sel_modes = ("eq", "mask_precompute", "bitmask", "bitmask_valu")
        for i in range(STRUCTURE_MUTANTS):
            per_round = {3: "eq", 14: "eq"}
            chosen = rng.choice(sel_modes)
            for r in (4, 5, 6, 7, 8, 9, 10):
                per_round[r] = chosen
            out.append(
                (
                    f"struct_mut_{i}",
                    replace(
                        spec,
                        emit_order=rng.choice(("auto", "round_major", "block")),
                        vector_block=rng.choice((0, 4, 8, 16)),
                        sched_policy=rng.choice(("baseline", "bottleneck_valu", "global_greedy")),
                        sched_deps_variant=rng.choice(("full", "waw0", "nowaw", "waw0_nowar")),
                        sched_repair_passes=rng.choice((1, 2, 3)),
                        sched_repair_try_swap=rng.choice((True, False)),
                        selection_mode_by_round={**spec.selection_mode_by_round, **per_round},
                    ),
                )
            )
    return [
        *out
    ]


def op_select_load_fusion(spec) -> list[tuple[str, object]]:
    out: list[tuple[str, object]] = []
    variants = (
        ("fusion_3_14_leafpairs", (3, 14), True, True),
        ("fusion_3_14_noleaf", (3, 14), False, True),
        ("fusion_4_10_leafpairs", (4, 5, 6, 7, 8, 9, 10), True, False),
        ("fusion_4_10_noleaf", (4, 5, 6, 7, 8, 9, 10), False, False),
        ("fusion_3_14_4_10_leafpairs", (3, 4, 5, 6, 7, 8, 9, 10, 14), True, True),
    )
    for label, rounds, leaf_pairs, precompute in variants:
        out.append(
            (
                label,
                replace(
                    spec,
                    valu_select=True,
                    valu_select_leaf_pairs=leaf_pairs,
                    valu_select_rounds=rounds,
                    valu_select_precompute_diffs=precompute,
                ),
            )
        )
    if STRUCTURE_MUTANTS > 0:
        rng = random.Random(STRUCTURE_SEED + 303)
        all_round_sets = (
            (3, 14),
            (4, 5, 6, 7, 8, 9, 10),
            (3, 4, 5, 6, 7, 8, 9, 10, 14),
            (3, 10, 14),
            (4, 6, 8, 10),
        )
        for i in range(STRUCTURE_MUTANTS):
            out.append(
                (
                    f"struct_mut_{i}",
                    replace(
                        spec,
                        valu_select=True,
                        valu_select_leaf_pairs=rng.choice((True, False)),
                        valu_select_rounds=rng.choice(all_round_sets),
                        valu_select_precompute_diffs=rng.choice((True, False)),
                    ),
                )
            )
    return [
        *out
    ]


OPERATORS: list[tuple[str, Callable[[object], list[tuple[str, object]]]]] = [
    ("dependency_splitting", op_dependency_splitting),
    ("round_local_templates", op_round_local_templates),
    ("select_load_fusion", op_select_load_fusion),
]


def evaluate_candidates(
    base_entries: list[dict[str, Any]],
    name: str,
    operator_fn: Callable[[object], list[tuple[str, object]]],
    *,
    beam_width: int,
    global_best_cycles: int,
    eq_window: int,
) -> tuple[list[dict[str, Any]], object, int, list[dict[str, Any]]]:
    stage_rows: list[dict[str, Any]] = []
    dedup: dict[str, dict[str, Any]] = {}
    best_spec = min(base_entries, key=lambda r: r["cycles"])["spec"]
    best_cycles = global_best_cycles
    base_count = len(base_entries)
    for parent_rank, parent in enumerate(base_entries, start=1):
        parent_spec = parent["spec"]
        parent_label = parent["label"]
        candidates = operator_fn(parent_spec)
        for child_label, spec in candidates:
            key = spec_key(spec)
            if key in dedup:
                continue
            try:
                cyc = bundle_cycles(spec)
            except Exception as exc:
                stage_rows.append(
                    {
                        "operator": name,
                        "parent": parent_label,
                        "parent_rank": parent_rank,
                        "label": child_label,
                        "status": "build_error",
                        "error": str(exc),
                    }
                )
                continue
            if cyc > global_best_cycles + eq_window:
                stage_rows.append(
                    {
                        "operator": name,
                        "parent": parent_label,
                        "parent_rank": parent_rank,
                        "label": child_label,
                        "status": "skip_eq_far",
                        "bundle_cycles": cyc,
                        "eq_window": eq_window,
                    }
                )
                continue
            ok, sim_cyc = verify_equivalence_once(spec, seed=123)
            row = {
                "operator": name,
                "parent": parent_label,
                "parent_rank": parent_rank,
                "label": child_label,
                "status": "checked",
                "bundle_cycles": cyc,
                "sim_cycles": sim_cyc,
                "equivalent": bool(ok),
            }
            stage_rows.append(row)
            if not ok:
                continue
            entry = {
                "spec": spec,
                "cycles": cyc,
                "label": f"{parent_label}>{name}:{child_label}",
            }
            dedup[key] = entry
            if cyc < best_cycles:
                best_spec = spec
                best_cycles = cyc

    if not dedup:
        return base_entries, best_spec, best_cycles, stage_rows
    ranked = sorted(dedup.values(), key=lambda r: (r["cycles"], r["label"]))
    next_beam = ranked[:beam_width]
    stage_rows.append(
        {
            "operator": name,
            "status": "beam",
            "beam_width": beam_width,
            "base_entries": base_count,
            "kept": len(next_beam),
            "best_cycles": next_beam[0]["cycles"],
            "best_label": next_beam[0]["label"],
        }
    )
    return next_beam, best_spec, best_cycles, stage_rows


def run_pipeline(
    base_spec, *, beam_width: int, eq_window: int, rounds: int
) -> tuple[object, int, list[dict[str, Any]]]:
    best_spec = base_spec
    best_cycles = bundle_cycles(base_spec)
    beam = [{"spec": base_spec, "cycles": best_cycles, "label": "base"}]
    rows: list[dict] = []
    print(f"start base={best_cycles} beam={beam_width}", flush=True)
    for round_idx in range(1, rounds + 1):
        for op_name, op_fn in OPERATORS:
            beam, op_best_spec, op_best_cycles, stage_rows = evaluate_candidates(
                beam,
                f"r{round_idx}_{op_name}",
                op_fn,
                beam_width=beam_width,
                global_best_cycles=best_cycles,
                eq_window=eq_window,
            )
            rows.extend(stage_rows)
            if op_best_cycles < best_cycles:
                best_spec = op_best_spec
                best_cycles = op_best_cycles
            print(
                f"round={round_idx} operator={op_name} best={best_cycles} beam_best={beam[0]['cycles']}",
                flush=True,
            )
    return best_spec, best_cycles, rows


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--out", type=str, default="tmp/json/transformation_pipeline_best.json")
    ap.add_argument("--replay-json", type=str, default="")
    ap.add_argument("--beam-width", type=int, default=6)
    ap.add_argument("--eq-window", type=int, default=80)
    ap.add_argument("--rounds", type=int, default=1)
    ap.add_argument("--structure-seed", type=int, default=0)
    ap.add_argument("--structure-mutants", type=int, default=0)
    args = ap.parse_args()
    global STRUCTURE_SEED, STRUCTURE_MUTANTS
    STRUCTURE_SEED = args.structure_seed
    STRUCTURE_MUTANTS = args.structure_mutants

    if args.replay_json:
        payload = json.loads(Path(args.replay_json).read_text())
        spec = payload_to_spec(payload["spec"])
        cyc = bundle_cycles(spec)
        ok, sim_cyc = verify_equivalence_once(spec, seed=123)
        print(json.dumps({"bundle_cycles": cyc, "equivalent": ok, "sim_cycles": sim_cyc}, indent=2))
        return

    best_spec, best_cycles, log_rows = run_pipeline(
        SPEC_UB_ENERGY_BUNDLE_1291,
        beam_width=args.beam_width,
        eq_window=args.eq_window,
        rounds=args.rounds,
    )

    out = {
        "best_cycles": best_cycles,
        "spec": spec_to_payload(best_spec),
        "rows": log_rows,
        "replay_cmd": f"PYTHONPATH=.:tests python3 tmp/scripts/transformation_pipeline.py --replay-json {args.out}",
    }
    out_path = Path(args.out)
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(json.dumps(out, indent=2), encoding="utf-8")
    print(f"done best={best_cycles} out={out_path}", flush=True)
    print(out["replay_cmd"], flush=True)


if __name__ == "__main__":
    main()
