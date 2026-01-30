#!/usr/bin/env python3
"""Sweep cache/offload parameters against engine caps.

This tool can operate in two modes:
1) Legacy sweep mode (top-4 + optional depth-4), using CLI flags.
2) Strategy-config mode via --config JSON (covers all proof strategies).
"""
from __future__ import annotations

import argparse
import json
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable, Sequence

ROOT = Path(__file__).resolve().parent.parent
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from problem import HASH_STAGES, VLEN

# Constants
VEC = 32
ROUNDS = 16

HASH_VALU_PER_VEC = 12 * ROUNDS  # 192 (includes 3 shifts per round)
NODE_XOR_PER_VEC = ROUNDS  # 16
PARITY_ROUNDS = ROUNDS - 2  # skip round10 and round15
RESET_VALU_OPS = 1  # round10 reset on VALU (0 if moved to flow)
MAX_OFFLOAD = 3 * ROUNDS * VEC  # one op per bitwise stage per vector-round

# Selection models
VSELECTS_PER_DEPTH = {0: 0, 1: 1, 2: 3, 3: 7, 4: 15, 5: 31}
BITMASK_ALU_PER_DEPTH = {0: 0, 1: 1, 2: 2, 3: 5, 4: 11}  # vector-ALU ops per vec
MASK_VALU_PER_DEPTH = {0: 0, 1: 1, 2: 3, 3: 8, 4: 18, 5: 40}
MASK_PRE_VALU_PER_DEPTH = {0: 0, 1: 1, 2: 3, 3: 5, 4: 9, 5: 13}

DEFAULT_ROUND_DEPTH_MAP = {
    0: 0,
    1: 1,
    2: 2,
    3: 3,
    11: 0,
    12: 1,
    13: 2,
    14: 3,
}


@dataclass
class Result:
    T: int
    x4: int
    x5: int
    flow_ops: int
    load_ops: int
    min_offload: int
    alu_ops: int
    valu_ops: int
    setup_slack: int


@dataclass
class StrategyCounts:
    flow_ops: int
    load_ops: int
    valu_ops: int
    alu_ops: int
    min_offload: int
    setup_slack: int


def _vector_const_count() -> int:
    vec_consts = {1, 2}
    for op1, val1, op2, op3, val3 in HASH_STAGES:
        if op1 == "+" and op2 == "+":
            mult = (1 + (1 << val3)) % (2**32)
            vec_consts.add(mult)
            vec_consts.add(val1)
        else:
            vec_consts.add(val1)
            vec_consts.add(val3)
    return len(vec_consts)


def _scalar_const_count(cfg, *, x4: int, x5: int) -> int:
    const_s = set()
    for v in (0, 1, 2, 4, 5, 6, 8, 10, 12, 14, 31, VLEN):
        const_s.add(v)
    # Cached-node address setup needs constants 0..cached_nodes-1.
    cached_nodes = _cached_nodes(cfg, x4=x4, x5=x5)
    node_const_max = cached_nodes + (1 if cfg.get("idx_shifted", False) else 0)
    const_s.update(range(node_const_max))
    # Bitmask thresholds for depth3 selection.
    if _selection_mode(cfg, group="base") == "bitmask":
        const_s.update({11, 13})
    # Hash constants (also used as vector consts).
    vec_consts = {1, 2}
    for op1, val1, op2, op3, val3 in HASH_STAGES:
        if op1 == "+" and op2 == "+":
            mult = (1 + (1 << val3)) % (2**32)
            vec_consts.add(mult)
            vec_consts.add(val1)
        else:
            vec_consts.add(val1)
            vec_consts.add(val3)
    const_s.update(vec_consts)
    # Equality-selection constants by depth.
    if _selection_mode(cfg, group="base") == "eq":
        const_s.update(range(1, 15))
    if _selection_mode(cfg, group="depth4") == "eq" and cfg.get("depth4_rounds") and x4 > 0:
        const_s.update(range(15, 31))
    if _selection_mode(cfg, group="depth5") == "eq" and cfg.get("depth5_rounds") and x5 > 0:
        const_s.update(range(31, 63))
    # Bitmask depth4 thresholds.
    if _selection_mode(cfg, group="depth4") == "bitmask" and cfg.get("depth4_rounds") and x4 > 0:
        const_s.update({17, 19, 21, 23, 25, 27, 29})
    return len(const_s)


CONST_V_COUNT = _vector_const_count()


def _expand_values(value, *, name: str, default: Sequence[int]) -> list[int]:
    if value is None:
        return list(default)
    if isinstance(value, int):
        return [value]
    if isinstance(value, list):
        return [int(v) for v in value]
    if isinstance(value, dict):
        start = int(value.get("start", 0))
        stop = int(value.get("stop", 0))
        step = int(value.get("step", 1))
        inclusive = bool(value.get("inclusive", True))
        if step <= 0:
            raise ValueError(f"{name} step must be positive")
        if inclusive:
            stop = stop + 1
        return list(range(start, stop, step))
    raise ValueError(f"{name} must be int, list, or range dict")


def _round_depth_map(cfg) -> dict[int, int]:
    custom = cfg.get("round_depth_map")
    if custom is None:
        return dict(DEFAULT_ROUND_DEPTH_MAP)
    return {int(k): int(v) for k, v in custom.items()}


def _vselects_per_depth(cfg) -> dict[int, int]:
    custom = cfg.get("vselects_per_depth")
    if custom is None:
        return dict(VSELECTS_PER_DEPTH)
    return {int(k): int(v) for k, v in custom.items()}


def _bitmask_alu_per_depth(cfg) -> dict[int, int]:
    custom = cfg.get("bitmask_alu_per_depth")
    if custom is None:
        return dict(BITMASK_ALU_PER_DEPTH)
    return {int(k): int(v) for k, v in custom.items()}


def _bitmask_flow_per_depth(cfg) -> dict[int, int]:
    custom = cfg.get("bitmask_flow_per_depth")
    if custom is None:
        # Default to eq-selection counts; override in config if needed.
        return dict(VSELECTS_PER_DEPTH)
    return {int(k): int(v) for k, v in custom.items()}


def _mask_valu_per_depth(cfg) -> dict[int, int]:
    custom = cfg.get("mask_valu_per_depth")
    if custom is None:
        return dict(MASK_VALU_PER_DEPTH)
    return {int(k): int(v) for k, v in custom.items()}


def _mask_pre_valu_per_depth(cfg) -> dict[int, int]:
    custom = cfg.get("mask_pre_valu_per_depth")
    if custom is None:
        return dict(MASK_PRE_VALU_PER_DEPTH)
    return {int(k): int(v) for k, v in custom.items()}


def _is_mask(mode: str) -> bool:
    return mode in {"mask", "mask_precompute"}


def _selection_mode(cfg, *, group: str) -> str:
    return cfg.get(f"selection_mode_{group}", cfg.get("selection_mode", "eq"))


def _cached_nodes(cfg, *, x4: int, x5: int) -> int:
    if cfg.get("cached_nodes") is not None:
        return int(cfg["cached_nodes"])
    # Mirror generator default: 31 nodes if depth4 used, 63 if depth5 used, else 15.
    if cfg.get("depth5_rounds") and x5 > 0:
        return 63
    if cfg.get("depth4_rounds") and x4 > 0:
        return 31
    return 15


def _setup_counts(cfg, *, x4: int, x5: int) -> tuple[int, int, int, int]:
    include_setup = bool(cfg.get("include_setup", True))
    if not include_setup:
        return 0, 0, 0, 0

    # Load setup: const loads + pointer loads
    setup_load = cfg.get("setup_load_ops")
    if setup_load is None:
        setup_load = _scalar_const_count(cfg, x4=x4, x5=x5) + 3

    # Flow setup: pointer add_imm if flow setup engine
    ptr_engine = cfg.get("ptr_setup_engine", "flow")
    setup_flow = cfg.get("flow_setup_ops")
    if setup_flow is None:
        setup_flow = 64 if ptr_engine == "flow" else 0

    # ALU setup: pointer setup if using ALU + optional forest_values_p shift
    setup_alu = cfg.get("setup_alu_ops")
    if setup_alu is None:
        setup_alu = 0
        if ptr_engine == "alu":
            setup_alu += 64
        if cfg.get("idx_shifted", False):
            setup_alu += 1

    # VALU setup: vector const broadcasts + cached node broadcasts + base pointer broadcast
    setup_valu = cfg.get("setup_valu_ops")
    if setup_valu is None:
        cached_nodes = _cached_nodes(cfg, x4=x4, x5=x5)
        setup_valu = CONST_V_COUNT + cached_nodes + 1
        if cfg.get("idx_shifted", False):
            setup_valu += VEC

    return int(setup_flow), int(setup_load), int(setup_valu), int(setup_alu)


def _selection_flow(cfg, *, x4: int, x5: int) -> int:
    depth_map = _round_depth_map(cfg)
    base_rounds = cfg.get("base_cached_rounds", [])
    vselects_per_depth = _vselects_per_depth(cfg)
    bitmask_flow_per_depth = _bitmask_flow_per_depth(cfg)
    base_mode = _selection_mode(cfg, group="base")
    depth4_mode = _selection_mode(cfg, group="depth4")
    depth5_mode = _selection_mode(cfg, group="depth5")
    flow = 0
    for r in base_rounds:
        if r not in depth_map:
            raise ValueError(f"round {r} missing from round_depth_map")
        depth = depth_map[r]
        if base_mode == "bitmask" and depth in bitmask_flow_per_depth:
            flow += bitmask_flow_per_depth[depth] * VEC
        else:
            flow += vselects_per_depth[depth] * VEC
    depth4_rounds = cfg.get("depth4_rounds", [])
    depth5_rounds = cfg.get("depth5_rounds", [])
    if depth4_rounds and x4 > 0:
        if depth4_mode == "bitmask" and 4 in bitmask_flow_per_depth:
            flow += bitmask_flow_per_depth[4] * x4 * len(depth4_rounds)
        else:
            flow += vselects_per_depth[4] * x4 * len(depth4_rounds)
    if depth5_rounds and x5 > 0:
        if depth5_mode == "bitmask" and 5 in bitmask_flow_per_depth:
            flow += bitmask_flow_per_depth[5] * x5 * len(depth5_rounds)
        else:
            flow += vselects_per_depth[5] * x5 * len(depth5_rounds)
    return flow


def _selection_alu(cfg, *, x4: int, x5: int) -> int:
    depth_map = _round_depth_map(cfg)
    base_rounds = cfg.get("base_cached_rounds", [])
    vselects_per_depth = _vselects_per_depth(cfg)
    bitmask_alu_per_depth = _bitmask_alu_per_depth(cfg)
    base_mode = _selection_mode(cfg, group="base")
    depth4_mode = _selection_mode(cfg, group="depth4")
    depth5_mode = _selection_mode(cfg, group="depth5")
    alu_ops = 0
    for r in base_rounds:
        depth = depth_map[r]
        if _is_mask(base_mode):
            continue
        if base_mode == "bitmask" and depth in bitmask_alu_per_depth:
            alu_ops += bitmask_alu_per_depth[depth] * VLEN * VEC
        else:
            alu_ops += vselects_per_depth[depth] * VLEN * VEC
    depth4_rounds = cfg.get("depth4_rounds", [])
    depth5_rounds = cfg.get("depth5_rounds", [])
    if depth4_rounds and x4 > 0:
        if _is_mask(depth4_mode):
            pass
        elif depth4_mode == "bitmask" and 4 in bitmask_alu_per_depth:
            alu_ops += bitmask_alu_per_depth[4] * VLEN * x4 * len(depth4_rounds)
        else:
            alu_ops += vselects_per_depth[4] * VLEN * x4 * len(depth4_rounds)
    if depth5_rounds and x5 > 0:
        if _is_mask(depth5_mode):
            pass
        elif depth5_mode == "bitmask" and 5 in bitmask_alu_per_depth:
            alu_ops += bitmask_alu_per_depth[5] * VLEN * x5 * len(depth5_rounds)
        else:
            alu_ops += vselects_per_depth[5] * VLEN * x5 * len(depth5_rounds)
    return alu_ops


def _selection_valu(cfg, *, x4: int, x5: int) -> int:
    depth_map = _round_depth_map(cfg)
    base_rounds = cfg.get("base_cached_rounds", [])
    mask_valu_per_depth = _mask_valu_per_depth(cfg)
    mask_pre_valu_per_depth = _mask_pre_valu_per_depth(cfg)
    base_mode = _selection_mode(cfg, group="base")
    depth4_mode = _selection_mode(cfg, group="depth4")
    depth5_mode = _selection_mode(cfg, group="depth5")
    valu_ops = 0
    if base_mode in {"mask", "mask_precompute"}:
        for r in base_rounds:
            depth = depth_map[r]
            if base_mode == "mask_precompute":
                valu_ops += mask_pre_valu_per_depth.get(depth, 0) * VEC
            else:
                valu_ops += mask_valu_per_depth.get(depth, 0) * VEC
    depth4_rounds = cfg.get("depth4_rounds", [])
    depth5_rounds = cfg.get("depth5_rounds", [])
    if depth4_rounds and x4 > 0 and depth4_mode in {"mask", "mask_precompute"}:
        if depth4_mode == "mask_precompute":
            valu_ops += mask_pre_valu_per_depth.get(4, 0) * x4 * len(depth4_rounds)
        else:
            valu_ops += mask_valu_per_depth.get(4, 0) * x4 * len(depth4_rounds)
    if depth5_rounds and x5 > 0 and depth5_mode in {"mask", "mask_precompute"}:
        if depth5_mode == "mask_precompute":
            valu_ops += mask_pre_valu_per_depth.get(5, 0) * x5 * len(depth5_rounds)
        else:
            valu_ops += mask_valu_per_depth.get(5, 0) * x5 * len(depth5_rounds)
    return valu_ops


def _uncached_rounds(cfg) -> int:
    cached_full = set(cfg.get("base_cached_rounds", []))
    depth4_rounds = set(cfg.get("depth4_rounds", []))
    depth5_rounds = set(cfg.get("depth5_rounds", []))
    uncached = [r for r in range(ROUNDS) if r not in cached_full and r not in depth4_rounds and r not in depth5_rounds]
    return len(uncached)


def _compute_counts(cfg, *, T: int, x4: int, x5: int) -> StrategyCounts | None:
    valu_cap = 6 * T
    alu_cap = 12 * T
    load_cap = 2 * T
    flow_cap = T

    setup_flow, setup_load, setup_valu, setup_alu = _setup_counts(cfg, x4=x4, x5=x5)

    # Flow ops
    reset_on_flow = bool(cfg.get("reset_on_flow", False))
    reset_flow_ops = VEC if reset_on_flow else 0
    flow_ops = setup_flow + _selection_flow(cfg, x4=x4, x5=x5) + reset_flow_ops

    # Load ops
    vloads = 2 * VEC
    cached_nodes = _cached_nodes(cfg, x4=x4, x5=x5)
    preload_nodes = cached_nodes if cached_nodes > 0 else 0
    uncached_full_rounds = _uncached_rounds(cfg)
    depth4_rounds = cfg.get("depth4_rounds", [])
    depth5_rounds = cfg.get("depth5_rounds", [])
    load_ops = (
        setup_load
        + vloads
        + preload_nodes
        + uncached_full_rounds * VEC * VLEN
        + len(depth4_rounds) * (VEC - x4) * VLEN
        + len(depth5_rounds) * (VEC - x5) * VLEN
    )

    # VALU ops (pre-offload)
    idx_shifted = bool(cfg.get("idx_shifted", False))
    parity_update_ops = 2 if idx_shifted else 3
    reset_valu_ops = 0 if reset_on_flow else RESET_VALU_OPS
    total_valu = (
        (HASH_VALU_PER_VEC + NODE_XOR_PER_VEC + PARITY_ROUNDS * parity_update_ops) * VEC
        + reset_valu_ops * VEC
        + setup_valu
    )
    # Mask-based selection adds VALU ops for bit extraction.
    total_valu += _selection_valu(cfg, x4=x4, x5=x5)
    total_valu += _selection_valu(cfg, x4=x4, x5=x5)

    shift_on_alu = bool(cfg.get("shift_on_alu", False))
    parity_on_alu = bool(cfg.get("parity_on_alu", False))
    shift_ops = 3 * ROUNDS * VEC
    parity_ops = PARITY_ROUNDS * VEC
    if shift_on_alu:
        total_valu -= shift_ops
    if parity_on_alu:
        total_valu -= parity_ops

    addr_on_alu = bool(cfg.get("addr_on_alu", False))
    if addr_on_alu:
        addr_ops = (
            uncached_full_rounds * VEC
            + len(depth4_rounds) * (VEC - x4)
            + len(depth5_rounds) * (VEC - x5)
        )
        total_valu -= addr_ops

    max_offload = int(cfg.get("max_offload", MAX_OFFLOAD))
    min_offload = max(0, total_valu - valu_cap)
    if min_offload > max_offload:
        return None

    # ALU ops
    alu_ops = setup_alu + _selection_alu(cfg, x4=x4, x5=x5)
    if shift_on_alu:
        alu_ops += shift_ops * VLEN
    if parity_on_alu:
        alu_ops += parity_ops * VLEN
    if addr_on_alu:
        alu_ops += (
            uncached_full_rounds * VEC
            + len(depth4_rounds) * (VEC - x4)
            + len(depth5_rounds) * (VEC - x5)
        ) * VLEN

    alu_ops += min_offload * VLEN
    valu_ops = total_valu - min_offload

    if load_ops > load_cap:
        return None
    if flow_ops > flow_cap:
        return None
    if alu_ops > alu_cap:
        return None
    if valu_ops > valu_cap:
        return None

    alu_slack = alu_cap - alu_ops
    extra_offload = min(alu_slack // VLEN, max_offload - min_offload)
    setup_slack = extra_offload

    return StrategyCounts(
        flow_ops=flow_ops,
        load_ops=load_ops,
        valu_ops=valu_ops,
        alu_ops=alu_ops,
        min_offload=min_offload,
        setup_slack=setup_slack,
    )


def feasible_strategy(cfg, *, T_values: Iterable[int]) -> list[Result]:
    x4_values = _expand_values(cfg.get("x4"), name="x4", default=[0])
    x5_values = _expand_values(cfg.get("x5"), name="x5", default=[0])
    results: list[Result] = []

    for T in T_values:
        for x4 in x4_values:
            for x5 in x5_values:
                counts = _compute_counts(cfg, T=T, x4=x4, x5=x5)
                if counts is None:
                    continue
                results.append(
                    Result(
                        T=T,
                        x4=x4,
                        x5=x5,
                        flow_ops=counts.flow_ops,
                        load_ops=counts.load_ops,
                        min_offload=counts.min_offload,
                        alu_ops=counts.alu_ops,
                        valu_ops=counts.valu_ops,
                        setup_slack=counts.setup_slack,
                    )
                )
    return results


def format_rows(results: Iterable[Result]) -> list[str]:
    rows = []
    for r in results:
        rows.append(
            f"T={r.T} x4={r.x4:2d} x5={r.x5:2d} "
            f"load={r.load_ops:4d} flow={r.flow_ops:4d} "
            f"min_offload={r.min_offload:4d} alu={r.alu_ops:5d} "
            f"valu={r.valu_ops:4d} setup_slack={r.setup_slack:3d}"
        )
    return rows


# --- Legacy sweep (top-4 + optional depth-4) ---

def _legacy_feasible(
    T: int,
    *,
    setup_valu: int,
    flow_setup_ops: int,
    depth4_rounds: int,
    shift_on_alu: bool,
    reset_on_flow: bool,
    parity_on_alu: bool,
    x_values: Iterable[int] | None = None,
) -> list[Result]:
    cfg = {
        "base_cached_rounds": [0, 1, 2, 3, 11, 12, 13, 14],
        "depth4_rounds": [4] if depth4_rounds else [],
        "x4": 0,
        "x5": 0,
        "selection_mode": "eq",
        "idx_shifted": False,
        "shift_on_alu": shift_on_alu,
        "reset_on_flow": reset_on_flow,
        "parity_on_alu": parity_on_alu,
        "ptr_setup_engine": "flow",
        "include_setup": True,
        "flow_setup_ops": flow_setup_ops,
        "setup_valu_ops": setup_valu,
    }
    if x_values is None:
        x_values = range(0, VEC + 1)
    results: list[Result] = []
    for X in x_values:
        cfg["x4"] = X
        counts = _compute_counts(cfg, T=T, x4=X, x5=0)
        if counts is None:
            continue
        results.append(
            Result(
                T=T,
                x4=X,
                x5=0,
                flow_ops=counts.flow_ops,
                load_ops=counts.load_ops,
                min_offload=counts.min_offload,
                alu_ops=counts.alu_ops,
                valu_ops=counts.valu_ops,
                setup_slack=counts.setup_slack,
            )
        )
    return results


def _parse_int_list(value: str, *, name: str) -> list[int]:
    items = [v.strip() for v in value.split(",") if v.strip()]
    if not items:
        raise argparse.ArgumentTypeError(f"{name} must not be empty")
    out = []
    for item in items:
        try:
            out.append(int(item))
        except ValueError as exc:
            raise argparse.ArgumentTypeError(f"{name} must be ints: {item}") from exc
    return out


def _parse_bool_list(value: str, *, name: str) -> list[bool]:
    value = value.strip().lower()
    if value in {"both", "all"}:
        return [False, True]
    if value in {"true", "1", "yes"}:
        return [True]
    if value in {"false", "0", "no"}:
        return [False]
    raise argparse.ArgumentTypeError(f"{name} must be true/false/both")


def main() -> None:
    parser = argparse.ArgumentParser(description="Sweep cache/offload parameters.")
    parser.add_argument("--config", help="JSON file with strategy configs.")
    parser.add_argument("--strategy", help="Strategy name to filter within --config.")
    parser.add_argument("--T", default="1013,1016", help="Comma-separated cycle budgets.")
    parser.add_argument("--json", action="store_true", help="Emit JSON output.")

    # Legacy args
    parser.add_argument(
        "--flow-setup-ops",
        default="0,64",
        help="Comma-separated flow setup counts.",
    )
    parser.add_argument(
        "--shift-on-alu",
        default="both",
        help="Whether shifts are on ALU: true/false/both.",
    )
    parser.add_argument(
        "--reset-on-flow",
        default="both",
        help="Whether reset is on flow: true/false/both.",
    )
    parser.add_argument(
        "--parity-on-alu",
        default="false",
        help="Whether parity (val & 1) is offloaded to ALU: true/false/both.",
    )
    parser.add_argument(
        "--depth4-rounds",
        default="0,1,2",
        help="Comma-separated depth-4 cache rounds.",
    )
    parser.add_argument(
        "--setup-valu",
        default="0,16,32,48",
        help="Comma-separated setup VALU op counts.",
    )
    parser.add_argument(
        "--x",
        default="",
        help="Optional comma-separated list of X values (cached vectors).",
    )

    args = parser.parse_args()
    t_values = _parse_int_list(args.T, name="T")

    if args.config:
        cfg = json.loads(open(args.config, "r", encoding="utf-8").read())
        strategies = cfg.get("strategies") or cfg.get("mappings") or []
        if args.strategy:
            strategies = [s for s in strategies if s.get("name") == args.strategy]
        if not strategies:
            raise SystemExit("No strategies matched.")

        all_results = []
        for s in strategies:
            name = s.get("name", "<unnamed>")
            t_override = s.get("T")
            T_vals = _expand_values(t_override, name="T", default=t_values)
            results = feasible_strategy(s, T_values=T_vals)
            if not results:
                continue
            all_results.append(
                {
                    "name": name,
                    "config": s,
                    "results": [r.__dict__ for r in results],
                }
            )

        if args.json:
            print(json.dumps(all_results, indent=2))
            return

        for entry in all_results:
            print(f"strategy: {entry['name']}")
            for line in format_rows(Result(**r) for r in entry["results"]):
                print(f"  {line}")
        return

    # Legacy mode
    flow_setup_values = _parse_int_list(args.flow_setup_ops, name="flow-setup-ops")
    depth4_values = _parse_int_list(args.depth4_rounds, name="depth4-rounds")
    setup_valu_values = _parse_int_list(args.setup_valu, name="setup-valu")
    shift_values = _parse_bool_list(args.shift_on_alu, name="shift-on-alu")
    reset_values = _parse_bool_list(args.reset_on_flow, name="reset-on-flow")
    parity_values = _parse_bool_list(args.parity_on_alu, name="parity-on-alu")
    x_values: Sequence[int] | None = None
    if args.x.strip():
        x_values = _parse_int_list(args.x, name="x")

    if args.json:
        all_results = []
        for flow_setup_ops in flow_setup_values:
            for shift_on_alu in shift_values:
                for reset_on_flow in reset_values:
                    for parity_on_alu in parity_values:
                        for depth4_rounds in depth4_values:
                            for setup_valu in setup_valu_values:
                                for T in t_values:
                                    results = _legacy_feasible(
                                        T,
                                        setup_valu=setup_valu,
                                        flow_setup_ops=flow_setup_ops,
                                        depth4_rounds=depth4_rounds,
                                        shift_on_alu=shift_on_alu,
                                        reset_on_flow=reset_on_flow,
                                        parity_on_alu=parity_on_alu,
                                        x_values=x_values,
                                    )
                                    if not results:
                                        continue
                                    all_results.append(
                                        {
                                            "T": T,
                                            "flow_setup": flow_setup_ops,
                                            "shift_on_alu": shift_on_alu,
                                            "reset_on_flow": reset_on_flow,
                                            "depth4_rounds": depth4_rounds,
                                            "setup_valu": setup_valu,
                                            "results": [r.__dict__ for r in results],
                                        }
                                    )
        print(json.dumps(all_results, indent=2))
        return

    for flow_setup_ops in flow_setup_values:
        for shift_on_alu in shift_values:
            for reset_on_flow in reset_values:
                for parity_on_alu in parity_values:
                    for depth4_rounds in depth4_values:
                        for setup_valu in setup_valu_values:
                            all_rows: list[str] = []
                            for T in t_values:
                                rows = _legacy_feasible(
                                    T,
                                    setup_valu=setup_valu,
                                    flow_setup_ops=flow_setup_ops,
                                    depth4_rounds=depth4_rounds,
                                    shift_on_alu=shift_on_alu,
                                    reset_on_flow=reset_on_flow,
                                    parity_on_alu=parity_on_alu,
                                    x_values=x_values,
                                )
                                all_rows.extend(format_rows(rows))
                            if not all_rows:
                                continue
                            print(
                                "config: "
                                f"flow_setup={flow_setup_ops} "
                                f"shifts={'alu' if shift_on_alu else 'valu'} "
                                f"reset={'flow' if reset_on_flow else 'valu'} "
                                f"parity={'alu' if parity_on_alu else 'valu'} "
                                f"depth4_rounds={depth4_rounds} "
                                f"setup_valu={setup_valu}"
                            )
                            for line in all_rows:
                                print(f"  {line}")


if __name__ == "__main__":
    main()
