#!/usr/bin/env python3
"""Sweep cache/offload parameters against engine caps for T=1013/1016.

Model assumptions:
- Top-4 caching (depths 0-3) for all vectors, both before and after wrap.
- Optional depth-4 caching for X vectors on round 4 and/or round 15.
- Flow ops are vselect-tree selection + optional pointer add_imm setup.
- Load ops count vloads + cached-node preloads + per-lane loads for uncached rounds.
- VALU ops per vector are derived from hash/node XOR + parity/update + reset.
- Offload uses bitwise op1 only: 1 VALU op -> 8 ALU ops.
- Shifts are on VALU unless explicitly moved to ALU.
"""
from __future__ import annotations

import argparse
import json
from dataclasses import dataclass
from typing import Iterable, Sequence

# Constants
VEC = 32
ROUNDS = 16
VLEN = 8

HASH_VALU_PER_VEC = 12 * ROUNDS  # 192 (includes 3 shifts per round)
NODE_XOR_PER_VEC = ROUNDS  # 16
PARITY_ROUNDS = ROUNDS - 2  # skip round10 and round15
IDX_UPDATE_ROUNDS = ROUNDS - 2  # skip round10 and round15
RESET_VALU_OPS = 1  # round10 reset on VALU (0 if moved to flow)
BASE_VALU_PER_VEC = (
    HASH_VALU_PER_VEC
    + NODE_XOR_PER_VEC
    + PARITY_ROUNDS
    + IDX_UPDATE_ROUNDS
)
MAX_OFFLOAD = 3 * ROUNDS * VEC  # one op per bitwise stage per vector-round

# Cache model (top-4 baseline)
BASE_CACHED_NODES = 15  # levels 0..3
LEVEL4_NODES = 16
BASE_CACHED_ROUNDS = 8  # rounds 0-3 and 11-14 (depths 0..3)

# Flow model
VSELECTS_PER_DEPTH = {0: 0, 1: 1, 2: 3, 3: 7, 4: 15}
FLOW_BASE_TOP4 = VEC * 2 * sum(VSELECTS_PER_DEPTH[d] for d in range(0, 4))
FLOW_PTR_SETUP = 64  # add_imm for idx/val pointers
FLOW_PER_VEC_DEPTH4 = VSELECTS_PER_DEPTH[4]

# Load model
VLOADS = 64

@dataclass
class Result:
    T: int
    X: int
    depth4_rounds: int
    flow_ops: int
    load_ops: int
    min_offload: int
    alu_ops: int
    valu_ops: int
    setup_slack: int


def compute_load_ops(*, depth4_rounds: int, X: int) -> int:
    uncached_full_rounds = ROUNDS - BASE_CACHED_ROUNDS - depth4_rounds
    cached_nodes = BASE_CACHED_NODES + (LEVEL4_NODES if X > 0 else 0)
    full_uncached = uncached_full_rounds * VEC * VLEN
    partial_uncached = depth4_rounds * (VEC - X) * VLEN
    return VLOADS + cached_nodes + full_uncached + partial_uncached


def feasible(
    T: int,
    *,
    setup_valu: int,
    flow_setup_ops: int,
    depth4_rounds: int,
    shift_on_alu: bool,
    reset_on_flow: bool,
    x_values: Iterable[int] | None = None,
) -> list[Result]:
    valu_cap = 6 * T
    alu_cap = 12 * T
    load_cap = 2 * T
    flow_cap = T

    flow_base = FLOW_BASE_TOP4 + flow_setup_ops
    shift_ops = 3 * ROUNDS * VEC
    shift_alu_ops = shift_ops * VLEN if shift_on_alu else 0
    reset_valu_ops = 0 if reset_on_flow else RESET_VALU_OPS
    reset_flow_ops = VEC if reset_on_flow else 0

    out: list[Result] = []
    if x_values is None:
        x_values = range(0, VEC + 1)

    for X in x_values:
        load_ops = compute_load_ops(depth4_rounds=depth4_rounds, X=X)
        flow_ops = flow_base + FLOW_PER_VEC_DEPTH4 * X * depth4_rounds + reset_flow_ops

        # Offload needed to fit VALU cap including setup_valu
        total_valu = (
            BASE_VALU_PER_VEC * VEC
            + reset_valu_ops * VEC
            + setup_valu
            - (shift_ops if shift_on_alu else 0)
        )
        min_offload = max(0, total_valu - valu_cap)
        if min_offload > MAX_OFFLOAD:
            continue

        alu_ops = min_offload * VLEN + shift_alu_ops
        valu_ops = total_valu - min_offload

        if load_ops > load_cap:
            continue
        if flow_ops > flow_cap:
            continue
        if alu_ops > alu_cap:
            continue
        if valu_ops > valu_cap:
            continue

        # Remaining VALU slack for additional setup if you offload more
        alu_slack = alu_cap - alu_ops
        # Each extra offload frees 1 VALU slot and costs 8 ALU slots
        extra_offload = min(alu_slack // VLEN, MAX_OFFLOAD - min_offload)
        setup_slack = extra_offload  # additional VALU ops you can fit

        out.append(
            Result(
                T=T,
                X=X,
                depth4_rounds=depth4_rounds,
                flow_ops=flow_ops,
                load_ops=load_ops,
                min_offload=min_offload,
                alu_ops=alu_ops,
                valu_ops=valu_ops,
                setup_slack=setup_slack,
            )
        )
    return out


def format_rows(results: Iterable[Result]) -> list[str]:
    rows = []
    for r in results:
        rows.append(
            f"T={r.T} depth4={r.depth4_rounds} X={r.X:2d} "
            f"load={r.load_ops:4d} flow={r.flow_ops:4d} "
            f"min_offload={r.min_offload:4d} alu={r.alu_ops:5d} "
            f"valu={r.valu_ops:4d} setup_slack={r.setup_slack:3d}"
        )
    return rows


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
    parser.add_argument("--T", default="1013,1016", help="Comma-separated cycle budgets.")
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
    parser.add_argument("--json", action="store_true", help="Emit JSON output.")
    args = parser.parse_args()

    t_values = _parse_int_list(args.T, name="T")
    flow_setup_values = _parse_int_list(args.flow_setup_ops, name="flow-setup-ops")
    depth4_values = _parse_int_list(args.depth4_rounds, name="depth4-rounds")
    setup_valu_values = _parse_int_list(args.setup_valu, name="setup-valu")
    shift_values = _parse_bool_list(args.shift_on_alu, name="shift-on-alu")
    reset_values = _parse_bool_list(args.reset_on_flow, name="reset-on-flow")
    x_values: Sequence[int] | None = None
    if args.x.strip():
        x_values = _parse_int_list(args.x, name="x")

    if args.json:
        all_results = []
        for flow_setup_ops in flow_setup_values:
            for shift_on_alu in shift_values:
                for reset_on_flow in reset_values:
                    for depth4_rounds in depth4_values:
                        for setup_valu in setup_valu_values:
                            for T in t_values:
                                results = feasible(
                                    T,
                                    setup_valu=setup_valu,
                                    flow_setup_ops=flow_setup_ops,
                                    depth4_rounds=depth4_rounds,
                                    shift_on_alu=shift_on_alu,
                                    reset_on_flow=reset_on_flow,
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
                for depth4_rounds in depth4_values:
                    for setup_valu in setup_valu_values:
                        all_rows: list[str] = []
                        for T in t_values:
                            rows = feasible(
                                T,
                                setup_valu=setup_valu,
                                flow_setup_ops=flow_setup_ops,
                                depth4_rounds=depth4_rounds,
                                shift_on_alu=shift_on_alu,
                                reset_on_flow=reset_on_flow,
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
                            f"depth4_rounds={depth4_rounds} "
                            f"setup_valu={setup_valu}"
                        )
                        for line in all_rows:
                            print(f"  {line}")


if __name__ == "__main__":
    main()
