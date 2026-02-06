#!/usr/bin/env python3
"""
Post-analysis for pareto_dp.py output.

Reports binding caps, slack, and deltas needed to hit a target T.
Intended to guide human/agent graph changes (not automatic edits).
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any


def _ceil_div(a: int, b: int) -> int:
    if b <= 0:
        return 0
    return (a + b - 1) // b


def _offload_cap(state: dict[str, Any], globals_cfg: dict[str, Any]) -> int:
    if globals_cfg.get("offload_order_mode") == "unlocked":
        return int(state.get("offloadable", 0))
    return min(int(state.get("offloadable", 0)), int(state.get("offload_prefix", 0)))


def _min_T_for_valu(state: dict[str, Any], caps: dict[str, int], globals_cfg: dict[str, Any]) -> int:
    alu_cap = int(caps.get("alu", 12))
    valu_cap = int(caps.get("valu", 6))
    offcap = _offload_cap(state, globals_cfg)
    T = 0
    while True:
        lower = max(0, int(state["valu_raw"]) - valu_cap * T)
        upper = min(offcap, (alu_cap * T - int(state["alu_base"])) // 8)
        if upper >= lower:
            return T
        T += 1


def _binding_caps(state: dict[str, Any], caps: dict[str, int], globals_cfg: dict[str, Any]) -> dict[str, Any]:
    t_flow = _ceil_div(int(state["flow"]), int(caps.get("flow", 1)))
    t_load = _ceil_div(int(state["load"]), int(caps.get("load", 2)))
    t_store = _ceil_div(int(state["store"]), int(caps.get("store", 2)))
    t_alu = _ceil_div(int(state["alu_base"]), int(caps.get("alu", 12)))
    t_valu = _min_T_for_valu(state, caps, globals_cfg)
    ts = {
        "flow": t_flow,
        "load": t_load,
        "store": t_store,
        "alu": t_alu,
        "valu/offload": t_valu,
    }
    tmax = max(ts.values())
    binding = [k for k, v in ts.items() if v == tmax]
    return {"T": tmax, "by_cap": ts, "binding": binding}


def _deltas_to_target(state: dict[str, Any], caps: dict[str, int], globals_cfg: dict[str, Any], target: int) -> dict[str, Any]:
    alu_cap = int(caps.get("alu", 12))
    valu_cap = int(caps.get("valu", 6))
    flow_cap = int(caps.get("flow", 1))
    load_cap = int(caps.get("load", 2))
    store_cap = int(caps.get("store", 2))

    need_flow = max(0, int(state["flow"]) - flow_cap * target)
    need_load = max(0, int(state["load"]) - load_cap * target)
    need_store = max(0, int(state["store"]) - store_cap * target)
    need_alu = max(0, int(state["alu_base"]) - alu_cap * target)

    offcap = _offload_cap(state, globals_cfg)
    lower = max(0, int(state["valu_raw"]) - valu_cap * target)
    upper = min(offcap, (alu_cap * target - int(state["alu_base"])) // 8)

    valu_ok = upper >= lower
    valu_reduction_needed = 0
    offload_extra_needed = 0
    if not valu_ok:
        # Required: valu_raw <= valu_cap * T + upper
        valu_reduction_needed = max(
            0, int(state["valu_raw"]) - (valu_cap * target + upper)
        )
        offload_extra_needed = max(0, lower - upper)

    return {
        "target": target,
        "need_flow": need_flow,
        "need_load": need_load,
        "need_store": need_store,
        "need_alu": need_alu,
        "valu_ok": valu_ok,
        "offload_cap": offcap,
        "offload_needed": lower,
        "offload_headroom": max(0, upper - lower),
        "valu_reduction_needed": valu_reduction_needed,
        "offload_extra_needed": offload_extra_needed,
    }


def main() -> int:
    ap = argparse.ArgumentParser(description="Post-analysis for pareto_dp.py output.")
    ap.add_argument("input", type=Path, help="pareto_dp.py JSON output")
    ap.add_argument("--mode", choices=["real", "ideal"], default="real")
    ap.add_argument("--target", type=int, default=None, help="Target T for delta report")
    ap.add_argument("--json", action="store_true", help="Emit JSON output")
    args = ap.parse_args()

    data = json.loads(args.input.read_text(encoding="utf-8"))
    globals_cfg = data.get("globals", {})
    caps = data.get("caps", {})
    state = data.get(args.mode)
    if state is None:
        raise SystemExit(f"no '{args.mode}' result in {args.input}")

    binding = _binding_caps(state, caps, globals_cfg)
    target = args.target if args.target is not None else binding["T"]
    deltas = _deltas_to_target(state, caps, globals_cfg, target)

    out = {
        "mode": args.mode,
        "best": state,
        "binding": binding,
        "deltas": deltas,
    }

    if args.json:
        print(json.dumps(out, indent=2))
        return 0

    print("Mode:", args.mode)
    print("Best:", state)
    print("Binding:", binding)
    print("Deltas:", deltas)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
