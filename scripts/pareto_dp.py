#!/usr/bin/env python3
"""
Pareto DP over per-round op-graph choices.

Input schema (JSON) expects:
- globals: knobs and policy flags (idx_shifted, include_setup, offload_order_mode, etc.)
- setup_profiles: keyed dict of setup cost profiles
- rounds: list of {round: int, choices: [choice, ...]}
- caps: {T: int} or empty (T computed)
- scratch_limit: int

Each choice should include:
  name, alu_base, valu_raw, flow, load, store,
  offloadable, offload_prefix,
  scratch_delta (optional), scratch_abs (optional),
  requires (optional dict of constraints).
"""
from __future__ import annotations

import argparse
import json
from dataclasses import dataclass
from pathlib import Path
from typing import Any


@dataclass
class State:
    alu_base: int
    valu_raw: int
    flow: int
    load: int
    store: int
    offloadable: int
    offload_prefix: int
    prefix_open: bool
    scratch: int
    choice_path: list[str]


def _ceil_div(a: int, b: int) -> int:
    if b <= 0:
        return 0
    return (a + b - 1) // b


def _dominates(a: State, b: State) -> bool:
    # Minimize alu/valu/flow/load/store/scratch, maximize offloadable/prefix.
    a_prefix = 1 if a.prefix_open else 0
    b_prefix = 1 if b.prefix_open else 0
    if (
        a.alu_base > b.alu_base
        or a.valu_raw > b.valu_raw
        or a.flow > b.flow
        or a.load > b.load
        or a.store > b.store
        or a.scratch > b.scratch
        or a.offloadable < b.offloadable
        or a.offload_prefix < b.offload_prefix
        or a_prefix < b_prefix
    ):
        return False
    return (
        a.alu_base < b.alu_base
        or a.valu_raw < b.valu_raw
        or a.flow < b.flow
        or a.load < b.load
        or a.store < b.store
        or a.scratch < b.scratch
        or a.offloadable > b.offloadable
        or a.offload_prefix > b.offload_prefix
        or a_prefix > b_prefix
    )


def _pareto_prune(states: list[State]) -> list[State]:
    kept: list[State] = []
    for s in states:
        dominated = False
        to_remove = []
        for i, k in enumerate(kept):
            if _dominates(k, s):
                dominated = True
                break
            if _dominates(s, k):
                to_remove.append(i)
        if dominated:
            continue
        for i in reversed(to_remove):
            kept.pop(i)
        kept.append(s)
    return kept


def _check_requires(choice: dict[str, Any], globals_cfg: dict[str, Any]) -> bool:
    req = choice.get("requires", {})
    for key, val in req.items():
        if globals_cfg.get(key) != val:
            return False
    if not globals_cfg.get("allow_per_round_selection", False):
        global_sel = globals_cfg.get("selection_mode") or globals_cfg.get("selection_mode_default")
        choice_sel = choice.get("selection_mode") or choice.get("selection_mode_override")
        if global_sel is not None and choice_sel is not None and choice_sel != global_sel:
            return False
    return True


def _choice_prefix(choice: dict[str, Any], *, order_mode: str) -> int:
    if order_mode == "vector_major":
        if int(choice.get("offloadable", 0)) == 0:
            return 0
        if "offload_prefix_vector_major" in choice:
            return int(choice["offload_prefix_vector_major"])
        if "offload_prefix_vector" in choice:
            return int(choice["offload_prefix_vector"])
        raise ValueError(
            "vector_major offload order requires 'offload_prefix_vector_major' or "
            "'offload_prefix_vector' in choices"
        )
    return int(choice.get("offload_prefix", 0))


def _apply_choice(prev: State, choice: dict[str, Any], scratch_mode: str, order_mode: str) -> State:
    scratch = prev.scratch
    scratch_abs = choice.get("scratch_abs")
    scratch_delta = choice.get("scratch_delta")
    if scratch_abs is not None:
        scratch = max(scratch, int(scratch_abs))
    if scratch_delta is not None:
        scratch_delta = int(scratch_delta)
        if scratch_delta < 0:
            raise ValueError("scratch_delta must be non-negative")
        if scratch_mode == "sum":
            scratch = scratch + scratch_delta
        else:
            scratch = max(scratch, scratch + scratch_delta)

    choice_offloadable = int(choice.get("offloadable", 0))
    choice_prefix = _choice_prefix(choice, order_mode=order_mode)
    offloadable = prev.offloadable + choice_offloadable
    if order_mode == "unlocked":
        offload_prefix = offloadable
        prefix_open = True
    else:
        if not prev.prefix_open:
            offload_prefix = prev.offload_prefix
            prefix_open = False
        else:
            total_ops = (
                int(choice.get("alu_base", 0))
                + int(choice.get("valu_raw", 0))
                + int(choice.get("flow", 0))
                + int(choice.get("load", 0))
                + int(choice.get("store", 0))
            )
            offload_prefix = prev.offload_prefix + choice_prefix
            prefix_open = (choice_prefix == total_ops) and (choice_prefix >= choice_offloadable)

    return State(
        alu_base=prev.alu_base + int(choice.get("alu_base", 0)),
        valu_raw=prev.valu_raw + int(choice.get("valu_raw", 0)),
        flow=prev.flow + int(choice.get("flow", 0)),
        load=prev.load + int(choice.get("load", 0)),
        store=prev.store + int(choice.get("store", 0)),
        offloadable=offloadable,
        offload_prefix=offload_prefix,
        prefix_open=prefix_open,
        scratch=scratch,
        choice_path=prev.choice_path + [choice.get("name", "choice")],
    )


def _min_T_for_state(
    s: State,
    *,
    offload_order_mode: str,
    caps: dict[str, int],
    max_T: int | None,
) -> int | None:
    alu_cap = int(caps.get("alu", 12))
    valu_cap = int(caps.get("valu", 6))
    flow_cap = int(caps.get("flow", 1))
    load_cap = int(caps.get("load", 2))
    store_cap = int(caps.get("store", 2))

    if alu_cap <= 0 and s.alu_base > 0:
        return None
    if valu_cap <= 0 and s.valu_raw > 0:
        return None
    if flow_cap <= 0 and s.flow > 0:
        return None
    if load_cap <= 0 and s.load > 0:
        return None
    if store_cap <= 0 and s.store > 0:
        return None

    # Determine offload cap.
    if offload_order_mode == "unlocked":
        offload_cap = s.offloadable
    else:
        offload_cap = min(s.offloadable, s.offload_prefix)

    # Base lower bound from flow/load/store.
    T = max(
        _ceil_div(s.alu_base, alu_cap),
        _ceil_div(s.flow, flow_cap),
        _ceil_div(s.load, load_cap),
        _ceil_div(s.store, store_cap),
    )

    # Increment T until offload feasibility holds (or hit max_T).
    while True:
        if max_T is not None and T > max_T:
            return None

        # Lower/upper offload bounds for this T.
        lower = max(0, s.valu_raw - valu_cap * T)
        upper = min(offload_cap, (alu_cap * T - s.alu_base) // 8)
        if upper >= lower:
            return T
        T += 1


def _normalize_config(cfg: dict[str, Any]) -> dict[str, Any]:
    if "setup_costs" in cfg and "setup_profiles" not in cfg:
        cfg["setup_profiles"] = {"default": cfg["setup_costs"]}
    setup_profiles = cfg.get("setup_profiles", {})
    for profile in setup_profiles.values():
        if "alu_base" not in profile and "alu" in profile:
            profile["alu_base"] = profile["alu"]
        if "valu_raw" not in profile and "valu" in profile:
            profile["valu_raw"] = profile["valu"]

    for round_cfg in cfg.get("rounds", []):
        for choice in round_cfg.get("choices", []):
            if "alu_base" not in choice and "alu" in choice:
                choice["alu_base"] = choice["alu"]
            if "valu_raw" not in choice and "valu" in choice:
                choice["valu_raw"] = choice["valu"]

    globals_cfg = cfg.get("globals", {})
    order_mode = globals_cfg.get("offload_order_mode", "round_major")
    if order_mode not in {"round_major", "vector_major", "unlocked"}:
        raise ValueError(f"unknown offload_order_mode {order_mode!r}")
    if order_mode == "vector_major":
        for round_cfg in cfg.get("rounds", []):
            for choice in round_cfg.get("choices", []):
                if int(choice.get("offloadable", 0)) == 0:
                    continue
                if (
                    "offload_prefix_vector_major" not in choice
                    and "offload_prefix_vector" not in choice
                ):
                    raise ValueError(
                        "vector_major offload requires per-choice "
                        "'offload_prefix_vector_major' (or 'offload_prefix_vector')"
                    )
    return cfg


def _caps_from_cfg(cfg: dict[str, Any]) -> dict[str, int]:
    caps = cfg.get("caps", {})
    return {
        "T": caps.get("T"),
        "alu": caps.get("alu", 12),
        "valu": caps.get("valu", 6),
        "flow": caps.get("flow", 1),
        "load": caps.get("load", 2),
        "store": caps.get("store", 2),
    }


def _rough_T_lower_bound(s: State, caps: dict[str, int]) -> int:
    return max(
        _ceil_div(s.alu_base, int(caps.get("alu", 12))),
        _ceil_div(s.flow, int(caps.get("flow", 1))),
        _ceil_div(s.load, int(caps.get("load", 2))),
        _ceil_div(s.store, int(caps.get("store", 2))),
        _ceil_div(s.valu_raw, int(caps.get("valu", 6))),
    )


def _run_dp(
    cfg: dict[str, Any],
    *,
    include_setup: bool,
    caps: dict[str, int],
    max_states: int,
) -> list[State]:
    globals_cfg = cfg.get("globals", {})
    scratch_mode = globals_cfg.get("scratch_mode", "max")
    scratch_limit = int(cfg.get("scratch_limit", 1536))

    setup_profiles = cfg.get("setup_profiles", {})
    setup_name = globals_cfg.get("setup_profile", "default")
    setup = setup_profiles.get(setup_name, {})

    if include_setup:
        setup_offloadable = int(setup.get("offloadable", 0))
        setup_prefix = int(setup.get("offload_prefix", 0))
        base = State(
            alu_base=int(setup.get("alu_base", 0)),
            valu_raw=int(setup.get("valu_raw", 0)),
            flow=int(setup.get("flow", 0)),
            load=int(setup.get("load", 0)),
            store=int(setup.get("store", 0)),
            offloadable=setup_offloadable,
            offload_prefix=setup_prefix,
            prefix_open=setup_prefix >= setup_offloadable,
            scratch=int(setup.get("scratch", 0)),
            choice_path=[],
        )
    else:
        base = State(0, 0, 0, 0, 0, 0, 0, True, 0, [])

    frontier: list[State] = [base]
    if globals_cfg.get("offload_order_mode", "round_major") == "unlocked":
        base.prefix_open = True
    for round_cfg in cfg.get("rounds", []):
        next_states: list[State] = []
        for state in frontier:
            for choice in round_cfg.get("choices", []):
                if not _check_requires(choice, globals_cfg):
                    continue
                new_state = _apply_choice(
                    state,
                    choice,
                    scratch_mode,
                    globals_cfg.get("offload_order_mode", "round_major"),
                )
                if globals_cfg.get("offload_order_mode", "round_major") == "unlocked":
                    new_state.prefix_open = True
                if new_state.scratch > scratch_limit:
                    continue
                next_states.append(new_state)
        frontier = _pareto_prune(next_states)
        if max_states > 0 and len(frontier) > max_states:
            frontier.sort(key=lambda s: _rough_T_lower_bound(s, caps))
            frontier = frontier[:max_states]
    return frontier


def main() -> int:
    ap = argparse.ArgumentParser(description="Pareto DP for per-round op-graph strategies.")
    ap.add_argument("input", type=Path, help="JSON input file")
    ap.add_argument("--max-states", type=int, default=0, help="Optional cap on frontier size")
    ap.add_argument("--json", action="store_true", help="Emit JSON output")
    args = ap.parse_args()

    cfg = _normalize_config(json.loads(args.input.read_text(encoding="utf-8")))
    globals_cfg = cfg.get("globals", {})
    offload_order_mode = globals_cfg.get("offload_order_mode", "round_major")
    caps = _caps_from_cfg(cfg)
    max_T = caps.get("T")

    # Run DP twice.
    frontier_real = _run_dp(cfg, include_setup=True, caps=caps, max_states=args.max_states)
    frontier_ideal = _run_dp(cfg, include_setup=False, caps=caps, max_states=args.max_states)

    def best_state(frontier: list[State]) -> dict[str, Any] | None:
        best = None
        best_T = None
        for s in frontier:
            T = _min_T_for_state(
                s,
                offload_order_mode=offload_order_mode,
                caps=caps,
                max_T=max_T,
            )
            if T is None:
                continue
            if best is None or T < best_T:
                best = s
                best_T = T
        if best is None:
            return None
        return {
            "T": best_T,
            "alu_base": best.alu_base,
            "valu_raw": best.valu_raw,
            "flow": best.flow,
            "load": best.load,
            "store": best.store,
            "offloadable": best.offloadable,
            "offload_prefix": best.offload_prefix,
            "prefix_open": best.prefix_open,
            "scratch": best.scratch,
            "choices": best.choice_path,
        }

    out = {
        "globals": globals_cfg,
        "caps": caps,
        "real": best_state(frontier_real),
        "ideal": best_state(frontier_ideal),
        "frontier_sizes": {
            "real": len(frontier_real),
            "ideal": len(frontier_ideal),
        },
    }
    if globals_cfg.get("allow_per_round_selection", False):
        out["mode"] = "speculative_requires_generator_change"
    else:
        out["mode"] = "faithful_global_selection"

    if args.json:
        print(json.dumps(out, indent=2))
        return 0

    print("Best (real):", out["real"])
    print("Best (ideal):", out["ideal"])
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
