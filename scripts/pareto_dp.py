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
import pickle
import sys
import time
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


def _suffix_bounds(
    rounds: list[dict[str, Any]],
    globals_cfg: dict[str, Any],
) -> list[dict[str, int]]:
    n = len(rounds)
    suffix = [
        {
            "alu_base": 0,
            "valu_raw": 0,
            "flow": 0,
            "load": 0,
            "store": 0,
            "offloadable": 0,
            "offload_prefix": 0,
        }
        for _ in range(n + 1)
    ]
    for i in range(n - 1, -1, -1):
        choices = [
            c
            for c in rounds[i].get("choices", [])
            if _check_requires(c, globals_cfg)
        ]
        if not choices:
            suffix[i] = dict(suffix[i + 1])
            continue
        suffix[i] = {
            "alu_base": suffix[i + 1]["alu_base"]
            + min(int(c.get("alu_base", 0)) for c in choices),
            "valu_raw": suffix[i + 1]["valu_raw"]
            + min(int(c.get("valu_raw", 0)) for c in choices),
            "flow": suffix[i + 1]["flow"]
            + min(int(c.get("flow", 0)) for c in choices),
            "load": suffix[i + 1]["load"]
            + min(int(c.get("load", 0)) for c in choices),
            "store": suffix[i + 1]["store"]
            + min(int(c.get("store", 0)) for c in choices),
            "offloadable": suffix[i + 1]["offloadable"]
            + max(int(c.get("offloadable", 0)) for c in choices),
            "offload_prefix": suffix[i + 1]["offload_prefix"]
            + max(int(c.get("offload_prefix", 0)) for c in choices),
        }
    return suffix


def _apply_suffix(state: State, suffix: dict[str, int]) -> State:
    return State(
        alu_base=state.alu_base + suffix["alu_base"],
        valu_raw=state.valu_raw + suffix["valu_raw"],
        flow=state.flow + suffix["flow"],
        load=state.load + suffix["load"],
        store=state.store + suffix["store"],
        offloadable=state.offloadable + suffix["offloadable"],
        offload_prefix=state.offload_prefix + suffix["offload_prefix"],
        prefix_open=state.prefix_open,
        scratch=state.scratch,
        choice_path=state.choice_path,
    )


def _run_dp(
    cfg: dict[str, Any],
    *,
    include_setup: bool,
    caps: dict[str, int],
    max_states: int,
    offload_order_mode: str,
    max_T: int | None,
    progress_log: Path | None,
    checkpoint: Path | None,
    checkpoint_every: int,
    resume_state: tuple[int, list[State]] | None,
    log_every_seconds: float,
) -> list[State]:
    globals_cfg = cfg.get("globals", {})
    scratch_mode = globals_cfg.get("scratch_mode", "max")
    scratch_limit = int(cfg.get("scratch_limit", 1536))
    rounds = cfg.get("rounds", [])
    suffix = _suffix_bounds(rounds, globals_cfg)

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

    start_round = 0
    if resume_state is not None:
        start_round, frontier = resume_state
    else:
        frontier = [base]

    if offload_order_mode == "unlocked":
        base.prefix_open = True

    best_T: int | None = None

    last_log = time.monotonic()
    for round_idx in range(start_round, len(rounds)):
        round_cfg = rounds[round_idx]
        next_states: list[State] = []
        processed = 0
        choices = round_cfg.get("choices", [])
        total_est = max(1, len(frontier) * max(1, len(choices)))
        for state in frontier:
            for choice in choices:
                if not _check_requires(choice, globals_cfg):
                    continue
                new_state = _apply_choice(
                    state,
                    choice,
                    scratch_mode,
                    offload_order_mode,
                )
                if offload_order_mode == "unlocked":
                    new_state.prefix_open = True
                if new_state.scratch > scratch_limit:
                    continue
                if round_idx == len(rounds) - 1:
                    T = _min_T_for_state(
                        new_state,
                        offload_order_mode=offload_order_mode,
                        caps=caps,
                        max_T=max_T,
                    )
                    if T is not None and (best_T is None or T < best_T):
                        best_T = T
                        if progress_log is not None:
                            progress_log.parent.mkdir(parents=True, exist_ok=True)
                            with progress_log.open("a", encoding="utf-8") as f:
                                f.write(
                                    json.dumps(
                                        {
                                            "event": "best",
                                            "round": round_idx,
                                            "T": best_T,
                                            "alu_base": new_state.alu_base,
                                            "valu_raw": new_state.valu_raw,
                                            "flow": new_state.flow,
                                            "load": new_state.load,
                                            "store": new_state.store,
                                            "offloadable": new_state.offloadable,
                                            "offload_prefix": new_state.offload_prefix,
                                            "scratch": new_state.scratch,
                                        }
                                    )
                                    + "\n"
                                )
                next_states.append(new_state)
                processed += 1
                if (
                    log_every_seconds > 0
                    and processed % 256 == 0
                    and (time.monotonic() - last_log) >= log_every_seconds
                ):
                    print(
                        f"[dp] round {round_idx+1}/{len(rounds)} "
                        f"processed {processed}/{total_est} candidates "
                        f"(frontier={len(frontier)}, next={len(next_states)})",
                        file=sys.stderr,
                        flush=True,
                    )
                    last_log = time.monotonic()
        frontier = _pareto_prune(next_states)

        if max_states > 0 and len(frontier) > max_states:
            scored = []
            for s in frontier:
                optimistic = _apply_suffix(s, suffix[round_idx + 1])
                lb_T = _min_T_for_state(
                    optimistic,
                    offload_order_mode=offload_order_mode,
                    caps=caps,
                    max_T=best_T,
                )
                scored.append((lb_T if lb_T is not None else 10**9, s))
            scored.sort(key=lambda x: x[0])
            frontier = [s for _, s in scored[:max_states]]

        best_lb = None
        if progress_log is not None or log_every_seconds > 0:
            for s in frontier:
                optimistic = _apply_suffix(s, suffix[round_idx + 1])
                lb_T = _min_T_for_state(
                    optimistic,
                    offload_order_mode=offload_order_mode,
                    caps=caps,
                    max_T=None,
                )
                if lb_T is not None and (best_lb is None or lb_T < best_lb):
                    best_lb = lb_T
        if progress_log is not None:
            progress_log.parent.mkdir(parents=True, exist_ok=True)
            with progress_log.open("a", encoding="utf-8") as f:
                f.write(json.dumps({"event": "lb", "round": round_idx, "best_lb": best_lb}) + "\n")
        if log_every_seconds > 0 and (time.monotonic() - last_log) >= log_every_seconds:
            print(
                f"[dp] round {round_idx+1}/{len(rounds)} done "
                f"(frontier={len(frontier)}, lb={best_lb})",
                file=sys.stderr,
                flush=True,
            )
            last_log = time.monotonic()

        if checkpoint is not None and (round_idx + 1) % checkpoint_every == 0:
            checkpoint.parent.mkdir(parents=True, exist_ok=True)
            with checkpoint.open("wb") as f:
                pickle.dump({"next_round": round_idx + 1, "frontier": frontier}, f)
    return frontier


def main() -> int:
    ap = argparse.ArgumentParser(description="Pareto DP for per-round op-graph strategies.")
    ap.add_argument("input", type=Path, help="JSON input file")
    ap.add_argument("--max-states", type=int, default=0, help="Optional cap on frontier size")
    ap.add_argument("--progress-log", type=Path, default=None, help="Append JSONL progress logs")
    ap.add_argument("--checkpoint", type=Path, default=None, help="Pickle checkpoint path")
    ap.add_argument("--checkpoint-every", type=int, default=1, help="Save checkpoint every N rounds")
    ap.add_argument("--resume", action="store_true", help="Resume from checkpoint")
    ap.add_argument("--max-T", type=int, default=None, help="Override caps.T")
    ap.add_argument("--log-every-seconds", type=float, default=0.0, help="Emit periodic stdout progress")
    ap.add_argument("--json", action="store_true", help="Emit JSON output")
    args = ap.parse_args()

    cfg = _normalize_config(json.loads(args.input.read_text(encoding="utf-8")))
    globals_cfg = cfg.get("globals", {})
    offload_order_mode = globals_cfg.get("offload_order_mode", "round_major")
    caps = _caps_from_cfg(cfg)
    if args.max_T is not None:
        caps["T"] = args.max_T
    max_T = caps.get("T")

    resume_state = None
    if args.resume and args.checkpoint is not None and args.checkpoint.exists():
        with args.checkpoint.open("rb") as f:
            payload = pickle.load(f)
        resume_state = (
            int(payload.get("next_round", 0)),
            payload.get("frontier", []),
        )

    # Run DP twice.
    frontier_real = _run_dp(
        cfg,
        include_setup=True,
        caps=caps,
        max_states=args.max_states,
        offload_order_mode=offload_order_mode,
        max_T=max_T,
        progress_log=args.progress_log,
        checkpoint=args.checkpoint,
        checkpoint_every=args.checkpoint_every,
        resume_state=resume_state,
        log_every_seconds=args.log_every_seconds,
    )
    frontier_ideal = _run_dp(
        cfg,
        include_setup=False,
        caps=caps,
        max_states=args.max_states,
        offload_order_mode=offload_order_mode,
        max_T=max_T,
        progress_log=None,
        checkpoint=None,
        checkpoint_every=1,
        resume_state=None,
        log_every_seconds=0.0,
    )

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

    real_best = out.get("real", {})
    ideal_best = out.get("ideal", {})
    best_line = f"BEST_T_REAL={real_best.get('T')} BEST_T_IDEAL={ideal_best.get('T')}"

    if args.json:
        # Keep JSON clean on stdout; emit a summary line on stderr.
        print(best_line, file=sys.stderr, flush=True)
        print(json.dumps(out, indent=2))
        return 0

    print(best_line, flush=True)
    print("Best (real):", out["real"])
    print("Best (ideal):", out["ideal"])
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
