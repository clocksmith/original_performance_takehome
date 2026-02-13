#!/usr/bin/env python3
"""
Energy-based search over SpecBase knobs.

This treats kernel search as an energy minimization problem:
  energy = constraint_penalty + lambda * cycles + penalty * max(0, lower_bound_cycles - target)

Constraint penalties are computed before building the DAG; if they exceed a threshold,
we skip scheduling and return constraint energy plus a large fallback cycles term so
skipped specs do not dominate the search.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import math
import os
import random
import sys
import time
from collections import defaultdict
from dataclasses import replace, fields
from typing import Any

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
if ROOT not in sys.path:
    sys.path.insert(0, ROOT)

from generator.spec_base import SPEC_BASE, SpecBase
from problem import SLOT_LIMITS, VLEN
from scripts.graph_dp_auto_search import build_final_ops, schedule_graph_with_restarts
from generator.build_kernel_base import build_base_instrs
from generator.scratch_layout import ScratchAlloc, build_layout
from generator.schedule_dep import _build_deps as _sched_build_deps

CAPS = {k: v for k, v in SLOT_LIMITS.items() if k != "debug"}
CANONICAL_DEPTH = {0: 0, 11: 0, 1: 1, 12: 1, 2: 2, 13: 2, 3: 3, 14: 3}
CANONICAL_ROUNDS = set(CANONICAL_DEPTH.keys())
MIN_CACHED_NODES = {0: 1, 1: 3, 2: 7, 3: 15, 4: 31, 5: 63}
OFFLOAD_SWAP_CATEGORIES = ("hash_shift", "hash_op1", "hash_op2", "parity", "node_xor")


def _offload_budget_for_category(spec, cat: str) -> int:
    attr = f"offload_budget_{cat}"
    if not hasattr(spec, attr):
        return 0
    try:
        return int(getattr(spec, attr))
    except (TypeError, ValueError):
        return 0


def _normalize_offload_budget_swaps(value: Any) -> dict[str, tuple[tuple[int, int], ...]]:
    if not isinstance(value, dict):
        return {}
    out: dict[str, tuple[tuple[int, int], ...]] = {}
    for cat, raw_pairs in value.items():
        if cat not in OFFLOAD_SWAP_CATEGORIES:
            continue
        if not isinstance(raw_pairs, (list, tuple)):
            continue
        pairs: list[tuple[int, int]] = []
        for raw in raw_pairs:
            if not isinstance(raw, (list, tuple)) or len(raw) != 2:
                continue
            try:
                a = int(raw[0])
                b = int(raw[1])
            except (TypeError, ValueError):
                continue
            if a < 0 or b < 0:
                continue
            pairs.append((a, b))
        out[cat] = tuple(pairs)
    return out


def _mutate_offload_budget_swaps(
    spec,
    rnd: random.Random,
    *,
    categories: tuple[str, ...],
    span: int,
    max_swaps_per_cat: int,
):
    cur: dict[str, list[tuple[int, int]]] = {
        cat: list(pairs)
        for cat, pairs in _normalize_offload_budget_swaps(
            getattr(spec, "offload_budget_swaps", {})
        ).items()
    }

    if not categories:
        return replace(spec, offload_budget_swaps={})

    action_roll = rnd.random()
    if action_roll < 0.08:
        return replace(spec, offload_budget_swaps={})

    active_cats = [cat for cat in categories if _offload_budget_for_category(spec, cat) > 0]
    if not active_cats:
        return replace(spec, offload_budget_swaps={})
    cat = rnd.choice(active_cats)

    if action_roll < 0.16:
        cur.pop(cat, None)
        return replace(spec, offload_budget_swaps={k: tuple(v) for k, v in cur.items() if v})

    cat_pairs = cur.get(cat, [])
    if action_roll < 0.32 and cat_pairs:
        cat_pairs.pop(rnd.randrange(len(cat_pairs)))
        if cat_pairs:
            cur[cat] = cat_pairs
        else:
            cur.pop(cat, None)
        return replace(spec, offload_budget_swaps={k: tuple(v) for k, v in cur.items() if v})

    cap = _offload_budget_for_category(spec, cat)
    if cap <= 0:
        return replace(spec, offload_budget_swaps={k: tuple(v) for k, v in cur.items() if v})
    a = rnd.randrange(cap)
    b = rnd.randrange(cap, cap + max(1, span))

    filtered = [p for p in cat_pairs if p[0] != a]
    filtered.append((a, b))
    if max_swaps_per_cat > 0 and len(filtered) > max_swaps_per_cat:
        rnd.shuffle(filtered)
        filtered = filtered[:max_swaps_per_cat]
    cur[cat] = filtered
    return replace(spec, offload_budget_swaps={k: tuple(v) for k, v in cur.items() if v})


def dependency_model_for_spec(spec) -> dict[str, Any]:
    return {
        "includes_raw": True,
        "includes_waw": True,
        "includes_war": True,
        "temp_hazard_tags": bool(getattr(spec, "use_temp_deps", True)),
        "read_after_read": False,
        "latency": {"raw": 1, "waw": 1, "war": 0, "temp": 1, "default": 1},
    }


def parse_list(s: str) -> list[str]:
    return [x.strip() for x in s.split(",") if x.strip()]


def parse_int_list(s: str) -> list[int]:
    items: list[int] = []
    for token in parse_list(s):
        if ":" in token:
            parts = [p for p in token.split(":") if p]
            if len(parts) < 2:
                continue
            start = int(parts[0])
            end = int(parts[1])
            step = int(parts[2]) if len(parts) > 2 else 1
            if step == 0:
                continue
            if end < start:
                rng = range(start, end - 1, -abs(step))
            else:
                rng = range(start, end + 1, abs(step))
            items.extend(list(rng))
        else:
            items.append(int(token))
    # preserve order, drop dups
    seen: set[int] = set()
    out: list[int] = []
    for v in items:
        if v in seen:
            continue
        seen.add(v)
        out.append(v)
    return out


def parse_bool_list(s: str) -> list[bool]:
    return [bool(int(x)) for x in parse_list(s)]


def parse_float_list(s: str) -> list[float]:
    items: list[float] = []
    for token in parse_list(s):
        if ":" in token:
            parts = [p for p in token.split(":") if p]
            if len(parts) < 2:
                continue
            start = float(parts[0])
            end = float(parts[1])
            step = float(parts[2]) if len(parts) > 2 else 1.0
            if step == 0:
                continue
            if end < start:
                rng = []
                val = start
                while val >= end:
                    rng.append(val)
                    val -= abs(step)
            else:
                rng = []
                val = start
                while val <= end:
                    rng.append(val)
                    val += abs(step)
            items.extend(rng)
        else:
            try:
                items.append(float(token))
            except ValueError:
                continue
    # preserve order, drop dups (by exact value)
    seen: set[float] = set()
    out: list[float] = []
    for v in items:
        if v in seen:
            continue
        seen.add(v)
        out.append(v)
    return out


def parse_int_or_none_list(s: str) -> list[int | None]:
    out: list[int | None] = []
    for token in parse_list(s):
        t = token.strip().lower()
        if t in {"none", "null"}:
            out.append(None)
            continue
        try:
            out.append(int(token))
        except ValueError:
            continue
    return out


def parse_caps_override(s: str, *, defaults: dict[str, int]) -> dict[str, int] | None:
    if not s:
        return None
    caps = dict(defaults)
    for token in parse_list(s):
        if ":" in token:
            key, val = token.split(":", 1)
        elif "=" in token:
            key, val = token.split("=", 1)
        else:
            continue
        key = key.strip()
        if key not in defaults:
            continue
        try:
            caps[key] = int(val.strip())
        except ValueError:
            continue
    return caps


def parse_hazard_set(s: str) -> set[str]:
    if not s:
        return set()
    token = s.strip().lower()
    if token in {"none", "null", "{}"}:
        return set()
    if token == "all":
        return {"raw", "waw", "war", "temp"}
    return set(parse_list(s))


def parse_round_sets(s: str) -> list[tuple[int, ...]]:
    out: list[tuple[int, ...]] = []
    for block in s.split("|"):
        block = block.strip()
        if not block:
            continue
        if block.lower() in {"none", "null", "{}"}:
            out.append(tuple())
            continue
        out.append(tuple(parse_int_list(block)))
    return out


def parse_round_maps(s: str) -> list[dict[int, int]]:
    out: list[dict[int, int]] = []
    for block in s.split("|"):
        block = block.strip()
        if not block or block.lower() in {"none", "null", "{}"}:
            out.append({})
            continue
        mapping: dict[int, int] = {}
        for token in parse_list(block):
            if ":" not in token:
                continue
            key, value = token.split(":", 1)
            try:
                mapping[int(key)] = int(value)
            except ValueError:
                continue
        out.append(mapping)
    return out


def parse_selection_by_round(s: str) -> list[dict[int, str]]:
    """
    Parse per-round selection overrides.
      - "none" -> {}
      - "11,12,13,14=bitmask" -> {11: "bitmask", ...}
      - "11-14=mask_precompute" -> same using range syntax
    Multiple options separated by "|".
    """
    out: list[dict[int, str]] = []
    for block in s.split("|"):
        block = block.strip()
        if not block:
            continue
        if block in {"none", "null", "{}"}:
            out.append({})
            continue
        if "=" not in block:
            continue
        rounds_part, mode = block.split("=", 1)
        rounds_part = rounds_part.replace("-", ":")
        rounds = parse_int_list(rounds_part)
        mapping = {r: mode for r in rounds}
        out.append(mapping)
    return out


def parse_round_sets_or_none(s: str) -> list[tuple[int, ...] | None]:
    """
    Like parse_round_sets, but allows an explicit None token.

    Examples:
      - "none|4|4,15" -> [None, (4,), (4,15)]
    """
    out: list[tuple[int, ...] | None] = []
    for block in s.split("|"):
        block = block.strip()
        if not block:
            continue
        if block.lower() in {"none", "null"}:
            out.append(None)
            continue
        out.append(tuple(parse_int_list(block)))
    return out


def parse_partial_cache(s: str) -> list[tuple[dict[int, int], dict[int, int]]]:
    """
    Parse partial-cache choices. Tokens:
      - "none" -> empty dicts
      - "x8"/"x16"/"x24"/"x32" -> canonical depths for rounds 11-14 with cached_round_x set to X
    """
    out: list[tuple[dict[int, int], dict[int, int]]] = []
    for token in parse_list(s):
        if token == "none":
            out.append(({}, {}))
            continue
        if token.startswith("x"):
            try:
                x_val = int(token[1:])
            except ValueError:
                continue
            depth = {11: 0, 12: 1, 13: 2, 14: 3}
            cached_x = {r: x_val for r in depth.keys()}
            out.append((depth, cached_x))
    return out


def make_presets() -> dict[str, tuple[int, ...]]:
    return {
        "top4": (0, 1, 2, 3, 11, 12, 13, 14),
        "skip_r3": (0, 1, 2, 11, 12, 13, 14),
        "skip_r3_r13": (0, 1, 2, 11, 12, 14),
        "loadbound": (0, 1, 2, 11, 12, 13),
    }


def _count_ops(ops) -> dict[str, int]:
    counts = {k: 0 for k in CAPS}
    for op in ops:
        if op.engine == "debug":
            continue
        counts[op.engine] = counts.get(op.engine, 0) + 1
    return counts


def _op_cost(op) -> int:
    if op.engine == "alu" and isinstance(op.slot, tuple) and op.slot and op.slot[0] == "alu_vec":
        return VLEN
    return 1


def _fast_bundle_precheck(ops, *, caps: dict[str, int] | None = None) -> dict[str, Any]:
    """
    Fast feasibility estimate for bundled closure.

    Returns:
      - quick_cycles: cycle count from a deterministic ready-list simulation
      - lb: per-engine throughput lower bound
      - critical_path: dep-only latency lower bound
      - starvation_ratio: cycles with no issuable work while unscheduled ops remain
      - max_idle_ratio: max engine idle ratio in quick schedule
      - predicted_gap: estimated bundle-lb gap
    """
    if caps is None:
        caps = CAPS

    n = len(ops)
    if n == 0:
        return {
            "quick_cycles": 0,
            "lb": 0,
            "critical_path": 0,
            "starvation_ratio": 0.0,
            "max_idle_ratio": 0.0,
            "predicted_gap": 0,
        }

    counts = _count_ops(ops)
    lb = lower_bound_cycles(counts, caps=caps)

    deps, children = _sched_build_deps(ops)
    indeg = [len(d) for d in deps]
    earliest = [0] * n
    cp = [0] * n

    ready_by_engine: dict[str, list[int]] = defaultdict(list)
    unscheduled = set(range(n))
    for i in range(n):
        if indeg[i] == 0:
            ready_by_engine[ops[i].engine].append(i)

    engine_used = {e: 0 for e in caps}
    starvation_cycles = 0
    cycle = 0
    max_cycles = max(1, lb * 6)

    def _sort_key(i: int) -> tuple[int, int]:
        return (cp[i], len(children[i]))

    while unscheduled and cycle < max_cycles:
        issued: list[int] = []
        for eng, cap in caps.items():
            if cap <= 0:
                continue
            ready = [i for i in ready_by_engine.get(eng, []) if i in unscheduled and earliest[i] <= cycle]
            if not ready:
                continue
            ready.sort(key=_sort_key, reverse=True)
            used = 0
            for i in ready:
                cost = _op_cost(ops[i])
                if used + cost > cap:
                    continue
                used += cost
                issued.append(i)
            engine_used[eng] += used

        if not issued:
            starvation_cycles += 1
            cycle += 1
            continue

        for i in issued:
            if i not in unscheduled:
                continue
            unscheduled.remove(i)
            if i in ready_by_engine.get(ops[i].engine, []):
                ready_by_engine[ops[i].engine].remove(i)
            for c, lat in children[i]:
                indeg[c] -= 1
                earliest[c] = max(earliest[c], cycle + lat)
                cp[c] = max(cp[c], cp[i] + lat)
                if indeg[c] == 0:
                    ready_by_engine[ops[c].engine].append(c)
        cycle += 1

    quick_cycles = cycle if not unscheduled else max_cycles + len(unscheduled) // max(1, sum(caps.values()))
    critical_path = max(cp) + 1 if cp else 0
    starvation_ratio = (starvation_cycles / quick_cycles) if quick_cycles else 0.0
    max_idle_ratio = 0.0
    for eng, cap in caps.items():
        denom = quick_cycles * cap
        if denom <= 0:
            continue
        util = engine_used.get(eng, 0) / denom
        max_idle_ratio = max(max_idle_ratio, max(0.0, 1.0 - util))
    predicted_gap = max(quick_cycles - lb, critical_path - lb)
    return {
        "quick_cycles": int(quick_cycles),
        "lb": int(lb),
        "critical_path": int(critical_path),
        "starvation_ratio": float(starvation_ratio),
        "max_idle_ratio": float(max_idle_ratio),
        "predicted_gap": int(max(0, predicted_gap)),
    }


def lower_bound_cycles(counts: dict[str, int], *, caps: dict[str, int] | None = None) -> int:
    if caps is None:
        caps = CAPS
    lb = 0
    for eng, cap in caps.items():
        total = counts.get(eng, 0)
        if total:
            lb = max(lb, math.ceil(total / cap))
    return lb


def bundle_cycles(spec) -> int:
    instrs = build_base_instrs(spec)
    cycles = 0
    for bundle in instrs:
        if any(engine != "debug" and bundle.get(engine) for engine in bundle):
            cycles += 1
    return cycles


def _sorted_list(values: list[int]) -> list[int]:
    return sorted(values)


def _compute_parity_hash(spec, *, sched_seed: int, sched_jitter: float, sched_restarts: int) -> dict[str, Any]:
    from scripts.export_doppler_energy import _build_deps

    ops = build_final_ops(spec)
    reads_list, writes_list, deps = _build_deps(ops)
    baseline_spec = replace(
        spec,
        sched_seed=sched_seed,
        sched_jitter=sched_jitter,
        sched_restarts=sched_restarts,
    )
    baseline_instrs = build_base_instrs(baseline_spec)
    bundle_count = len(baseline_instrs)
    baseline_cycles = sum(
        1
        for bundle in baseline_instrs
        if any(engine != "debug" and bundle.get(engine) for engine in bundle)
    )
    tasks_for_hash = []
    for i, op in enumerate(ops):
        tasks_for_hash.append(
            {
                "engine": op.engine,
                "reads": _sorted_list(reads_list[i]),
                "writes": _sorted_list(writes_list[i]),
                "deps": _sorted_list(deps[i]),
            }
        )
    caps_sorted = {k: CAPS[k] for k in sorted(CAPS)}
    dependency_model = dependency_model_for_spec(spec)
    hash_payload = {
        "caps": caps_sorted,
        "tasks": tasks_for_hash,
        "dependencyModel": dependency_model,
        "bundleCount": bundle_count,
    }
    digest = hashlib.sha256(
        json.dumps(hash_payload, separators=(",", ":"), sort_keys=True).encode("utf-8")
    ).hexdigest()
    return {
        "dag_hash": digest,
        "bundle_count": bundle_count,
        "baseline_cycles": baseline_cycles,
        "dependency_model": dependency_model,
    }


def _constraint_energy(spec) -> tuple[float, list[str]]:
    violations: list[str] = []

    if getattr(spec, "hash_variant", "direct") == "prog":
        prog = getattr(spec, "hash_prog", None)
        prog_variant = str(getattr(spec, "hash_prog_variant", "none") or "none")
        if not prog and prog_variant in {"none", "null", ""}:
            violations.append("hash_variant=prog requires hash_prog or hash_prog_variant")
            return float("inf"), violations

    try:
        build_layout(spec, ScratchAlloc())
    except RuntimeError as exc:
        violations.append(str(exc))
        return float("inf"), violations

    depth4_rounds = getattr(spec, "depth4_rounds", 0)
    depth4_cached_rounds = tuple(getattr(spec, "depth4_cached_rounds", ()))
    if depth4_rounds != len(depth4_cached_rounds):
        violations.append(
            f"depth4_rounds mismatch: {depth4_rounds} != len(depth4_cached_rounds) {len(depth4_cached_rounds)}"
        )
        return float("inf"), violations
    if depth4_rounds == 0 and depth4_cached_rounds:
        violations.append("depth4_cached_rounds must be empty when depth4_rounds == 0")
        return float("inf"), violations
    if depth4_rounds > 0:
        # For the frozen 16-round workload (height=10, reset at r=10), the only
        # depth-4 rounds are r=4 (pre-reset) and r=15 (post-reset).
        allowed = {4, 15}
        if any(r not in allowed for r in depth4_cached_rounds):
            violations.append(
                f"depth4_cached_rounds must be subset of {tuple(sorted(allowed))} in safe mode"
            )
            return float("inf"), violations
    if depth4_rounds == 0 and getattr(spec, "x4", 0) != 0:
        violations.append("x4 must be 0 when depth4_rounds == 0")
        return float("inf"), violations

    if getattr(spec, "x4", 0) > spec.vectors:
        violations.append(f"x4 exceeds vectors: {spec.x4} > {spec.vectors}")
        return float("inf"), violations
    if getattr(spec, "x5", 0) > spec.vectors:
        violations.append(f"x5 exceeds vectors: {spec.x5} > {spec.vectors}")
        return float("inf"), violations

    for round_id, depth in getattr(spec, "cached_round_depth", {}).items():
        if round_id not in CANONICAL_DEPTH:
            violations.append(f"cached_round_depth round not canonical: {round_id}")
            return float("inf"), violations
        if depth != CANONICAL_DEPTH[round_id]:
            violations.append(
                f"cached_round_depth invalid: round {round_id} depth {depth} != {CANONICAL_DEPTH[round_id]}"
            )
            return float("inf"), violations
        if depth >= 4:
            violations.append(f"cached_round_depth depth >= 4 invalid: {round_id}:{depth}")
            return float("inf"), violations

    cached_round_aliases = getattr(spec, "cached_round_aliases", {})
    for alias_round, depth in cached_round_aliases.items():
        if not isinstance(depth, int):
            violations.append("cached_round_aliases value not int")
            return float("inf"), violations
        if depth not in {0, 1, 2, 3}:
            violations.append(f"cached_round_aliases depth invalid: {alias_round}:{depth}")
            return float("inf"), violations

    cached_rounds = set(getattr(spec, "base_cached_rounds", ()))
    cached_rounds |= set(getattr(spec, "cached_round_depth", {}).keys())
    cached_rounds |= set(cached_round_aliases.keys())
    for round_id, x_val in getattr(spec, "cached_round_x", {}).items():
        if round_id not in CANONICAL_DEPTH:
            violations.append(f"cached_round_x round not canonical: {round_id}")
            return float("inf"), violations
        if round_id not in cached_rounds:
            violations.append(f"cached_round_x for non-cached round: {round_id}")
            return float("inf"), violations
        if x_val < 0 or x_val > spec.vectors:
            violations.append(f"cached_round_x out of range: {round_id}:{x_val}")
            return float("inf"), violations

    cached_nodes = getattr(spec, "cached_nodes", None)
    if cached_nodes is not None:
        max_depth = 0
        for round_id in getattr(spec, "base_cached_rounds", ()):
            if round_id in CANONICAL_DEPTH:
                max_depth = max(max_depth, CANONICAL_DEPTH[round_id])
        for depth in getattr(spec, "cached_round_depth", {}).values():
            if not isinstance(depth, int):
                violations.append("cached_round_depth value not int")
                return float("inf"), violations
            max_depth = max(max_depth, depth)
        for depth in cached_round_aliases.values():
            max_depth = max(max_depth, depth)
        if depth4_rounds and getattr(spec, "x4", 0) > 0:
            max_depth = max(max_depth, 4)
        if getattr(spec, "x5", 0) > 0:
            max_depth = max(max_depth, 5)
        required = MIN_CACHED_NODES.get(max_depth, 1)
        if cached_nodes < required:
            violations.append(f"cached_nodes {cached_nodes} < required {required} for depth {max_depth}")
            return float("inf"), violations

    penalty = 0.0
    selection_mode = getattr(spec, "selection_mode", None)
    if selection_mode is None:
        selection_mode = "bitmask" if getattr(spec, "use_bitmask_selection", False) else "eq"
    extra_vecs = getattr(spec, "extra_vecs", 0)
    uses_depth4 = bool(depth4_rounds and getattr(spec, "x4", 0) > 0)
    if selection_mode == "mask_precompute" and uses_depth4 and extra_vecs < 4:
        penalty += 3.0
        violations.append("soft: mask_precompute with extra_vecs < 4 (depth4)")
    if selection_mode == "mask_precompute" and not getattr(spec, "idx_shifted", False):
        penalty += 1.0
        violations.append("soft: mask_precompute with idx_shifted=0")
    if selection_mode in {"bitmask", "bitmask_valu"} and extra_vecs < 3:
        penalty += 1.0
        violations.append("soft: bitmask with extra_vecs < 3")

    vector_block = getattr(spec, "vector_block", 0)
    if vector_block and spec.vectors % vector_block != 0:
        penalty += 0.5
        violations.append("soft: vector_block does not divide vectors")

    for round_id, mode in getattr(spec, "selection_mode_by_round", {}).items():
        if mode not in {"eq", "mask", "bitmask", "bitmask_valu", "mask_precompute"}:
            penalty += 1.0
            violations.append(f"soft: selection_mode_by_round invalid mode {mode} at round {round_id}")
            break
        if mode in {"mask", "bitmask", "bitmask_valu", "mask_precompute"} and selection_mode == "eq":
            penalty += 1.0
            violations.append("soft: selection_mode_by_round requires extras but global selection_mode=eq")
            break
        if mode in {"bitmask", "bitmask_valu"} and extra_vecs < 3:
            penalty += 1.0
            violations.append("soft: selection_mode_by_round bitmask with extra_vecs < 3")
            break
        if mode == "mask_precompute" and uses_depth4 and round_id in depth4_cached_rounds and extra_vecs < 4:
            penalty += 1.0
            violations.append("soft: selection_mode_by_round mask_precompute with extra_vecs < 4 (depth4)")
            break
        if mode == "mask_precompute" and not getattr(spec, "idx_shifted", False):
            penalty += 0.5
            violations.append("soft: selection_mode_by_round mask_precompute with idx_shifted=0")
            break

    return penalty, violations


def score_spec(
    spec,
    *,
    target: int,
    penalty: float,
    constraint_threshold: float,
    lambda_cycles: float,
    schedule: bool,
    sched_restarts: int,
    sched_seed: int,
    sched_jitter: float,
    sched_policies: list[str],
    score_mode: str,
    dep_model: dict[str, Any] | None,
    caps: dict[str, int] | None,
    bundle_gap_threshold: int,
) -> dict[str, Any]:
    constraint_penalty, constraint_violations = _constraint_energy(spec)
    if math.isinf(constraint_penalty) or constraint_penalty > constraint_threshold:
        fallback_cycles = max(int(getattr(spec, "total_cycles", 0)), 10_000)
        return {
            "energy": constraint_penalty + lambda_cycles * fallback_cycles,
            "cycles": fallback_cycles,
            "lb": 0,
            "counts": {},
            "gap": 0,
            "constraint_penalty": constraint_penalty,
            "constraint_violations": constraint_violations,
            "skipped": True,
        }
    try:
        ops = build_final_ops(spec)
    except (RuntimeError, IndexError, ValueError, KeyError) as exc:
        # Treat invalid specs (e.g., scratch overflow) as high-energy.
        return {
            "energy": float("inf"),
            "cycles": 0,
            "lb": 0,
            "counts": {},
            "gap": 0,
            "error": str(exc),
            "constraint_penalty": constraint_penalty,
            "constraint_violations": constraint_violations,
        }
    counts = _count_ops(ops)
    lb = lower_bound_cycles(counts, caps=caps)
    precheck = _fast_bundle_precheck(ops, caps=caps)
    cycles = lb
    best_policy: str | None = None
    if score_mode == "bundle":
        if bundle_gap_threshold >= 0 and precheck["predicted_gap"] > bundle_gap_threshold:
            return {
                "energy": float("inf"),
                "cycles": 0,
                "lb": lb,
                "counts": counts,
                "gap": 0,
                "error": (
                    f"bundle precheck rejected: predicted_gap={precheck['predicted_gap']} "
                    f"> threshold={bundle_gap_threshold}"
                ),
                "constraint_penalty": constraint_penalty,
                "constraint_violations": constraint_violations,
                "policy": None,
                "precheck": precheck,
            }
        if schedule:
            spec_for_bundle = replace(
                spec,
                sched_seed=sched_seed,
                sched_jitter=sched_jitter,
                sched_restarts=sched_restarts,
            )
            try:
                cycles = bundle_cycles(spec_for_bundle)
            except (RuntimeError, ValueError, IndexError, KeyError) as exc:
                return {
                    "energy": float("inf"),
                    "cycles": 0,
                    "lb": lb,
                    "counts": counts,
                    "gap": 0,
                    "error": str(exc),
                    "constraint_penalty": constraint_penalty,
                    "constraint_violations": constraint_violations,
                    "policy": None,
                    "precheck": precheck,
                }
    elif score_mode == "graph":
        if schedule:
            best_cycles: int | None = None
            last_error: str | None = None
            for policy in sched_policies:
                try:
                    candidate = schedule_graph_with_restarts(
                        ops,
                        restarts=sched_restarts,
                        seed=sched_seed,
                        jitter=sched_jitter,
                        policy=policy,
                        dep_model=dep_model,
                        caps=caps,
                    )
                except (RuntimeError, ValueError, IndexError, KeyError) as exc:
                    last_error = str(exc)
                    continue
                if best_cycles is None or candidate < best_cycles:
                    best_cycles = candidate
                    best_policy = policy
            if best_cycles is None:
                return {
                    "energy": float("inf"),
                    "cycles": 0,
                    "lb": lb,
                    "counts": counts,
                    "gap": 0,
                    "error": last_error or "graph scheduling failed for all policies",
                    "constraint_penalty": constraint_penalty,
                    "constraint_violations": constraint_violations,
                    "policy": None,
                    "precheck": precheck,
                }
            cycles = best_cycles
    elif score_mode == "lb":
        cycles = lb
    else:
        raise ValueError(f"unknown score_mode {score_mode!r}")
    gap = max(0, lb - target) if target > 0 else 0
    energy = constraint_penalty + lambda_cycles * cycles + penalty * gap
    return {
        "energy": energy,
        "cycles": cycles,
        "lb": lb,
        "counts": counts,
        "gap": gap,
        "constraint_penalty": constraint_penalty,
        "constraint_violations": constraint_violations,
        "policy": best_policy,
        "precheck": precheck,
    }


def mutate_spec(
    spec,
    rnd: random.Random,
    domains: dict[str, list[Any]],
    *,
    key: str | None = None,
    swap_cfg: dict[str, Any] | None = None,
):
    if not domains:
        return spec
    if key is None:
        key = rnd.choice(list(domains.keys()))
    choices = domains[key]
    if not choices:
        return spec
    value = rnd.choice(choices)
    if key == "selection_mode":
        return replace(
            spec,
            selection_mode=value,
            use_bitmask_selection=(value == "bitmask"),
        )
    if key == "base_cached_rounds":
        return replace(spec, base_cached_rounds=tuple(value))
    if key == "depth4_rounds":
        return replace(spec, depth4_rounds=len(value), depth4_cached_rounds=tuple(value))
    if key == "cached_round_x":
        return replace(spec, cached_round_x=dict(value))
    if key == "cached_round_depth":
        return replace(spec, cached_round_depth=dict(value))
    if key == "selection_by_round":
        return replace(spec, selection_mode_by_round=value)
    if key == "partial_cache":
        depth_map, x_map = value
        return replace(spec, cached_round_depth=depth_map, cached_round_x=x_map)
    if key == "offload_budget_swaps":
        if not bool(value):
            return replace(spec, offload_budget_swaps={})
        cfg = swap_cfg or {}
        return _mutate_offload_budget_swaps(
            spec,
            rnd,
            categories=tuple(cfg.get("categories", ())),
            span=int(cfg.get("span", 512)),
            max_swaps_per_cat=int(cfg.get("max_swaps_per_cat", 1)),
        )
    return replace(spec, **{key: value})


def mutate_spec_multi(
    spec,
    rnd: random.Random,
    domains: dict[str, list[Any]],
    *,
    count: int,
    swap_cfg: dict[str, Any] | None = None,
):
    if count <= 1:
        return mutate_spec(spec, rnd, domains, swap_cfg=swap_cfg)
    keys = list(domains.keys())
    if not keys:
        return spec
    if count >= len(keys):
        chosen = keys[:]
        rnd.shuffle(chosen)
    else:
        chosen = rnd.sample(keys, count)
    out = spec
    for key in chosen:
        out = mutate_spec(out, rnd, domains, key=key, swap_cfg=swap_cfg)
    return out


def spec_to_json(spec) -> dict[str, Any]:
    return dict(spec.__dict__)


def _spec_from_dict(seed: dict[str, Any]) -> SpecBase:
    field_names = {f.name for f in fields(SpecBase)}
    tuple_fields = {f.name for f in fields(SpecBase) if str(f.type).startswith("tuple")}
    int_key_fields = {"cached_round_depth", "cached_round_x", "cached_round_aliases", "selection_mode_by_round"}
    int_value_fields = {"cached_round_depth", "cached_round_x", "cached_round_aliases"}
    overrides: dict[str, Any] = {}
    for key, value in seed.items():
        if key not in field_names:
            continue
        if key == "offload_budget_swaps":
            overrides[key] = _normalize_offload_budget_swaps(value)
            continue
        if key in tuple_fields and isinstance(value, list):
            overrides[key] = tuple(value)
            continue
        if key in int_key_fields and isinstance(value, dict):
            fixed: dict[int, Any] = {}
            for raw_key, raw_val in value.items():
                try:
                    int_key = int(raw_key)
                except (TypeError, ValueError):
                    continue
                if key in int_value_fields:
                    try:
                        fixed[int_key] = int(raw_val)
                    except (TypeError, ValueError):
                        continue
                else:
                    fixed[int_key] = raw_val
            overrides[key] = fixed
            continue
        else:
            overrides[key] = value
    return replace(SPEC_BASE, **overrides)


def _enforce_frozen_workload(spec: SpecBase, *, mode: str) -> None:
    if mode != "parity":
        return
    frozen_fields = ("rounds", "vectors", "vlen")
    mismatches: list[str] = []
    for field in frozen_fields:
        want = getattr(SPEC_BASE, field)
        got = getattr(spec, field)
        if got != want:
            mismatches.append(f"{field}={got} (expected {want})")
    if mismatches:
        raise SystemExit(
            "Parity mode requires frozen workload fields; "
            + ", ".join(mismatches)
        )


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--mode", type=str, default="parity", choices=["parity", "relaxed"])
    ap.add_argument("--steps", type=int, default=2000)
    ap.add_argument("--seed", type=int, default=0)
    ap.add_argument("--report-every", type=int, default=50)
    ap.add_argument("--schedule-every", type=int, default=10,
                    help="schedule every N steps (0 = always schedule)")
    ap.add_argument("--bundle-gap-threshold", type=int, default=220,
                    help="Skip bundled scheduling if fast precheck predicts LB->bundle gap above this value (-1 disables).")
    ap.add_argument("--unscheduled-score", type=str, default="auto",
                    choices=["auto", "lb", "skip"],
                    help="behavior on unscheduled steps (auto=skip for bundle, lb otherwise)")
    ap.add_argument("--score-mode", type=str, default="bundle",
                    choices=["graph", "bundle", "lb"],
                    help="How to score cycles: graph scheduler, bundle count, or per-engine LB.")
    ap.add_argument("--hazards", type=str, default="raw,waw,war,temp",
                    help="Dependency hazards to include in graph/lb scoring: raw,waw,war,temp (comma-separated).")
    ap.add_argument("--latency-raw", type=int, default=1)
    ap.add_argument("--latency-waw", type=int, default=1)
    ap.add_argument("--latency-war", type=int, default=0)
    ap.add_argument("--latency-temp", type=int, default=1)
    ap.add_argument("--latency-default", type=int, default=1)
    ap.add_argument("--caps-override", type=str, default="",
                    help="Override engine caps for graph/lb scoring (e.g., 'alu:16,valu:8,load:3,store:3,flow:2').")
    ap.add_argument("--caps-scale", type=float, default=1.0,
                    help="Scale SLOT_LIMITS caps for graph/lb scoring (ignored if caps-override is set).")
    ap.add_argument("--target", type=int, default=0,
                    help="target cycles; adds penalty if per-engine LB exceeds this")
    ap.add_argument("--penalty", type=float, default=100.0)
    ap.add_argument("--constraint-threshold", type=float, default=10.0,
                    help="skip DAG/schedule when constraint penalty exceeds this")
    ap.add_argument("--lambda-cycles", type=float, default=1.0,
                    help="weight for cycles term in total energy")
    ap.add_argument("--temp-start", type=float, default=50.0)
    ap.add_argument("--temp-decay", type=float, default=0.995)
    ap.add_argument("--mutate-count", type=int, default=1,
                    help="number of knobs to mutate per step (>=1)")
    ap.add_argument("--out", type=str, default="")
    ap.add_argument("--seed-spec", type=str, default="",
                    help="JSON path for a seed spec (accepts {spec: {...}} or spec dict).")

    ap.add_argument("--selection", type=str, default="eq,bitmask,bitmask_valu,mask,mask_precompute")
    ap.add_argument("--idx-shifted", type=str, default="0,1")
    ap.add_argument("--assume-zero-indices", type=str, default="0,1")
    ap.add_argument("--vector-block", type=str, default="0,4,8,16,32")
    ap.add_argument("--extra-vecs", type=str, default="0,1,2,3,4")
    ap.add_argument("--reset-on-valu", type=str, default="0,1")
    ap.add_argument("--shifts-on-valu", type=str, default="0,1")
    ap.add_argument("--use-temp-deps", type=str, default="0,1",
                    help="include temp hazards in the dependency model (0/1 domain)")
    ap.add_argument("--use-temp-deps-extras", type=str, default="0,1",
                    help="include extra temp hazard tags for shared selection scratch (0/1 domain)")
    ap.add_argument("--emit-order", type=str, default="auto,vector_major,round_major,block",
                    help="op emission order: auto|vector_major|round_major|block")
    ap.add_argument("--temp-rename-mode", type=str, default="off,round,vec,window,op",
                    help="temp hazard renaming mode: off|round|vec|window|op")
    ap.add_argument("--temp-rename-window", type=str, default="4,8,16",
                    help="window size for temp-rename-mode=window")
    ap.add_argument("--cached-nodes", type=str, default="none,7,15,31,63")
    ap.add_argument("--base-cached-presets", type=str, default="top4,skip_r3,skip_r3_r13,loadbound")
    ap.add_argument("--depth4-rounds", type=str, default="4|15|4,15|none")
    ap.add_argument("--x4", type=str, default="0,8,12,15,24,32")
    ap.add_argument("--selection-by-round", type=str, default="none|11-14=bitmask|11-14=mask_precompute",
                    help="per-round selection overrides, e.g. '11-14=bitmask|none'")
    ap.add_argument("--cached-round-x", type=str, default="",
                    help="Per-round partial caching (e.g. '11:16,12:16|11:8,12:8').")
    ap.add_argument("--cached-round-depth", type=str, default="",
                    help="Override per-round cache depth (e.g. '11:2,12:2').")
    ap.add_argument("--partial-cache", type=str, default="none,x8,x16,x24,x32",
                    help="partial cache choices: none|x8|x16|x24|x32 (applies to rounds 11-14)")
    ap.add_argument("--offload-op1", type=str, default="0,200,400,800,1200,1600")
    ap.add_argument("--offload-mode", type=str, default="prefix,budgeted",
                    help="offload mode: prefix|budgeted (comma-separated domain)")
    ap.add_argument("--offload-alu-vec", type=str, default="0,1",
                    help="emit offloaded vector ops as ALU_VEC pseudo ops (0/1)")
    ap.add_argument("--offload-budget-hash-shift", type=str, default="0,12,48,96,192,384,768,1536",
                    help="budgeted offload cap for hash shift ops (vector ops count)")
    ap.add_argument("--offload-budget-hash-op1", type=str, default="0,12,48,96,192,384,768,1536",
                    help="budgeted offload cap for hash op1 ops (vector ops count)")
    ap.add_argument("--offload-budget-hash-op2", type=str, default="0,12,48,96,192,384,768,1536",
                    help="budgeted offload cap for hash op2 ops (vector ops count)")
    ap.add_argument("--offload-budget-parity", type=str, default="0,32,64,128,256,384,448",
                    help="budgeted offload cap for parity ops (vector ops count)")
    ap.add_argument("--offload-budget-node-xor", type=str, default="0,32,64,128,256,384,512",
                    help="budgeted offload cap for node_xor ops (vector ops count)")
    ap.add_argument("--offload-budget-swaps", type=str, default="0,1",
                    help="mutate offload_budget_swaps (0 disables, 1 enables)")
    ap.add_argument("--offload-swap-cats", type=str, default="parity,node_xor,hash_op2,hash_shift,hash_op1",
                    help="categories eligible for offload_budget_swaps mutation")
    ap.add_argument("--offload-swap-span", type=int, default=512,
                    help="destination window size for generated category-local swap positions")
    ap.add_argument("--offload-swap-max-per-cat", type=int, default=2,
                    help="cap on retained swap pairs per category during mutation")
    ap.add_argument("--offload-hash-op1", type=str, default="0,1")
    ap.add_argument("--offload-hash-shift", type=str, default="0,1")
    ap.add_argument("--offload-hash-op2", type=str, default="0,1")
    ap.add_argument("--offload-parity", type=str, default="0,1")
    ap.add_argument("--offload-node-xor", type=str, default="0,1")
    ap.add_argument("--node-ptr-incremental", type=str, default="0,1")
    ap.add_argument("--valu-select", type=str, default="0,1")
    ap.add_argument("--valu-select-precompute-diffs", type=str, default="0,1",
                    help="precompute node diffs for valu_select (costs scratch)")
    ap.add_argument("--valu-select-rounds", type=str, default="none|4|15|4,15",
                    help="round whitelist for valu_select lowering (none=all rounds)")
    ap.add_argument("--ptr-setup-engine", type=str, default="flow,alu")
    ap.add_argument("--setup-style", type=str, default="packed,inline")
    ap.add_argument("--hash-variant", type=str, default="direct,ir,prog",
                    help="hash implementation variant: direct|ir|prog (comma-separated domain)")
    ap.add_argument("--hash-prog-variant", type=str, default="none,baseline,swap_xor,tmp_xor_const,tmp_op1,pingpong",
                    help="hash program preset when hash_variant=prog")
    ap.add_argument("--hash-bitwise-style", type=str, default="inplace,tmp_op1",
                    help="hash lowering for bitwise stages: inplace|tmp_op1 (comma-separated domain)")
    ap.add_argument("--hash-xor-style", type=str, default="baseline,swap,tmp_xor_const",
                    help="xor-stage lowering: baseline|swap|tmp_xor_const (comma-separated domain)")
    ap.add_argument("--hash-linear-style", type=str, default="muladd,shift_add",
                    help="linear-stage lowering: muladd|shift_add (comma-separated domain)")
    ap.add_argument("--fuse-stages", type=str, default="0,1",
                    help="enable hash stage fusion where legal (0/1)")
    ap.add_argument("--valu-select-leaf-pairs", type=str, default="0,1",
                    help="enable leaf-only VALU selection lowering (0/1)")

    ap.add_argument("--sched-restarts", type=int, default=10)
    ap.add_argument("--sched-jitter", type=float, default=0.4)
    ap.add_argument("--sched-policy", type=str, default="mix")
    ap.add_argument("--sched-compact-domain", type=str, default="",
                    help="Mutation domain for sched_compact (0,1).")
    ap.add_argument("--mutate-sched", action="store_true",
                    help="Include sched_seed/jitter/restarts in the mutation domain.")
    ap.add_argument("--sched-seed-domain", type=str, default="",
                    help="Mutation domain for sched_seed (e.g., '0:63' or '0,8,16').")
    ap.add_argument("--sched-jitter-domain", type=str, default="",
                    help="Mutation domain for sched_jitter (e.g., '0,0.05,0.1').")
    ap.add_argument("--sched-restarts-domain", type=str, default="",
                    help="Mutation domain for sched_restarts (e.g., '1,2,4,8,16,32').")
    ap.add_argument("--sched-policy-domain", type=str, default="",
                    help="Mutation domain for spec.sched_policy in bundle mode (e.g., 'baseline,bottleneck_valu').")
    ap.add_argument("--sched-target-domain", type=str, default="",
                    help="Mutation domain for spec.sched_target_cycles (e.g., 'none,1100,1150,1200').")
    ap.add_argument("--sched-deps-variant", type=str, default="full,nowar,nowaw,nowaw_nowar,waw0,waw0_nowar",
                    help="Dependency suffix family for scheduler policy.")
    ap.add_argument("--sched-repair-passes", type=str, default="0,1,2",
                    help="Deterministic post-schedule repair passes.")
    ap.add_argument("--sched-repair-swap", type=str, default="0,1",
                    help="Enable adjacent swap/pack repair step (0/1).")
    ap.add_argument("--log-file", type=str, default="",
                    help="Optional file to write progress logs.")
    args = ap.parse_args()

    def make_logger(path: str):
        handle = None
        if path:
            handle = open(path, "w", encoding="utf-8")

        def _log(line: str) -> None:
            print(line, flush=True)
            if handle:
                handle.write(line + "\n")
                handle.flush()

        def _close() -> None:
            if handle:
                handle.close()

        return _log, _close

    log, close_log = make_logger(args.log_file)

    sched_policies = parse_list(args.sched_policy)
    if not sched_policies:
        sched_policies = ["mix"]

    if args.mutate_count < 1:
        raise SystemExit("mutate-count must be >= 1")

    unscheduled_score = args.unscheduled_score
    if unscheduled_score == "auto":
        unscheduled_score = "skip" if args.score_mode == "bundle" else "lb"
    if unscheduled_score == "lb" and args.score_mode == "bundle" and args.schedule_every != 0:
        log("warn: unscheduled-score=lb with score_mode=bundle mixes LB and bundle energies")

    hazard_set = parse_hazard_set(args.hazards)
    caps_override = parse_caps_override(args.caps_override, defaults=CAPS)
    if caps_override is None and args.caps_scale != 1.0:
        if args.caps_scale <= 0:
            raise SystemExit("caps-scale must be > 0")
        caps_override = {
            k: max(1, int(math.ceil(v * args.caps_scale))) for k, v in CAPS.items()
        }

    def dep_model_for_args(spec) -> dict[str, Any]:
        base = dependency_model_for_spec(spec)
        base["includes_raw"] = "raw" in hazard_set
        base["includes_waw"] = "waw" in hazard_set
        base["includes_war"] = "war" in hazard_set
        base["temp_hazard_tags"] = (
            "temp" in hazard_set and bool(getattr(spec, "use_temp_deps", True))
        )
        base["latency"] = {
            "raw": args.latency_raw,
            "waw": args.latency_waw,
            "war": args.latency_war,
            "temp": args.latency_temp,
            "default": args.latency_default,
        }
        return base

    sched_seed_domain = parse_int_list(args.sched_seed_domain) if args.sched_seed_domain else []
    sched_jitter_domain = parse_float_list(args.sched_jitter_domain) if args.sched_jitter_domain else []
    sched_restarts_domain = parse_int_list(args.sched_restarts_domain) if args.sched_restarts_domain else []
    sched_policy_domain = parse_list(args.sched_policy_domain) if args.sched_policy_domain else []
    sched_target_domain = parse_int_or_none_list(args.sched_target_domain) if args.sched_target_domain else []
    sched_deps_variant_domain = parse_list(args.sched_deps_variant)
    sched_repair_passes_domain = parse_int_list(args.sched_repair_passes)
    sched_repair_swap_domain = parse_bool_list(args.sched_repair_swap)
    sched_compact_domain = parse_bool_list(args.sched_compact_domain) if args.sched_compact_domain else []
    mutate_sched = bool(
        args.mutate_sched
        or sched_seed_domain
        or sched_jitter_domain
        or sched_restarts_domain
        or sched_policy_domain
        or sched_target_domain
        or sched_compact_domain
    )
    if args.mutate_sched:
        if not sched_seed_domain:
            sched_seed_domain = list(range(0, 64))
        if not sched_jitter_domain:
            sched_jitter_domain = [0.0, 0.05, 0.1]
        if not sched_restarts_domain:
            # Keep default search fast; widen explicitly via --sched-restarts-domain.
            sched_restarts_domain = [1, 2, 4, 8]

    def sched_params_for(spec, *, seed_offset: int = 0) -> tuple[int, int, float]:
        if args.mode == "parity" or mutate_sched:
            return (
                int(getattr(spec, "sched_restarts", 1)),
                int(getattr(spec, "sched_seed", 0)),
                float(getattr(spec, "sched_jitter", 0.0)),
            )
        return (
            args.sched_restarts,
            args.seed + seed_offset,
            args.sched_jitter,
        )

    rnd = random.Random(args.seed)
    presets = make_presets()

    selection_modes = parse_list(args.selection)
    idx_shifted_list = parse_bool_list(args.idx_shifted)
    assume_zero_indices_list = parse_bool_list(args.assume_zero_indices)
    vector_blocks = parse_int_list(args.vector_block)
    extra_vecs_list = parse_int_list(args.extra_vecs)
    reset_on_valu_list = parse_bool_list(args.reset_on_valu)
    shifts_on_valu_list = parse_bool_list(args.shifts_on_valu)
    use_temp_deps_list = parse_bool_list(args.use_temp_deps)
    use_temp_deps_extras_list = parse_bool_list(args.use_temp_deps_extras)
    emit_order_list = parse_list(args.emit_order)
    temp_rename_mode_list = parse_list(args.temp_rename_mode)
    temp_rename_window_list = parse_int_list(args.temp_rename_window)
    hash_variant_list = parse_list(args.hash_variant)
    hash_prog_variant_list = parse_list(args.hash_prog_variant)
    hash_bitwise_style_list = parse_list(args.hash_bitwise_style)
    hash_xor_style_list = parse_list(args.hash_xor_style)
    hash_linear_style_list = parse_list(args.hash_linear_style)
    fuse_stages_list = parse_bool_list(args.fuse_stages)
    valu_select_leaf_pairs_list = parse_bool_list(args.valu_select_leaf_pairs)

    cached_nodes_list: list[int | None] = []
    for item in parse_list(args.cached_nodes):
        if item.lower() in {"none", "null"}:
            cached_nodes_list.append(None)
        else:
            cached_nodes_list.append(int(item))

    base_presets = []
    for name in parse_list(args.base_cached_presets):
        if name not in presets:
            raise SystemExit(f"Unknown preset: {name}")
        base_presets.append(presets[name])

    depth4_sets = parse_round_sets(args.depth4_rounds) if args.depth4_rounds else [tuple()]
    x4_list = parse_int_list(args.x4)
    selection_by_round_list = parse_selection_by_round(args.selection_by_round)
    cached_round_x_list = parse_round_maps(args.cached_round_x) if args.cached_round_x else [{}]
    cached_round_depth_list = parse_round_maps(args.cached_round_depth) if args.cached_round_depth else [{}]
    partial_cache_list = parse_partial_cache(args.partial_cache)
    valu_select_precompute_diffs_list = parse_bool_list(args.valu_select_precompute_diffs)
    valu_select_rounds_list = parse_round_sets_or_none(args.valu_select_rounds)
    offload_budget_swaps_list = parse_bool_list(args.offload_budget_swaps)
    swap_cats_raw = tuple(parse_list(args.offload_swap_cats))
    swap_cats = tuple(cat for cat in swap_cats_raw if cat in OFFLOAD_SWAP_CATEGORIES)
    if swap_cats_raw and not swap_cats:
        raise SystemExit(
            "offload-swap-cats has no valid categories; "
            f"valid: {', '.join(OFFLOAD_SWAP_CATEGORIES)}"
        )
    if args.offload_swap_span < 1:
        raise SystemExit("offload-swap-span must be >= 1")
    if args.offload_swap_max_per_cat < 1:
        raise SystemExit("offload-swap-max-per-cat must be >= 1")
    swap_cfg = {
        "categories": swap_cats,
        "span": args.offload_swap_span,
        "max_swaps_per_cat": args.offload_swap_max_per_cat,
    }

    domains = {
        "selection_mode": selection_modes,
        "idx_shifted": idx_shifted_list,
        "assume_zero_indices": assume_zero_indices_list,
        "vector_block": vector_blocks,
        "extra_vecs": extra_vecs_list,
        "reset_on_valu": reset_on_valu_list,
        "shifts_on_valu": shifts_on_valu_list,
        "use_temp_deps": use_temp_deps_list,
        "use_temp_deps_extras": use_temp_deps_extras_list,
        "emit_order": emit_order_list,
        "temp_rename_mode": temp_rename_mode_list,
        "temp_rename_window": temp_rename_window_list,
        "cached_nodes": cached_nodes_list,
        "base_cached_rounds": base_presets,
        "depth4_rounds": depth4_sets,
        "x4": x4_list,
        "selection_by_round": selection_by_round_list,
        "cached_round_x": cached_round_x_list,
        "cached_round_depth": cached_round_depth_list,
        "partial_cache": partial_cache_list,
        "offload_op1": parse_int_list(args.offload_op1),
        "offload_mode": parse_list(args.offload_mode),
        "offload_alu_vec": parse_bool_list(args.offload_alu_vec),
        "offload_budget_hash_shift": parse_int_list(args.offload_budget_hash_shift),
        "offload_budget_hash_op1": parse_int_list(args.offload_budget_hash_op1),
        "offload_budget_hash_op2": parse_int_list(args.offload_budget_hash_op2),
        "offload_budget_parity": parse_int_list(args.offload_budget_parity),
        "offload_budget_node_xor": parse_int_list(args.offload_budget_node_xor),
        "offload_hash_op1": parse_bool_list(args.offload_hash_op1),
        "offload_hash_shift": parse_bool_list(args.offload_hash_shift),
        "offload_hash_op2": parse_bool_list(args.offload_hash_op2),
        "offload_parity": parse_bool_list(args.offload_parity),
        "offload_node_xor": parse_bool_list(args.offload_node_xor),
        "node_ptr_incremental": parse_bool_list(args.node_ptr_incremental),
        "valu_select": parse_bool_list(args.valu_select),
        "valu_select_precompute_diffs": valu_select_precompute_diffs_list,
        "valu_select_rounds": valu_select_rounds_list,
        "ptr_setup_engine": parse_list(args.ptr_setup_engine),
        "setup_style": parse_list(args.setup_style),
        "hash_variant": hash_variant_list,
        "hash_prog_variant": hash_prog_variant_list,
        "hash_bitwise_style": hash_bitwise_style_list,
        "hash_xor_style": hash_xor_style_list,
        "hash_linear_style": hash_linear_style_list,
        "fuse_stages": fuse_stages_list,
        "valu_select_leaf_pairs": valu_select_leaf_pairs_list,
        "sched_deps_variant": sched_deps_variant_domain,
        "sched_repair_passes": sched_repair_passes_domain,
        "sched_repair_try_swap": sched_repair_swap_domain,
    }
    if any(offload_budget_swaps_list):
        domains["offload_budget_swaps"] = offload_budget_swaps_list
    if mutate_sched:
        if sched_seed_domain:
            domains["sched_seed"] = sched_seed_domain
        if sched_jitter_domain:
            domains["sched_jitter"] = sched_jitter_domain
        if sched_restarts_domain:
            domains["sched_restarts"] = sched_restarts_domain
        if sched_policy_domain:
            domains["sched_policy"] = sched_policy_domain
        if sched_target_domain:
            domains["sched_target_cycles"] = sched_target_domain
        if sched_compact_domain:
            domains["sched_compact"] = sched_compact_domain

    # Avoid wasting mutations on knobs that are effectively frozen (0/1 choice).
    domains = {
        k: v for k, v in domains.items()
        if v and (len(v) > 1 or k == "offload_budget_swaps")
    }

    spec = SPEC_BASE
    if args.seed_spec:
        with open(args.seed_spec, "r", encoding="utf-8") as f:
            payload = json.load(f)
        seed_dict = payload.get("spec", payload)
        spec = _spec_from_dict(seed_dict)
    _enforce_frozen_workload(spec, mode=args.mode)
    best_spec = spec
    sched_restarts, sched_seed, sched_jitter = sched_params_for(spec)
    best_score = score_spec(
        spec,
        target=args.target,
        penalty=args.penalty,
        constraint_threshold=args.constraint_threshold,
        lambda_cycles=args.lambda_cycles,
        schedule=True,
        sched_restarts=sched_restarts,
        sched_seed=sched_seed,
        sched_jitter=sched_jitter,
        sched_policies=sched_policies,
        score_mode=args.score_mode,
        dep_model=dep_model_for_args(spec),
        caps=caps_override,
        bundle_gap_threshold=args.bundle_gap_threshold,
    )
    curr_score = best_score
    temp = args.temp_start

    start_ts = time.time()
    log(f"energy_search: {time.strftime('%Y-%m-%d %H:%M:%S')}")
    log(f"  mode={args.mode} score_mode={args.score_mode} steps={args.steps} seed={args.seed}")
    log(f"  schedule_every={args.schedule_every} unscheduled_score={unscheduled_score}")
    log(f"  mutate_count={args.mutate_count} mutate_sched={mutate_sched}")
    log(f"  mutate_keys={sorted(domains.keys())}")
    if "offload_budget_swaps" in domains:
        log(
            "  offload_swap_cfg="
            f"cats={swap_cfg['categories']} span={swap_cfg['span']} "
            f"max_per_cat={swap_cfg['max_swaps_per_cat']}"
        )
    if mutate_sched:
        log(f"  sched_seed_domain={sched_seed_domain}")
        log(f"  sched_jitter_domain={sched_jitter_domain}")
        log(f"  sched_restarts_domain={sched_restarts_domain}")
        if sched_policy_domain:
            log(f"  sched_policy_domain={sched_policy_domain}")
        if sched_compact_domain:
            log(f"  sched_compact_domain={sched_compact_domain}")
    log(f"  sched_policies={sched_policies} sched_restarts={args.sched_restarts} sched_jitter={args.sched_jitter}")
    log(f"  hazards={sorted(hazard_set)} latency_raw={args.latency_raw} latency_waw={args.latency_waw} "
        f"latency_war={args.latency_war} latency_temp={args.latency_temp} latency_default={args.latency_default}")
    log(
        f"  gate={args.constraint_threshold} bundle_gap_threshold={args.bundle_gap_threshold} "
        f"lambda={args.lambda_cycles} target={args.target} penalty={args.penalty}"
    )
    if args.log_file:
        log(f"  log_file={args.log_file}")

    for step in range(1, args.steps + 1):
        cand = mutate_spec_multi(
            spec,
            rnd,
            domains,
            count=args.mutate_count,
            swap_cfg=swap_cfg,
        )
        do_schedule = args.schedule_every == 0 or (step % args.schedule_every == 0)
        if not do_schedule and unscheduled_score == "skip":
            continue
        cand_restarts, cand_seed, cand_jitter = sched_params_for(cand, seed_offset=step)
        cand_score = score_spec(
            cand,
            target=args.target,
            penalty=args.penalty,
            constraint_threshold=args.constraint_threshold,
            lambda_cycles=args.lambda_cycles,
            schedule=do_schedule,
            sched_restarts=cand_restarts,
            sched_seed=cand_seed,
            sched_jitter=cand_jitter,
            sched_policies=sched_policies,
            score_mode=args.score_mode,
            dep_model=dep_model_for_args(cand),
            caps=caps_override,
            bundle_gap_threshold=args.bundle_gap_threshold,
        )
        delta = cand_score["energy"] - curr_score["energy"]
        accept = delta <= 0
        if not accept and temp > 1e-9:
            prob = math.exp(-delta / temp)
            accept = rnd.random() < prob
        if accept:
            spec = cand
            curr_score = cand_score
        if cand_score["energy"] < best_score["energy"]:
            best_spec = cand
            best_score = cand_score
            log(
                "BEST "
                f"step={step} t={time.time() - start_ts:.1f}s "
                f"energy={best_score['energy']:.1f} cycles={best_score['cycles']} "
                f"lb={best_score['lb']} penalty={best_score['constraint_penalty']} "
                f"skipped={best_score.get('skipped', False)} policy={best_score.get('policy')}"
            )
            log(f"  spec={spec_to_json(best_spec)}")
        if step % args.report_every == 0:
            log(
                f"[{step:5d}] t={time.time() - start_ts:.1f}s "
                f"energy={curr_score['energy']:.1f} "
                f"cycles={curr_score['cycles']} lb={curr_score['lb']} "
                f"best={best_score['energy']:.1f}"
            )
        temp *= args.temp_decay

    summary_hash = None
    if args.mode == "parity":
        try:
            summary_hash = _compute_parity_hash(
                best_spec,
                sched_seed=getattr(best_spec, "sched_seed", 0),
                sched_jitter=getattr(best_spec, "sched_jitter", 0.0),
                sched_restarts=getattr(best_spec, "sched_restarts", 1),
            )
        except Exception as exc:
            summary_hash = {"error": str(exc)}

    log("best_score: " + json.dumps(best_score, sort_keys=True))
    log("best_spec: " + json.dumps(spec_to_json(best_spec), sort_keys=True))
    log("summary:")
    log(f"  mode: {args.mode}")
    log(f"  score_mode: {args.score_mode}")
    log(f"  schedule_every: {args.schedule_every} (unscheduled_score={unscheduled_score})")
    log(f"  mutate_count: {args.mutate_count} mutate_sched: {mutate_sched}")
    log(f"  sched_policies: {sched_policies} (tie-break: earliest policy)")
    log(f"  engine_order: {list(CAPS.keys())}")
    caps_label = "SLOT_LIMITS" if caps_override is None else f"override {caps_override}"
    log(f"  caps_source: {caps_label}")
    log(f"  hazards: {sorted(hazard_set)}")
    log(
        "  latency: "
        f"raw={args.latency_raw} waw={args.latency_waw} "
        f"war={args.latency_war} temp={args.latency_temp} default={args.latency_default}"
    )
    log(f"  gate: {args.constraint_threshold}")
    log(f"  lambda: {args.lambda_cycles}")
    log(f"  fallback_cycles: {max(10_000, int(getattr(best_spec, 'total_cycles', 0)))}")
    log(f"  best_cycles: {best_score.get('cycles')}")
    log(f"  best_energy: {best_score.get('energy')}")
    log(f"  best_penalty: {best_score.get('constraint_penalty')}")
    log(f"  best_gap: {best_score.get('gap')}")
    log(f"  elapsed_s: {time.time() - start_ts:.1f}")
    if summary_hash:
        if "error" in summary_hash:
            log(f"  dag_hash_error: {summary_hash['error']}")
        else:
            log(f"  dag_hash: {summary_hash['dag_hash']}")
            log(f"  bundle_count: {summary_hash['bundle_count']}")
            log(f"  baseline_cycles: {summary_hash['baseline_cycles']}")
            log(f"  dependency_model: {summary_hash['dependency_model']}")
    if summary_hash is None:
        log(f"  dependency_model: {dep_model_for_args(best_spec)}")
    if args.out:
        with open(args.out, "w", encoding="utf-8") as f:
            json.dump({"score": best_score, "spec": spec_to_json(best_spec)}, f, indent=2)
    close_log()


if __name__ == "__main__":
    main()
