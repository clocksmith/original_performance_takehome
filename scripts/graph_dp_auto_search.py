#!/usr/bin/env python3
"""
Automatic strategy search:
- Sweep global SpecBase knobs.
- For each config, run Pareto DP over per-round cache depth choices.
- Use DP result as optimistic bound; then build and schedule the best path
  to get an actual cycle upper bound.
"""
from __future__ import annotations

from dataclasses import replace
import argparse
import os
import sys
from typing import Any

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
if ROOT not in sys.path:
    sys.path.insert(0, ROOT)

from generator.spec_base import SPEC_BASE
from generator.scratch_layout import ScratchAlloc, build_layout
from generator.op_list import build_ops
from generator.ops import OpLists, Op
from generator.build_kernel_base import build_base_instrs, _build_setup_prelude
from generator.schedule_dep import schedule_ops_dep
from problem import SLOT_LIMITS, VLEN

import scripts.pareto_dp as pareto

CAPS = {k: v for k, v in SLOT_LIMITS.items() if k != "debug"}
CAPS_KEY = tuple(sorted(CAPS.items()))


def _freeze(obj: Any) -> Any:
    if isinstance(obj, dict):
        return tuple(sorted((k, _freeze(v)) for k, v in obj.items()))
    if isinstance(obj, (list, tuple)):
        return tuple(_freeze(v) for v in obj)
    return obj


def _spec_cache_key(spec) -> tuple[tuple[str, Any], ...]:
    data = dict(spec.__dict__)
    # Ignore fields that don't affect build_ops counts.
    data.pop("offload_op1", None)
    data.pop("setup_style", None)
    data.pop("total_cycles", None)
    data.pop("valu_pad_cycles", None)
    return tuple(sorted((k, _freeze(v)) for k, v in data.items()))


def parse_list(s: str) -> list[str]:
    return [x.strip() for x in s.split(",") if x.strip()]


def parse_int_list(s: str) -> list[int]:
    return [int(x) for x in parse_list(s)]


def parse_bool_list(s: str) -> list[bool]:
    return [bool(int(x)) for x in parse_list(s)]


def _count_ops(ops: OpLists, *, round_only: bool) -> dict[str, int]:
    counts = {"alu_base": 0, "valu_raw": 0, "flow": 0, "load": 0, "store": 0}

    def include(op):
        if op.meta is None:
            return not round_only
        if round_only:
            return "round" in op.meta
        return "round" not in op.meta

    for op in ops.alu_ops:
        if include(op):
            counts["alu_base"] += 1
    for op in ops.valu_ops:
        if include(op):
            counts["valu_raw"] += 1
    for op in ops.flow_ops:
        if include(op):
            counts["flow"] += 1
    for op in ops.load_ops:
        if include(op):
            counts["load"] += 1
    for op in ops.store_ops:
        if include(op):
            counts["store"] += 1
    return counts


def _count_offloadable(ops: OpLists, *, round_only: bool) -> int:
    total = 0

    def include(op):
        if op.meta is None:
            return not round_only
        if round_only:
            return "round" in op.meta
        return "round" not in op.meta

    for op in ops.valu_ops:
        if include(op) and getattr(op, "offloadable", False):
            total += 1
    return total


def _choice_spec(base_spec, cache_depth: int | None, cache_x: int, *, allow_depth4: bool) -> Any:
    spec = replace(
        base_spec,
        rounds=1,
        base_cached_rounds=(),
        depth4_rounds=0,
        depth4_cached_rounds=(),
        cached_round_depth={},
        cached_round_x={},
    )
    if cache_depth is None:
        return spec
    if cache_depth in (0, 1, 2, 3):
        return replace(spec, cached_round_depth={0: cache_depth}, cached_round_x={0: cache_x})
    if cache_depth == 4:
        if not allow_depth4:
            return spec
        return replace(spec, depth4_rounds=1, depth4_cached_rounds=(0,), x4=cache_x)
    raise ValueError(f"unknown cache_depth {cache_depth}")


def _build_choice_counts(spec) -> tuple[dict[str, int], int, dict[str, int]]:
    scratch = ScratchAlloc()
    layout = build_layout(spec, scratch)
    ops = build_ops(spec, layout)

    round_counts = _count_ops(ops, round_only=True)
    round_offloadable = _count_offloadable(ops, round_only=True)
    setup_counts = _count_ops(ops, round_only=False)
    setup_offloadable = _count_offloadable(ops, round_only=False)

    scratch_abs = scratch.ptr

    return (
        {**round_counts, "offloadable": round_offloadable},
        scratch_abs,
        {**setup_counts, "offloadable": setup_offloadable},
    )


def _choice_counts_cached(
    base_spec,
    depth: int | None,
    cx: int,
    *,
    allow_depth4: bool,
    cache: dict[tuple, tuple[dict[str, int], int, dict[str, int]]],
    spec_key: tuple,
) -> tuple[dict[str, int], int, dict[str, int]]:
    key = (spec_key, depth, cx)
    cached = cache.get(key)
    if cached is not None:
        return cached
    spec = _choice_spec(base_spec, depth, cx, allow_depth4=allow_depth4)
    counts = _build_choice_counts(spec)
    cache[key] = counts
    return counts


def _state_with_offload_cap(state: pareto.State, cap: int) -> pareto.State:
    if cap <= 0:
        return state
    off = min(state.offloadable, cap)
    pref = min(state.offload_prefix, cap)
    return pareto.State(
        alu_base=state.alu_base,
        valu_raw=state.valu_raw,
        flow=state.flow,
        load=state.load,
        store=state.store,
        offloadable=off,
        offload_prefix=pref,
        prefix_open=state.prefix_open,
        scratch=state.scratch,
        choice_path=state.choice_path,
    )


def _choice_depth_from_name(name: str) -> tuple[int | None, int]:
    # name format: "d=DEPTH,x=X"
    parts = name.split(",")
    depth = None
    x = 0
    for p in parts:
        if p.startswith("d="):
            val = p[2:]
            depth = None if val == "none" else int(val)
        elif p.startswith("x="):
            x = int(p[2:])
    return depth, x


def _build_spec_from_path(base_spec, path: list[str], *, vectors: int, x4: int) -> Any:
    cached_round_depth = {}
    cached_round_x = {}
    depth4_cached_rounds = []

    for r, name in enumerate(path):
        depth, cx = _choice_depth_from_name(name)
        if depth is None:
            continue
        if depth in (0, 1, 2, 3):
            cached_round_depth[r] = depth
            cached_round_x[r] = vectors
        elif depth == 4:
            depth4_cached_rounds.append(r)
        else:
            raise ValueError(f"unknown depth {depth}")

    spec = replace(
        base_spec,
        base_cached_rounds=(),
        cached_round_depth=cached_round_depth,
        cached_round_x=cached_round_x,
        depth4_cached_rounds=tuple(depth4_cached_rounds),
        depth4_rounds=len(depth4_cached_rounds),
        x4=x4,
    )
    return spec


def count_cycles(instrs: list[dict]) -> int:
    return sum(1 for instr in instrs if any(k != "debug" for k in instr))

def _reads_writes(op: Op) -> tuple[list[int], list[int]]:
    # Mirror generator.schedule_dep._reads_writes
    engine = op.engine
    slot = op.slot

    def _vec_addrs(base: int) -> list[int]:
        return [base + i for i in range(VLEN)]

    if engine == "alu":
        _, dest, a1, a2 = slot
        return [a1, a2], [dest]

    if engine == "load":
        match slot:
            case ("const", dest, _val):
                return [], [dest]
            case ("load", dest, addr):
                return [addr], [dest]
            case ("vload", dest, addr):
                return [addr], _vec_addrs(dest)
            case ("load_offset", dest, addr, offset):
                return [addr + offset], [dest + offset]
        raise NotImplementedError(f"Unknown load op {slot}")

    if engine == "store":
        match slot:
            case ("store", addr, src):
                return [addr, src], []
            case ("vstore", addr, src):
                return [addr, *_vec_addrs(src)], []
        raise NotImplementedError(f"Unknown store op {slot}")

    if engine == "flow":
        match slot:
            case ("add_imm", dest, a, _imm):
                return [a], [dest]
            case ("select", dest, cond, a, b):
                return [cond, a, b], [dest]
            case ("vselect", dest, cond, a, b):
                return [*_vec_addrs(cond), *_vec_addrs(a), *_vec_addrs(b)], _vec_addrs(dest)
        raise NotImplementedError(f"Unknown flow op {slot}")

    if engine == "valu":
        match slot:
            case ("vbroadcast", dest, src):
                return [src], _vec_addrs(dest)
            case ("multiply_add", dest, a, b, c):
                return [*_vec_addrs(a), *_vec_addrs(b), *_vec_addrs(c)], _vec_addrs(dest)
            case (_op, dest, a1, a2):
                return [*_vec_addrs(a1), *_vec_addrs(a2)], _vec_addrs(dest)
        raise NotImplementedError(f"Unknown valu op {slot}")

    if engine == "debug":
        return [], []

    raise NotImplementedError(f"Unknown engine {engine}")


def _build_dep_graph(ops: list[Op]):
    n_ops = len(ops)
    reads_list: list[list[int]] = []
    writes_list: list[list[int]] = []
    for op in ops:
        reads, writes = _reads_writes(op)
        reads_list.append(reads)
        writes_list.append(writes)

    deps: list[list[tuple[int, int]]] = [list() for _ in range(n_ops)]
    last_write: dict[int, int] = {}
    last_read: dict[int, int] = {}
    last_temp: dict[str, int] = {}

    for i in range(n_ops):
        reads = reads_list[i]
        writes = writes_list[i]
        for addr in reads:
            if addr in last_write:
                deps[i].append((last_write[addr], 1))
        for addr in writes:
            if addr in last_write:
                deps[i].append((last_write[addr], 1))
            if addr in last_read:
                deps[i].append((last_read[addr], 0))
        temps: list[str] = []
        if ops[i].meta is not None:
            temp_meta = ops[i].meta.get("temp")
            if temp_meta:
                if isinstance(temp_meta, str):
                    temps = [temp_meta]
                else:
                    temps = list(temp_meta)
        for key in temps:
            if key in last_temp:
                deps[i].append((last_temp[key], 1))

        for addr in reads:
            last_read[addr] = i
        for addr in writes:
            last_write[addr] = i
            last_read.pop(addr, None)
        for key in temps:
            last_temp[key] = i

    children: list[list[tuple[int, int]]] = [[] for _ in range(n_ops)]
    indegree = [0] * n_ops
    for i in range(n_ops):
        for d, latency in deps[i]:
            children[d].append((i, latency))
            indegree[i] += 1

    # critical-path priority
    priority = [1] * n_ops
    for i in range(n_ops - 1, -1, -1):
        if children[i]:
            priority[i] = 1 + max(priority[c] for c, _ in children[i])

    return children, indegree, priority, writes_list


def _schedule_ops_custom(ops: list[Op], *, seed: int, jitter: float) -> int:
    import random

    rnd = random.Random(seed)
    n_ops = len(ops)
    children, indegree, priority, writes_list = _build_dep_graph(ops)

    earliest = [0] * n_ops
    scheduled = [-1] * n_ops
    ready: list[tuple[int, int]] = []  # (ready_cycle, idx)

    for i in range(n_ops):
        if indegree[i] == 0:
            ready.append((0, i))

    cycle = 0
    remaining = n_ops

    while remaining > 0:
        available = [i for rc, i in ready if rc <= cycle]
        if not available:
            next_cycle = min(rc for rc, _ in ready)
            cycle = max(cycle + 1, next_cycle)
            continue

        writes_cycle: set[int] = set()
        engine_counts = {e: 0 for e in CAPS}

        def key(i: int):
            # prioritize critical path; break ties with jitter
            return (-priority[i], rnd.random() * jitter)

        scheduled_any = False
        made_progress = True
        while made_progress:
            made_progress = False
            available = [i for rc, i in ready if rc <= cycle and scheduled[i] < 0]
            if not available:
                break
            available.sort(key=key)
            scheduled_now: list[int] = []
            for i in available:
                eng = ops[i].engine
                if eng == "debug":
                    continue
                if engine_counts[eng] >= CAPS[eng]:
                    continue
                if any(w in writes_cycle for w in writes_list[i]):
                    continue
                scheduled[i] = cycle
                scheduled_now.append(i)
                engine_counts[eng] += 1
                for w in writes_list[i]:
                    writes_cycle.add(w)

            if not scheduled_now:
                break

            scheduled_any = True
            remaining -= len(scheduled_now)
            new_ready: list[tuple[int, int]] = []
            for i in scheduled_now:
                for child, latency in children[i]:
                    indegree[child] -= 1
                    earliest[child] = max(earliest[child], cycle + latency)
                    if indegree[child] == 0:
                        new_ready.append((earliest[child], child))

            ready = [(rc, i) for rc, i in ready if scheduled[i] < 0]
            ready.extend(new_ready)
            made_progress = True

        if not scheduled_any:
            cycle += 1
            continue

        cycle += 1

    return cycle


def schedule_with_restarts(ops: list[Op], *, restarts: int, seed: int, jitter: float) -> int:
    best = None
    for k in range(restarts):
        c = _schedule_ops_custom(ops, seed=seed + k, jitter=jitter)
        if best is None or c < best:
            best = c
    return best if best is not None else 0


def build_final_ops(spec) -> list[Op]:
    # Build a flat op list matching build_base_instrs, but without bundling.
    scratch = ScratchAlloc()
    layout = build_layout(spec, scratch)

    setup_ops: list[Op] = []
    if getattr(spec, "setup_style", "inline") == "packed":
        setup_instrs = _build_setup_prelude(spec, layout)
        for instr in setup_instrs:
            for eng, slots in instr.items():
                for slot in slots:
                    setup_ops.append(Op(engine=eng, slot=slot, meta={"setup": True}))

    spec_for_ops = spec
    if getattr(spec, "setup_style", "inline") in {"packed", "none"} and getattr(spec, "include_setup", True):
        spec_for_ops = replace(spec, include_setup=False)

    ordered_ops: list[Op] = []
    build_ops(spec_for_ops, layout, ordered_ops=ordered_ops)

    # Apply offload in-order
    final_ops: list[Op] = []
    offloaded = 0
    for op in setup_ops + ordered_ops:
        if op.offloadable and offloaded < spec.offload_op1:
            op_name, dest, a, b = op.slot
            for lane in range(VLEN):
                final_ops.append(Op(engine="alu", slot=(op_name, dest + lane, a + lane, b + lane), meta=op.meta))
            offloaded += 1
        else:
            final_ops.append(op)
    return final_ops


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--selection", type=str, default="eq,bitmask,mask,mask_precompute")
    ap.add_argument("--idx-shifted", type=str, default="0,1")
    ap.add_argument("--offload-hash-op1", type=str, default="0,1")
    ap.add_argument("--offload-hash-shift", type=str, default="0,1")
    ap.add_argument("--offload-hash-op2", type=str, default="0,1")
    ap.add_argument("--offload-parity", type=str, default="0,1")
    ap.add_argument("--offload-node-xor", type=str, default="0,1")
    ap.add_argument("--node-ptr-incremental", type=str, default="0,1")
    ap.add_argument("--ptr-setup-engine", type=str, default="flow,alu")
    ap.add_argument("--setup-style", type=str, default="packed,inline")
    ap.add_argument("--offload-op1", type=str, default="0,200,400,600,800,1000,1200,1400")
    ap.add_argument("--cache-depths", type=str, default="none,0,1,2,3,4")
    ap.add_argument("--cache-x", type=str, default="8,12,15,24,32")
    ap.add_argument("--cache-x-all", type=int, default=0,
                    help="if 1, allow cache_x choices for depths 0..3 (partial caching)")
    ap.add_argument("--rounds", type=int, default=16)
    ap.add_argument("--max-states", type=int, default=20000)
    ap.add_argument("--max-candidates", type=int, default=200)
    ap.add_argument("--schedule-top", type=int, default=10, help="schedule top-N DP candidates")
    ap.add_argument("--offload-order-mode", choices=["unlocked", "vector_major"], default="unlocked")
    ap.add_argument("--cap-offload", type=int, default=1,
                    help="if 1, cap offloadable ops by offload_op1; if 0, ignore cap (more optimistic DP)")
    ap.add_argument("--sched-mode", choices=["custom", "dep", "bundled"], default="custom",
                    help="custom: randomized critical-path scheduler; dep: schedule_dep; bundled: build_base_instrs")
    ap.add_argument("--sched-restarts", type=int, default=8, help="randomized restarts per candidate")
    ap.add_argument("--sched-seed", type=int, default=0)
    ap.add_argument("--sched-jitter", type=float, default=0.35, help="tie-break jitter in custom scheduler")
    args = ap.parse_args()

    selection_modes = parse_list(args.selection)
    idx_shifted_list = parse_bool_list(args.idx_shifted)
    offload_hash_op1_list = parse_bool_list(args.offload_hash_op1)
    offload_hash_shift_list = parse_bool_list(args.offload_hash_shift)
    offload_hash_op2_list = parse_bool_list(args.offload_hash_op2)
    offload_parity_list = parse_bool_list(args.offload_parity)
    offload_node_xor_list = parse_bool_list(args.offload_node_xor)
    node_ptr_inc_list = parse_bool_list(args.node_ptr_incremental)
    ptr_engines = parse_list(args.ptr_setup_engine)
    setup_styles = parse_list(args.setup_style)
    offload_op1_list = parse_int_list(args.offload_op1)
    cache_depths = [None if x == "none" else int(x) for x in parse_list(args.cache_depths)]
    cache_xs = parse_int_list(args.cache_x)

    best_sched = None
    best_sched_spec = None
    candidates = []
    tried = 0

    choice_cache: dict[tuple, tuple[dict[str, int], int, dict[str, int]]] = {}
    dp_cache: dict[tuple, list[pareto.State]] = {}
    best_cache: dict[tuple, tuple[int | None, pareto.State | None]] = {}

    def stop() -> bool:
        return bool(args.max_candidates and tried >= args.max_candidates)

    allow_depth4 = 4 in cache_depths
    if not cache_xs:
        cache_xs = [SPEC_BASE.x4]
    x4_choices = cache_xs if allow_depth4 else [cache_xs[0]]

    for selection in selection_modes:
        use_bitmask = selection == "bitmask"
        if stop():
            break
        for idx_shifted in idx_shifted_list:
            if stop():
                break
            for offload_hash_op1 in offload_hash_op1_list:
                if stop():
                    break
                for offload_hash_shift in offload_hash_shift_list:
                    if stop():
                        break
                    for offload_hash_op2 in offload_hash_op2_list:
                        if stop():
                            break
                        for offload_parity in offload_parity_list:
                            if stop():
                                break
                            for offload_node_xor in offload_node_xor_list:
                                if stop():
                                    break
                                for node_ptr_inc in node_ptr_inc_list:
                                    if stop():
                                        break
                                    for ptr_engine in ptr_engines:
                                        if stop():
                                            break

                                        dp_spec_base = replace(
                                            SPEC_BASE,
                                            selection_mode=selection,
                                            use_bitmask_selection=use_bitmask,
                                            idx_shifted=idx_shifted,
                                            offload_hash_op1=offload_hash_op1,
                                            offload_hash_shift=offload_hash_shift,
                                            offload_hash_op2=offload_hash_op2,
                                            offload_parity=offload_parity,
                                            offload_node_xor=offload_node_xor,
                                            node_ptr_incremental=node_ptr_inc,
                                            ptr_setup_engine=ptr_engine,
                                            include_setup=True,
                                        )
                                        spec_key = _spec_cache_key(dp_spec_base)

                                        for x4 in x4_choices:
                                            if stop():
                                                break

                                            dp_key = (
                                                spec_key,
                                                x4,
                                                tuple(cache_depths),
                                                tuple(cache_xs),
                                                args.cache_x_all,
                                                args.rounds,
                                                args.offload_order_mode,
                                                CAPS_KEY,
                                                args.max_states,
                                                1536,
                                            )
                                            frontier = dp_cache.get(dp_key)

                                            if frontier is None:
                                                choices = []
                                                setup_profile = {
                                                    "alu_base": 0,
                                                    "valu_raw": 0,
                                                    "flow": 0,
                                                    "load": 0,
                                                    "store": 0,
                                                    "offloadable": 0,
                                                    "offload_prefix": 0,
                                                    "scratch": 0,
                                                }

                                                for depth in cache_depths:
                                                    if depth == 4 and not allow_depth4:
                                                        continue
                                                    if depth is None:
                                                        depth_xs = [0]
                                                    elif depth == 4:
                                                        depth_xs = [x4]
                                                    else:
                                                        depth_xs = cache_xs if args.cache_x_all else [dp_spec_base.vectors]
                                                    for cx in depth_xs:
                                                        try:
                                                            counts, scratch_abs, setup_counts = _choice_counts_cached(
                                                                dp_spec_base,
                                                                depth,
                                                                cx,
                                                                allow_depth4=allow_depth4,
                                                                cache=choice_cache,
                                                                spec_key=spec_key,
                                                            )
                                                        except Exception:
                                                            continue

                                                        for k in ("alu_base", "valu_raw", "flow", "load", "store", "offloadable"):
                                                            setup_profile[k] = max(
                                                                setup_profile[k], setup_counts.get(k, 0)
                                                            )
                                                        setup_profile["scratch"] = max(
                                                            setup_profile["scratch"], scratch_abs
                                                        )

                                                        choices.append(
                                                            {
                                                                "name": f"d={depth if depth is not None else 'none'},x={cx}",
                                                                "alu_base": counts["alu_base"],
                                                                "valu_raw": counts["valu_raw"],
                                                                "flow": counts["flow"],
                                                                "load": counts["load"],
                                                                "store": counts["store"],
                                                                "offloadable": counts["offloadable"],
                                                                "offload_prefix": counts["offloadable"],
                                                                "scratch_abs": scratch_abs,
                                                            }
                                                        )

                                                if not choices:
                                                    continue

                                                cfg = {
                                                    "globals": {
                                                        "selection_mode": selection,
                                                        "offload_order_mode": args.offload_order_mode,
                                                        "scratch_mode": "max",
                                                        "setup_profile": "default",
                                                    },
                                                    "setup_profiles": {"default": setup_profile},
                                                    "rounds": [
                                                        {"round": r, "choices": choices} for r in range(args.rounds)
                                                    ],
                                                    "caps": CAPS,
                                                    "scratch_limit": 1536,
                                                }

                                                frontier = pareto._run_dp(
                                                    cfg,
                                                    include_setup=True,
                                                    caps=CAPS,
                                                    max_states=args.max_states,
                                                    offload_order_mode=args.offload_order_mode,
                                                    max_T=None,
                                                    progress_log=None,
                                                    checkpoint=None,
                                                    checkpoint_every=0,
                                                    resume_state=None,
                                                    log_every_seconds=0.0,
                                                )
                                                dp_cache[dp_key] = frontier

                                            for offload_op1 in offload_op1_list:
                                                if stop():
                                                    break

                                                cap_key = offload_op1 if args.cap_offload else -1
                                                best_key = (dp_key, cap_key)
                                                if best_key in best_cache:
                                                    best_T, best_state = best_cache[best_key]
                                                else:
                                                    best_T = None
                                                    best_state = None
                                                    for s in frontier:
                                                        s_cap = _state_with_offload_cap(
                                                            s, offload_op1
                                                        ) if args.cap_offload else s
                                                        T = pareto._min_T_for_state(
                                                            s_cap,
                                                            offload_order_mode=args.offload_order_mode,
                                                            caps=CAPS,
                                                            max_T=None,
                                                        )
                                                        if T is not None and (best_T is None or T < best_T):
                                                            best_T = T
                                                            best_state = s
                                                    best_cache[best_key] = (best_T, best_state)

                                                if best_T is None or best_state is None:
                                                    continue

                                                for setup_style in setup_styles:
                                                    if stop():
                                                        break
                                                    tried += 1
                                                    sched_spec = replace(
                                                        dp_spec_base,
                                                        offload_op1=offload_op1,
                                                        setup_style=setup_style,
                                                    )
                                                    candidates.append((best_T, sched_spec, x4, best_state))

    candidates.sort(key=lambda x: x[0])
    print(f"candidates tried: {len(candidates)}")
    print("top DP bounds:")
    for i, (t, spec, x4, _state) in enumerate(candidates[: min(5, len(candidates))]):
        print(
            f"  {i+1}. T={t} selection={spec.selection_mode} idx_shifted={spec.idx_shifted} "
            f"x4={x4} offload_op1={spec.offload_op1} setup={spec.setup_style}"
        )

    # Schedule top-N candidates
    for t, spec, x4, state in candidates[: min(args.schedule_top, len(candidates))]:
        full_spec = _build_spec_from_path(spec, state.choice_path, vectors=spec.vectors, x4=x4)
        try:
            if args.sched_mode == "bundled":
                instrs = build_base_instrs(full_spec)
                cycles = count_cycles(instrs)
            else:
                ops = build_final_ops(full_spec)
                if args.sched_mode == "dep":
                    instrs = schedule_ops_dep(ops)
                    cycles = len(instrs)
                else:
                    restarts = max(1, args.sched_restarts)
                    cycles = schedule_with_restarts(
                        ops, restarts=restarts, seed=args.sched_seed, jitter=args.sched_jitter
                    )
        except Exception:
            continue
        if best_sched is None or cycles < best_sched:
            best_sched = cycles
            best_sched_spec = full_spec
        print(f"scheduled cycles: {cycles} (dp_T={t})")

    print(f"best_scheduled_cycles: {best_sched}")
    if best_sched_spec is not None:
        print("best_scheduled_spec:")
        print(best_sched_spec)


if __name__ == "__main__":
    main()
