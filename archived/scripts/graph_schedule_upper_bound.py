#!/usr/bin/env python3
"""
Compute a tight *upper bound* on cycles for a fixed instruction multiset
by rescheduling slots under dependency + resource constraints.

This does NOT change the algorithm; it only repacks existing slots into
new bundles while respecting conservative dependencies.
"""
from __future__ import annotations

from dataclasses import dataclass
from collections import defaultdict, deque
import argparse
import heapq
import math
import random
from typing import Iterable

import os
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
if ROOT not in sys.path:
    sys.path.insert(0, ROOT)

from perf_takehome import KernelBuilder
from problem import VLEN, SLOT_LIMITS

ENGINES = [e for e in SLOT_LIMITS if e != "debug"]
CAPS = {e: SLOT_LIMITS[e] for e in ENGINES}


@dataclass(frozen=True)
class Task:
    tid: int
    engine: str
    slot: tuple
    reads: frozenset[int]
    writes: frozenset[int]
    bundle_idx: int


def _r_range(base: int, length: int) -> set[int]:
    return set(range(base, base + length))


def rw_sets(engine: str, slot: tuple) -> tuple[set[int], set[int]]:
    """Return (reads, writes) scratch addresses for a slot."""
    if engine == "alu":
        _, dest, a1, a2 = slot
        return {a1, a2}, {dest}
    if engine == "valu":
        op = slot[0]
        if op == "vbroadcast":
            _, dest, src = slot
            return {src}, _r_range(dest, VLEN)
        if op == "multiply_add":
            _, dest, a, b, c = slot
            return _r_range(a, VLEN) | _r_range(b, VLEN) | _r_range(c, VLEN), _r_range(dest, VLEN)
        # generic vector op
        _, dest, a1, a2 = slot
        return _r_range(a1, VLEN) | _r_range(a2, VLEN), _r_range(dest, VLEN)
    if engine == "load":
        op = slot[0]
        if op == "load":
            _, dest, addr = slot
            return {addr}, {dest}
        if op == "load_offset":
            _, dest, addr, offset = slot
            return {addr + offset}, {dest + offset}
        if op == "vload":
            _, dest, addr = slot
            return {addr}, _r_range(dest, VLEN)
        if op == "const":
            _, dest, _val = slot
            return set(), {dest}
    if engine == "store":
        op = slot[0]
        if op == "store":
            _, addr, src = slot
            return {addr, src}, set()
        if op == "vstore":
            _, addr, src = slot
            return {addr} | _r_range(src, VLEN), set()
    if engine == "flow":
        op = slot[0]
        if op == "select":
            _, dest, cond, a, b = slot
            return {cond, a, b}, {dest}
        if op == "add_imm":
            _, dest, a, _imm = slot
            return {a}, {dest}
        if op == "vselect":
            _, dest, cond, a, b = slot
            return _r_range(cond, VLEN) | _r_range(a, VLEN) | _r_range(b, VLEN), _r_range(dest, VLEN)
        if op == "trace_write":
            _, val = slot
            return {val}, set()
        if op == "coreid":
            _, dest = slot
            return set(), {dest}
        # control-flow ops (halt/pause/jump/cond_jump/etc.)
        return set(), set()
    raise ValueError(f"Unknown engine/slot: {engine} {slot}")


def build_tasks(instrs: list[dict], conservative_mem: bool = True) -> tuple[list[Task], list[set[int]]]:
    tasks: list[Task] = []
    deps: list[set[int]] = []
    last_write: dict[int, int] = {}
    last_mem: int | None = None

    for bundle_idx, instr in enumerate(instrs):
        bundle_task_ids: list[int] = []
        bundle_mem_ids: list[int] = []

        for engine, slots in instr.items():
            if engine == "debug":
                continue
            for slot in slots:
                reads, writes = rw_sets(engine, slot)
                tid = len(tasks)
                dep_set: set[int] = set()

                # RAW/WAW on scratch, but only against previous bundles
                for r in reads:
                    if r in last_write:
                        dep_set.add(last_write[r])
                for w in writes:
                    if w in last_write:
                        dep_set.add(last_write[w])

                # conservative memory order across bundles
                if conservative_mem and engine in ("load", "store"):
                    if last_mem is not None:
                        dep_set.add(last_mem)
                    bundle_mem_ids.append(tid)

                tasks.append(Task(tid, engine, slot, frozenset(reads), frozenset(writes), bundle_idx))
                deps.append(dep_set)
                bundle_task_ids.append(tid)

        # update last writers after the whole bundle (same-cycle writes are concurrent)
        for tid in bundle_task_ids:
            for w in tasks[tid].writes:
                last_write[w] = tid

        if conservative_mem and bundle_mem_ids:
            last_mem = bundle_mem_ids[-1]

    return tasks, deps


def build_graph(tasks: list[Task], deps: list[set[int]]) -> tuple[list[list[int]], list[int]]:
    n = len(tasks)
    succ = [[] for _ in range(n)]
    indeg = [0] * n
    for tid, dep_set in enumerate(deps):
        for d in dep_set:
            succ[d].append(tid)
            indeg[tid] += 1
    return succ, indeg


def longest_path_lengths(succ: list[list[int]], indeg: list[int]) -> tuple[list[int], list[int], int]:
    n = len(indeg)
    # topological order (Kahn)
    indeg_work = indeg[:]
    q = deque([i for i, d in enumerate(indeg_work) if d == 0])
    topo = []
    while q:
        u = q.popleft()
        topo.append(u)
        for v in succ[u]:
            indeg_work[v] -= 1
            if indeg_work[v] == 0:
                q.append(v)
    if len(topo) != n:
        raise RuntimeError("Cycle detected in dependency graph")

    earliest = [0] * n
    for u in topo:
        if succ[u]:
            for v in succ[u]:
                earliest[v] = max(earliest[v], earliest[u] + 1)

    height = [1] * n
    for u in reversed(topo):
        if succ[u]:
            height[u] = 1 + max(height[v] for v in succ[u])
        else:
            height[u] = 1

    cp = 0
    for u in range(n):
        cp = max(cp, earliest[u] + height[u] - 1)
    return earliest, height, cp


def schedule(tasks: list[Task], succ: list[list[int]], indeg: list[int],
             earliest: list[int], height: list[int], mode: str, *, seed: int, jitter: float) -> int:
    n = len(tasks)
    indeg_work = indeg[:]
    # slack based on critical path estimate
    cp = max(earliest[u] + height[u] - 1 for u in range(n)) if n else 0
    slack = [cp - (earliest[u] + height[u] - 1) for u in range(n)]
    outdeg = [len(succ[u]) for u in range(n)]
    rnd = random.Random(seed)

    def prio_tuple(tid: int):
        jitter_val = rnd.random() * jitter
        if mode == "height":
            return (-height[tid], jitter_val, tid)
        if mode == "slack":
            return (slack[tid], -height[tid], jitter_val, tid)
        if mode == "mix":
            return (slack[tid], -height[tid], -outdeg[tid], jitter_val, tid)
        if mode == "global":
            return (slack[tid], -height[tid], -outdeg[tid], jitter_val, tid)
        raise ValueError(f"unknown mode {mode}")

    ready = {e: [] for e in ENGINES}
    ready_all: set[int] = set()
    for tid, d in enumerate(indeg_work):
        if d == 0:
            if mode == "global":
                ready_all.add(tid)
            else:
                heapq.heappush(ready[tasks[tid].engine], (prio_tuple(tid), tid))

    t = 0
    scheduled = 0
    while scheduled < n:
        cycle_tasks = []
        if mode == "global":
            writes_cycle: set[int] = set()
            engine_counts = {e: 0 for e in ENGINES}
            ready_now = [tid for tid in ready_all if earliest[tid] <= t]
            ready_now.sort(key=prio_tuple)
            for tid in ready_now:
                eng = tasks[tid].engine
                if engine_counts[eng] >= CAPS[eng]:
                    continue
                if any(w in writes_cycle for w in tasks[tid].writes):
                    continue
                cycle_tasks.append(tid)
                engine_counts[eng] += 1
                for w in tasks[tid].writes:
                    writes_cycle.add(w)
            if not cycle_tasks:
                # advance to next earliest ready task
                next_t = None
                for tid in ready_all:
                    rt = earliest[tid]
                    if next_t is None or rt < next_t:
                        next_t = rt
                t = t + 1 if next_t is None else max(t + 1, next_t)
                continue
        else:
            for eng in ENGINES:
                cap = CAPS[eng]
                q = ready[eng]
                for _ in range(cap):
                    if not q:
                        break
                    _, tid = heapq.heappop(q)
                    cycle_tasks.append(tid)

        if not cycle_tasks:
            raise RuntimeError("Deadlock: no ready tasks but schedule incomplete")

        # complete the cycle: release successors
        for tid in cycle_tasks:
            scheduled += 1
            for v in succ[tid]:
                indeg_work[v] -= 1
                if indeg_work[v] == 0:
                    if mode == "global":
                        ready_all.add(v)
                    else:
                        heapq.heappush(ready[tasks[v].engine], (prio_tuple(v), v))

        if mode == "global":
            for tid in cycle_tasks:
                ready_all.discard(tid)
        t += 1

    return t


def count_cycles(instrs: list[dict]) -> int:
    return sum(1 for instr in instrs if any(k != "debug" for k in instr))


def resource_bound(tasks: list[Task]) -> tuple[int, dict[str, tuple[int, int, int]]]:
    totals = defaultdict(int)
    for t in tasks:
        totals[t.engine] += 1
    parts = {}
    lb = 0
    for eng in ENGINES:
        total = totals.get(eng, 0)
        if total == 0:
            continue
        part = math.ceil(total / CAPS[eng])
        parts[eng] = (total, CAPS[eng], part)
        lb = max(lb, part)
    return lb, parts


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--forest-height", type=int, default=10)
    ap.add_argument("--rounds", type=int, default=16)
    ap.add_argument("--batch-size", type=int, default=256)
    ap.add_argument("--instrs-module", type=str, default="",
                    help="Import path to a module with build_instrs(), e.g. generator.cache_top4_d4x15_skip_r3_x4_24_offhash_900")
    ap.add_argument("--kernel-builder-path", type=str, default="",
                    help="Path to a Python file that defines KernelBuilder (same as tests override)")
    ap.add_argument("--conservative-mem", action="store_true", help="keep all mem ops in program order")
    ap.add_argument("--mode", choices=["height", "slack", "mix", "global", "all"], default="all")
    ap.add_argument("--restarts", type=int, default=1, help="randomized restarts per mode")
    ap.add_argument("--seed", type=int, default=0, help="base RNG seed")
    ap.add_argument("--jitter", type=float, default=0.0, help="priority jitter for tie-breaking")
    args = ap.parse_args()

    if args.kernel_builder_path:
        import importlib.util
        import os as _os
        path = _os.path.abspath(args.kernel_builder_path)
        spec = importlib.util.spec_from_file_location("kernel_builder_override", path)
        if spec is None or spec.loader is None:
            raise ImportError(f"Failed to load KernelBuilder override: {path}")
        module = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(module)
        if not hasattr(module, "KernelBuilder"):
            raise AttributeError("KernelBuilder override module must define KernelBuilder.")
        KB = module.KernelBuilder
        n_nodes = 2 ** (args.forest_height + 1) - 1
        kb = KB()
        kb.build_kernel(args.forest_height, n_nodes, args.batch_size, args.rounds)
        instrs = kb.instrs
    elif args.instrs_module:
        import importlib
        mod = importlib.import_module(args.instrs_module)
        if not hasattr(mod, "build_instrs"):
            raise AttributeError(f"{args.instrs_module} has no build_instrs()")
        instrs = mod.build_instrs()
    else:
        n_nodes = 2 ** (args.forest_height + 1) - 1
        kb = KernelBuilder()
        kb.build_kernel(args.forest_height, n_nodes, args.batch_size, args.rounds)
        instrs = kb.instrs

    base_cycles = count_cycles(instrs)
    tasks, deps = build_tasks(instrs, conservative_mem=args.conservative_mem)
    succ, indeg = build_graph(tasks, deps)
    earliest, height, cp = longest_path_lengths(succ, indeg)
    res_lb, parts = resource_bound(tasks)

    print(f"bundles_in_program: {base_cycles}")
    print(f"tasks: {len(tasks)}")
    print(f"critical_path_lb: {cp}")
    print(f"resource_lb: {res_lb} (per-engine: {parts})")

    modes = [args.mode] if args.mode != "all" else ["slack", "mix", "height"]
    best = None
    for mode in modes:
        best_mode = None
        for k in range(max(1, args.restarts)):
            sched_cycles = schedule(
                tasks,
                succ,
                indeg,
                earliest,
                height,
                mode,
                seed=args.seed + k,
                jitter=args.jitter,
            )
            if best_mode is None or sched_cycles < best_mode:
                best_mode = sched_cycles
        print(f"scheduled_cycles_{mode}: {best_mode}")
        best = best_mode if best is None else min(best, best_mode)
    if args.mode == "all":
        print(f"best_scheduled_cycles: {best}")


if __name__ == "__main__":
    main()
