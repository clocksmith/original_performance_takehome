from __future__ import annotations

from collections import defaultdict
import heapq
from typing import Any

from problem import SLOT_LIMITS, VLEN

from .ops import Op


def _vec_addrs(base: int) -> list[int]:
    return [base + i for i in range(VLEN)]


def _reads_writes(op: Op) -> tuple[list[int], list[int]]:
    engine = op.engine
    slot = op.slot

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


def schedule_ops_dep(
    ops: list[Op],
    return_ops: bool = False,
) -> list[dict[str, list[Any]]]:
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

    priority = [1] * n_ops
    for i in range(n_ops - 1, -1, -1):
        if children[i]:
            priority[i] = 1 + max(priority[c] for c, _ in children[i])

    earliest = [0] * n_ops
    scheduled = [-1] * n_ops
    ready: dict[str, list[tuple[int, int, int]]] = defaultdict(list)

    for i, op in enumerate(ops):
        if indegree[i] == 0:
            heapq.heappush(ready[op.engine], (0, -priority[i], i))

    engine_order = ("valu", "alu", "flow", "load", "store", "debug")
    instrs: list[dict[str, list[tuple[Any, ...]]]] = []

    cycle = 0
    remaining = n_ops
    while remaining > 0:
        while len(instrs) <= cycle:
            instrs.append({})

        writes_cycle: set[int] = set()
        engine_counts: dict[str, int] = {}
        any_scheduled = False

        def release_children(idx: int) -> None:
            for child, latency in children[idx]:
                indegree[child] -= 1
                earliest[child] = max(earliest[child], scheduled[idx] + latency)
                if indegree[child] == 0:
                    child_engine = ops[child].engine
                    heapq.heappush(ready[child_engine], (earliest[child], -priority[child], child))

        made_progress = True
        while made_progress:
            made_progress = False
            for engine in engine_order:
                cap = SLOT_LIMITS[engine]
                if cap <= 0:
                    continue
                count = engine_counts.get(engine, 0)
                if count >= cap:
                    continue
                heap = ready.get(engine)
                if not heap:
                    continue
                skipped: list[tuple[int, int, int]] = []
                while heap and count < cap:
                    ready_cycle, neg_pri, idx = heapq.heappop(heap)
                    if ready_cycle > cycle:
                        skipped.append((ready_cycle, neg_pri, idx))
                        break
                    if any(w in writes_cycle for w in writes_list[idx]):
                        skipped.append((ready_cycle, neg_pri, idx))
                        continue
                    op = ops[idx]
                    if return_ops:
                        instrs[cycle].setdefault(engine, []).append(op)
                    else:
                        instrs[cycle].setdefault(engine, []).append(op.slot)
                    scheduled[idx] = cycle
                    for w in writes_list[idx]:
                        writes_cycle.add(w)
                    remaining -= 1
                    any_scheduled = True
                    made_progress = True
                    count += 1
                    release_children(idx)
                for item in skipped:
                    heapq.heappush(heap, item)
                engine_counts[engine] = count

        if not any_scheduled:
            next_cycle = None
            for heap in ready.values():
                if heap:
                    rc = heap[0][0]
                    if next_cycle is None or rc < next_cycle:
                        next_cycle = rc
            if next_cycle is None:
                break
            cycle = max(cycle + 1, next_cycle)
            continue

        cycle += 1

    return instrs
