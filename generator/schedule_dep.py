from __future__ import annotations

from collections import defaultdict
import heapq
import random
from typing import Any

from problem import SLOT_LIMITS, VLEN

from .ops import Op


def _vec_addrs(base: int) -> list[int]:
    return [base + i for i in range(VLEN)]


def _build_deps(
    ops: list[Op],
    *,
    waw0_same_engine: bool = False,
    waw0_all: bool = False,
) -> tuple[list[list[tuple[int, int]]], list[list[tuple[int, int]]]]:
    """
    Build dependency graph from a linear op stream.

    Returns:
      deps[i]: list of (parent_idx, latency) edges into i
      children[i]: list of (child_idx, latency) edges out of i
    """
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
                p = last_write[addr]
                # The simulator commits scratch writes at end-of-cycle and resolves
                # multiple same-cycle writes by "last write wins" in execution order.
                # We can optionally allow 0-lat WAW to pack independent overwrites.
                if waw0_all:
                    lat = 0
                else:
                    lat = 0 if (waw0_same_engine and ops[p].engine == ops[i].engine) else 1
                deps[i].append((p, lat))
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
    for i in range(n_ops):
        for d, latency in deps[i]:
            children[d].append((i, latency))
    return deps, children


def _reads_writes(op: Op) -> tuple[list[int], list[int]]:
    engine = op.engine
    slot = op.slot

    if engine == "alu":
        match slot:
            # Pseudo op emitted by generator/offload.py: an 8-lane vector op executed
            # on the ALU engine by consuming VLEN scalar slots in the same cycle.
            case ("alu_vec", _op, dest, a1, a2):
                return [*_vec_addrs(a1), *_vec_addrs(a2)], _vec_addrs(dest)
            case (_op, dest, a1, a2):
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


def _count_cycles(instrs: list[dict[str, list[Any]]]) -> int:
    cycles = 0
    for bundle in instrs:
        for engine, slots in bundle.items():
            if engine != "debug" and slots:
                cycles += 1
                break
    return cycles


def _schedule_ops_dep_once(
    ops: list[Op],
    return_ops: bool = False,
    *,
    seed: int = 0,
    jitter: float = 0.0,
    policy: str = "baseline",
    target_cycles: int | None = None,
) -> list[dict[str, list[Any]]]:
    n_ops = len(ops)
    reads_list: list[list[int]] = []
    writes_list: list[list[int]] = []
    for op in ops:
        reads, writes = _reads_writes(op)
        reads_list.append(reads)
        writes_list.append(writes)

    waw0_same_engine = False
    waw0_all = False
    deps_policy = policy
    # Policy suffix: allow same-engine WAW at 0 latency (deterministic within-slot order).
    if deps_policy.endswith("_waw0"):
        waw0_same_engine = True
        deps_policy = deps_policy[: -len("_waw0")]
    # Policy suffix: allow WAW at 0 latency across engines too. This requires
    # enforcing a per-cycle engine order consistent with those WAW edges.
    if deps_policy.endswith("_waw0all"):
        waw0_all = True
        deps_policy = deps_policy[: -len("_waw0all")]

    deps, children = _build_deps(ops, waw0_same_engine=waw0_same_engine, waw0_all=waw0_all)
    indegree = [len(deps[i]) for i in range(n_ops)]

    # Optional: compute ALAP latest-start times for slack scheduling.
    # latest[i] is the latest cycle we can schedule op i without exceeding
    # `target_cycles`, ignoring per-cycle engine caps and write conflicts.
    latest: list[int] | None = None
    if policy in {"slack", "global_greedy_slack"}:
        if target_cycles is None:
            raise ValueError("policy requires target_cycles")
        T = int(target_cycles)
        if T <= 0:
            raise ValueError("target_cycles must be positive")
        latest = [T - 1] * n_ops
        # Topological order (Kahn) for reverse propagation.
        topo: list[int] = []
        q = [i for i in range(n_ops) if indegree[i] == 0]
        # We'll rebuild indegree below for forward scheduling; keep a copy here.
        indeg2 = indegree[:]  # copy
        qi = 0
        while qi < len(q):
            i = q[qi]
            qi += 1
            topo.append(i)
            for c, _lat in children[i]:
                indeg2[c] -= 1
                if indeg2[c] == 0:
                    q.append(c)
        if len(topo) != n_ops:
            # Shouldn't happen, but avoid infinite loops if deps are cyclic.
            raise RuntimeError("dependency graph is not a DAG")
        for i in reversed(topo):
            if not children[i]:
                continue
            li = T - 1
            for c, lat in children[i]:
                li = min(li, latest[c] - lat)
            latest[i] = li

    # Critical-path depth (ignores engine caps; original heuristic).
    priority = [1] * n_ops
    for i in range(n_ops - 1, -1, -1):
        if children[i]:
            priority[i] = 1 + max(priority[c] for c, _ in children[i])

    # Bottleneck-aware signals (used when policy="bottleneck_valu").
    # valu_path[i]: max number of VALU ops on any path starting at i.
    # valu_kids[i]: number of immediate children that are VALU ops.
    valu_path = [1 if ops[i].engine == "valu" else 0 for i in range(n_ops)]
    valu_kids = [0] * n_ops
    for i in range(n_ops - 1, -1, -1):
        if not children[i]:
            continue
        vk = 0
        vbest = 0
        for c, _lat in children[i]:
            if ops[c].engine == "valu":
                vk += 1
            if valu_path[c] > vbest:
                vbest = valu_path[c]
        valu_kids[i] = vk
        if vbest:
            valu_path[i] += vbest

    earliest = [0] * n_ops
    scheduled = [-1] * n_ops
    # Heap items are (ready_cycle, k0, k1, k2, jitter, op_idx).
    ready: dict[str, list[tuple[int, int, int, int, float, int]]] = defaultdict(list)

    rng = random.Random(seed) if jitter > 0 else None

    def _jitter_key() -> float:
        if rng is None:
            return 0.0
        return rng.random() * jitter

    gang_alu = False
    gang_alu_opcodes: set[str] | None = None
    gang_offload = False
    base_policy = deps_policy
    # Optional suffixes:
    # - _gang_offload: gang only ALU lane ops produced by vector->scalar offload
    # - _gang_alu: gang any 8-lane ALU groups that share a meta dict
    # - _gang_alu_cmp: like _gang_alu but only for comparisons ("==", "<")
    #
    # These are scheduling-only constraints; they do not change the executed op stream.
    while True:
        if base_policy.endswith("_gang_offload"):
            gang_offload = True
            base_policy = base_policy[: -len("_gang_offload")]
            continue
        if base_policy.endswith("_gang_alu_cmp"):
            gang_alu = True
            gang_alu_opcodes = {"==", "<"}
            base_policy = base_policy[: -len("_gang_alu_cmp")]
            continue
        if base_policy.endswith("_gang_alu"):
            gang_alu = True
            gang_alu_opcodes = None
            base_policy = base_policy[: -len("_gang_alu")]
            continue
        break

    def _ready_key(i: int) -> tuple[int, int, int, float]:
        # Smaller tuples pop first.
        if base_policy == "baseline":
            return (-priority[i], 0, 0, _jitter_key())
        if base_policy == "valu_first":
            # Same per-engine prioritization as baseline; difference is in the
            # per-cycle engine packing order (see below).
            return (-priority[i], 0, 0, _jitter_key())
        if base_policy == "bottleneck_valu":
            # Keep CP pressure, but bias ops that unlock future VALU work.
            return (-priority[i], -valu_path[i], -valu_kids[i], _jitter_key())
        if base_policy == "global_greedy":
            # Same prioritization signals as bottleneck_valu, but a different
            # within-cycle packer (see below).
            return (-priority[i], -valu_path[i], -valu_kids[i], _jitter_key())
        if base_policy == "slack":
            assert latest is not None
            # Schedule ops with earlier deadlines first (min slack).
            # Tie-break by CP depth and VALU-unlock signals.
            return (latest[i], -priority[i], -valu_path[i], _jitter_key())
        if base_policy == "global_greedy_slack":
            assert latest is not None
            return (latest[i], -priority[i], -valu_path[i], _jitter_key())
        raise ValueError(f"unknown schedule policy {policy!r}")

    # Optional: gang-schedule ALU lane groups (8-lane ALU_VEC and offload expansions).
    # These appear in the op stream as 8 independent ALU ops sharing the same meta dict.
    # If the scheduler spreads lanes across cycles, dependents that read the full vector
    # get delayed until the last lane completes, increasing critical path length.
    gang_any = gang_alu or gang_offload
    alu_group_of: list[int] = [-1] * n_ops
    alu_groups: list[list[int]] = []
    if gang_any:
        by_meta: dict[int, list[int]] = defaultdict(list)
        for i, op in enumerate(ops):
            if op.engine != "alu" or op.meta is None:
                continue
            if gang_offload and not op.meta.get("offload", False):
                continue
            if gang_alu_opcodes is not None and op.slot[0] not in gang_alu_opcodes:
                continue
            by_meta[id(op.meta)].append(i)
        for _mid, members in by_meta.items():
            if len(members) != VLEN:
                continue
            # Verify this looks like an 8-lane op: same opcode, contiguous dests.
            op0 = ops[members[0]].slot[0]
            if gang_alu_opcodes is not None and op0 not in gang_alu_opcodes:
                continue
            dests = []
            ok = True
            for j in members:
                slot = ops[j].slot
                if slot[0] != op0:
                    ok = False
                    break
                dests.append(slot[1])
            if not ok:
                continue
            dests_sorted = sorted(dests)
            if dests_sorted[-1] - dests_sorted[0] != VLEN - 1:
                continue
            if len(set(dests_sorted)) != VLEN:
                continue
            g = len(alu_groups)
            alu_groups.append(list(members))
            for j in members:
                alu_group_of[j] = g

    for i, op in enumerate(ops):
        if indegree[i] == 0:
            if gang_any and op.engine == "alu" and alu_group_of[i] != -1:
                # Defer: push the group only once all members are ready.
                pass
            else:
                k0, k1, k2, kj = _ready_key(i)
                heapq.heappush(ready[op.engine], (0, k0, k1, k2, kj, i))

    alu_group_ready = [0] * len(alu_groups)
    if gang_any and alu_groups:
        for i, op in enumerate(ops):
            if op.engine != "alu":
                continue
            g = alu_group_of[i]
            if g == -1:
                continue
            if indegree[i] == 0:
                alu_group_ready[g] += 1
        for g, cnt in enumerate(alu_group_ready):
            if cnt != VLEN:
                continue
            # All lanes ready: push group handle as a negative index.
            members = alu_groups[g]
            rc = 0
            k0 = k1 = k2 = 0
            kj = 0.0
            # Use the best (smallest) key among members for prioritization.
            # All lanes should have similar priority anyway.
            best_key: tuple[int, int, int, float] | None = None
            for m in members:
                rc = max(rc, earliest[m])
                key = _ready_key(m)
                if best_key is None or key < best_key:
                    best_key = key
            if best_key is not None:
                k0, k1, k2, kj = best_key
            heapq.heappush(ready["alu"], (rc, k0, k1, k2, kj, -(g + 1)))

    engine_order_base = ("valu", "alu", "flow", "load", "store", "debug")
    engine_index = {eng: idx for idx, eng in enumerate(engine_order_base)}
    instrs: list[dict[str, list[tuple[Any, ...]]]] = []

    cycle = 0
    remaining = n_ops
    while remaining > 0:
        while len(instrs) <= cycle:
            instrs.append({})

        # Track which engine wrote each scratch address in this cycle.
        # If waw0_all is enabled, we'll enforce per-cycle engine ordering at the end
        # of the cycle instead of rejecting cross-engine WAW here.
        writes_cycle_owner: dict[int, str] = {}
        engine_counts: dict[str, int] = {}
        any_scheduled = False

        def release_children(idx: int) -> None:
            for child, latency in children[idx]:
                indegree[child] -= 1
                earliest[child] = max(earliest[child], scheduled[idx] + latency)
                if indegree[child] == 0:
                    child_engine = ops[child].engine
                    if gang_any and child_engine == "alu" and alu_group_of[child] != -1:
                        g = alu_group_of[child]
                        alu_group_ready[g] += 1
                        if alu_group_ready[g] == VLEN:
                            members = alu_groups[g]
                            rc = 0
                            best_key: tuple[int, int, int, float] | None = None
                            for m in members:
                                rc = max(rc, earliest[m])
                                key = _ready_key(m)
                                if best_key is None or key < best_key:
                                    best_key = key
                            k0 = k1 = k2 = 0
                            kj = 0.0
                            if best_key is not None:
                                k0, k1, k2, kj = best_key
                            heapq.heappush(ready["alu"], (rc, k0, k1, k2, kj, -(g + 1)))
                    else:
                        k0, k1, k2, kj = _ready_key(child)
                        heapq.heappush(
                            ready[child_engine],
                            (earliest[child], k0, k1, k2, kj, child),
                        )

        def _is_alu_group(engine: str, idx: int) -> bool:
            return gang_any and engine == "alu" and idx < 0

        def _members(engine: str, idx: int) -> list[int]:
            if _is_alu_group(engine, idx):
                return alu_groups[-idx - 1]
            return [idx]

        def _slot_cost(engine: str, idx: int) -> int:
            if _is_alu_group(engine, idx):
                return len(alu_groups[-idx - 1])
            if engine == "alu":
                # ALU pseudo vector op consumes VLEN scalar ALU slots in one cycle.
                if ops[idx].slot[0] == "alu_vec":
                    return VLEN
            return 1

        def _writes(engine: str, idx: int) -> list[int]:
            if _is_alu_group(engine, idx):
                out: list[int] = []
                for m in alu_groups[-idx - 1]:
                    out.extend(writes_list[m])
                return out
            return writes_list[idx]

        def _already_scheduled(engine: str, idx: int) -> bool:
            ms = _members(engine, idx)
            return scheduled[ms[0]] >= 0

        made_progress = True
        while made_progress:
            made_progress = False
            if base_policy in {"global_greedy", "global_greedy_slack"}:
                # Global greedy packer: pick ops across engines by a unified
                # priority key, subject to per-engine caps and same-cycle write
                # conflicts.
                #
                # This can outperform the per-engine greedy order when the
                # per-engine choice would schedule a low-value op that blocks
                # a higher-value op from another engine in the same cycle.
                PER_ENGINE_CAND = 8

                def pop_ready(engine: str) -> tuple[list[tuple[int, int, int, int, float, int]], list[tuple[int, int, int, int, float, int]]]:
                    heap = ready.get(engine)
                    if not heap:
                        return [], []
                    taken: list[tuple[int, int, int, int, float, int]] = []
                    skipped: list[tuple[int, int, int, int, float, int]] = []
                    while heap and len(taken) < PER_ENGINE_CAND:
                        item = heapq.heappop(heap)
                        if item[0] > cycle:
                            skipped.append(item)
                            break
                        taken.append(item)
                    return taken, skipped

                any_local = False
                # Keep packing until no engine can schedule anything else this cycle.
                while True:
                    candidates: list[tuple[int, int, int, int, float, int, str]] = []
                    stash: dict[str, list[tuple[int, int, int, int, float, int]]] = {}
                    stash2: dict[str, list[tuple[int, int, int, int, float, int]]] = {}
                    for eng in engine_order_base:
                        cap = SLOT_LIMITS[eng]
                        if cap <= 0:
                            continue
                        if engine_counts.get(eng, 0) >= cap:
                            continue
                        taken, skipped = pop_ready(eng)
                        if taken:
                            for it in taken:
                                candidates.append((*it, eng))
                            stash[eng] = taken
                        if skipped:
                            stash2[eng] = skipped

                    # Push back the "not yet ready" head items immediately.
                    for eng, items in stash2.items():
                        heap = ready.get(eng)
                        if heap is None:
                            ready[eng] = items
                        else:
                            for it in items:
                                heapq.heappush(heap, it)

                    if not candidates:
                        break

                    # Sort by our heap key (ready_cycle first, then k0/k1/k2/jitter),
                    # and prefer earlier engines for tie-break determinism.
                    candidates.sort(key=lambda x: (x[0], x[1], x[2], x[3], x[4], engine_index[x[6]]))

                    scheduled_any = False
                    for ready_cycle, k0, k1, k2, _j, idx, eng in candidates:
                        if ready_cycle > cycle:
                            continue
                        cap = SLOT_LIMITS[eng]
                        cost = _slot_cost(eng, idx)
                        if engine_counts.get(eng, 0) + cost > cap:
                            continue
                        ws = _writes(eng, idx)
                        if not waw0_all:
                            bad = False
                            for w in ws:
                                ow = writes_cycle_owner.get(w)
                                if ow is not None and ow != eng:
                                    bad = True
                                    break
                            if bad:
                                continue
                        ms = _members(eng, idx)
                        for m in ms:
                            op = ops[m]
                            if return_ops:
                                instrs[cycle].setdefault(eng, []).append(op)
                            else:
                                instrs[cycle].setdefault(eng, []).append(op.slot)
                            scheduled[m] = cycle
                        for w in ws:
                            writes_cycle_owner[w] = eng
                        remaining -= len(ms)
                        any_scheduled = True
                        scheduled_any = True
                        any_local = True
                        engine_counts[eng] = engine_counts.get(eng, 0) + cost
                        for m in ms:
                            release_children(m)

                    # Push back everything we popped but didn't schedule.
                    for eng, items in stash.items():
                        heap = ready.get(eng)
                        if heap is None:
                            ready[eng] = items
                        else:
                            for it in items:
                                # If it was scheduled, it won't be in indegree==0 anymore
                                # but we still have it in stash; filter by scheduled time.
                                idx = it[5]
                                if _already_scheduled(eng, idx):
                                    continue
                                heapq.heappush(heap, it)

                    if not scheduled_any:
                        break

                if any_local:
                    made_progress = True
                continue

            def engine_key(engine: str) -> tuple[int, int, int]:
                cap = SLOT_LIMITS[engine]
                if cap <= 0 or engine_counts.get(engine, 0) >= cap:
                    return (0, -1, -engine_index[engine])
                heap = ready.get(engine)
                if not heap:
                    return (0, -1, -engine_index[engine])
                ready_cycle = heap[0][0]
                if ready_cycle > cycle:
                    return (0, -1, -engine_index[engine])
                if base_policy == "slack":
                    # Prefer engines whose head op has the earliest deadline.
                    # heap[0][1] is (latest).
                    return (1, -(10**9 - heap[0][1]), -engine_index[engine])
                # Prefer engines whose top element is more critical by CP depth.
                # heap[0][1] is (-cp_depth).
                return (1, -heap[0][1], -engine_index[engine])

            if base_policy == "valu_first":
                # Always try to fill VALU before other engines. This can reduce
                # wasted VALU slots when other engines would otherwise schedule
                # WAW-conflicting ops earlier in the bundle.
                engine_order = list(engine_order_base)
            else:
                engine_order = sorted(
                    engine_order_base,
                    key=engine_key,
                    reverse=True,
                )

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
                skipped: list[tuple[int, int, int, int, float, int]] = []
                while heap and count < cap:
                    ready_cycle, k0, k1, k2, _j, idx = heapq.heappop(heap)
                    if ready_cycle > cycle:
                        skipped.append((ready_cycle, k0, k1, k2, _j, idx))
                        break
                    cost = _slot_cost(engine, idx)
                    if count + cost > cap:
                        skipped.append((ready_cycle, k0, k1, k2, _j, idx))
                        continue
                    ws = _writes(engine, idx)
                    if not waw0_all:
                        bad = False
                        for w in ws:
                            ow = writes_cycle_owner.get(w)
                            if ow is not None and ow != engine:
                                bad = True
                                break
                        if bad:
                            skipped.append((ready_cycle, k0, k1, k2, _j, idx))
                            continue
                    ms = _members(engine, idx)
                    for m in ms:
                        op = ops[m]
                        if return_ops:
                            instrs[cycle].setdefault(engine, []).append(op)
                        else:
                            instrs[cycle].setdefault(engine, []).append(op.slot)
                        scheduled[m] = cycle
                    for w in ws:
                        writes_cycle_owner[w] = engine
                    remaining -= len(ms)
                    any_scheduled = True
                    made_progress = True
                    count += cost
                    for m in ms:
                        release_children(m)
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

        if waw0_all:
            # Enforce a deterministic engine execution order consistent with any 0-lat edges
            # scheduled within this cycle. Without this, the simulator's dict iteration
            # order could invert same-cycle WAW edges across engines.
            bundle = instrs[cycle]
            engs = [e for e in engine_order_base if e in bundle]
            if len(engs) > 1:
                # Build engine-order constraints from 0-latency edges within the cycle.
                # Only 0-lat WAW matters here, but we conservatively include all 0-lat edges.
                edges: set[tuple[str, str]] = set()
                for i in range(n_ops):
                    if scheduled[i] != cycle:
                        continue
                    ei = ops[i].engine
                    for c, lat in children[i]:
                        if lat != 0:
                            continue
                        if scheduled[c] != cycle:
                            continue
                        ec = ops[c].engine
                        if ei != ec:
                            edges.add((ei, ec))

                if edges:
                    # Kahn topo sort on the small engine graph.
                    present = set(engs)
                    indeg = {e: 0 for e in present}
                    outs: dict[str, set[str]] = {e: set() for e in present}
                    for a, b in edges:
                        if a not in present or b not in present or a == b:
                            continue
                        if b not in outs[a]:
                            outs[a].add(b)
                            indeg[b] += 1
                    q = [e for e in engs if indeg.get(e, 0) == 0]
                    out_order: list[str] = []
                    qi = 0
                    while qi < len(q):
                        e = q[qi]
                        qi += 1
                        out_order.append(e)
                        for nb in sorted(outs.get(e, ())):
                            indeg[nb] -= 1
                            if indeg[nb] == 0:
                                q.append(nb)
                    if len(out_order) == len(present):
                        nb: dict[str, list[Any]] = {}
                        for e in out_order:
                            nb[e] = bundle[e]
                        instrs[cycle] = nb
                    # If cyclic, keep original order; schedule may still be valid if
                    # the cycle didn't include actual conflicting WAW across engines.

        cycle += 1

    return instrs


def schedule_ops_dep(
    ops: list[Op],
    return_ops: bool = False,
    *,
    seed: int = 0,
    jitter: float = 0.0,
    restarts: int = 1,
    compact: bool = False,
    policy: str = "baseline",
    target_cycles: int | None = None,
) -> list[dict[str, list[Any]]]:
    restarts = max(1, int(restarts))
    if restarts == 1 or jitter <= 0.0:
        instrs = _schedule_ops_dep_once(
            ops, return_ops=True, seed=seed, jitter=jitter, policy=policy, target_cycles=target_cycles
        )
        if compact:
            instrs = _compact_schedule(ops, instrs)
        if not return_ops:
            instrs = _strip_ops(instrs)
        return instrs

    best_instrs: list[dict[str, list[Any]]] | None = None
    best_cycles: int | None = None
    for k in range(restarts):
        instrs_k = _schedule_ops_dep_once(
            ops, return_ops=True, seed=seed + k, jitter=jitter, policy=policy, target_cycles=target_cycles
        )
        if compact:
            instrs_k = _compact_schedule(ops, instrs_k)
        cycles = _count_cycles(_strip_ops(instrs_k))
        if best_cycles is None or cycles < best_cycles:
            best_cycles = cycles
            best_instrs = instrs_k
            if target_cycles is not None and best_cycles <= int(target_cycles):
                break
    if not best_instrs:
        return []
    if not return_ops:
        return _strip_ops(best_instrs)
    return best_instrs


def _strip_ops(instrs: list[dict[str, list[Any]]]) -> list[dict[str, list[Any]]]:
    out: list[dict[str, list[Any]]] = []
    for bundle in instrs:
        nb: dict[str, list[Any]] = {}
        for eng, slots in bundle.items():
            if not slots:
                continue
            first = slots[0]
            # Expand pseudo ALU vector ops into scalar ALU slots for the simulator.
            if isinstance(first, Op):
                out_slots: list[Any] = []
                for op in slots:  # type: ignore[assignment]
                    if not isinstance(op, Op):
                        raise TypeError("mixed slot types in schedule")
                    slot = op.slot
                    if eng == "alu" and isinstance(slot, tuple) and slot and slot[0] == "alu_vec":
                        _, op_name, dest, a, b = slot
                        for lane in range(VLEN):
                            out_slots.append((op_name, dest + lane, a + lane, b + lane))
                    else:
                        out_slots.append(slot)
                nb[eng] = out_slots
            else:
                out_slots2: list[Any] = []
                for slot in slots:
                    if eng == "alu" and isinstance(slot, tuple) and slot and slot[0] == "alu_vec":
                        _, op_name, dest, a, b = slot
                        for lane in range(VLEN):
                            out_slots2.append((op_name, dest + lane, a + lane, b + lane))
                    else:
                        out_slots2.append(slot)
                nb[eng] = out_slots2
        out.append(nb)
    return out


def _compact_schedule(ops: list[Op], instrs_ops: list[dict[str, list[Any]]]) -> list[dict[str, list[Op]]]:
    """
    Greedy "pull left" compaction pass over an existing schedule.

    This only moves ops earlier; it never violates deps, per-engine caps, or
    same-cycle write conflicts (which are undefined in the machine semantics).
    """
    # Map op object -> original index
    op_to_idx: dict[int, int] = {id(op): i for i, op in enumerate(ops)}

    # Build current schedule times
    t: list[int] = [-1] * len(ops)
    for cycle, bundle in enumerate(instrs_ops):
        for eng, slots in bundle.items():
            for op in slots:
                if not isinstance(op, Op):
                    raise TypeError("compact requires return_ops=True schedule")
                idx = op_to_idx.get(id(op))
                if idx is None:
                    continue
                t[idx] = cycle
    # Some ops may be absent if scheduler returned empty; ignore.

    deps, children = _build_deps(ops)
    writes_list = [_reads_writes(op)[1] for op in ops]

    def _op_cost(op: Op) -> int:
        if op.engine == "alu" and isinstance(op.slot, tuple) and op.slot and op.slot[0] == "alu_vec":
            return VLEN
        return 1

    # Per-cycle resource + write usage
    max_cycle = max((x for x in t if x >= 0), default=-1)
    engine_counts: list[dict[str, int]] = [defaultdict(int) for _ in range(max_cycle + 1)]
    writes_count: list[dict[int, int]] = [defaultdict(int) for _ in range(max_cycle + 1)]
    for i, ti in enumerate(t):
        if ti < 0:
            continue
        eng = ops[i].engine
        engine_counts[ti][eng] += _op_cost(ops[i])
        for w in writes_list[i]:
            writes_count[ti][w] += 1

    def can_place(i: int, c: int) -> bool:
        eng = ops[i].engine
        if engine_counts[c].get(eng, 0) + _op_cost(ops[i]) > SLOT_LIMITS[eng]:
            return False
        ws = writes_list[i]
        if any(writes_count[c].get(w, 0) > 0 for w in ws):
            return False
        return True

    def earliest_cycle(i: int) -> int:
        e = 0
        for p, lat in deps[i]:
            tp = t[p]
            if tp < 0:
                continue
            e = max(e, tp + lat)
        return e

    # Move ops in descending time so we shrink the tail first.
    order = sorted([i for i, ti in enumerate(t) if ti >= 0], key=lambda i: t[i], reverse=True)
    for i in order:
        cur = t[i]
        e = earliest_cycle(i)
        if e >= cur:
            continue
        # Try to pull as far left as possible.
        for c in range(e, cur):
            if not can_place(i, c):
                continue
            # Move i from cur -> c
            eng = ops[i].engine
            engine_counts[cur][eng] -= _op_cost(ops[i])
            if engine_counts[cur][eng] <= 0:
                engine_counts[cur].pop(eng, None)
            for w in writes_list[i]:
                writes_count[cur][w] -= 1
                if writes_count[cur][w] <= 0:
                    writes_count[cur].pop(w, None)
            engine_counts[c][eng] += _op_cost(ops[i])
            for w in writes_list[i]:
                writes_count[c][w] += 1
            t[i] = c
            break

    # Rebuild bundles from new times.
    new_max = max(t)
    out: list[dict[str, list[Op]]] = [defaultdict(list) for _ in range(new_max + 1)]  # type: ignore[list-item]
    for i, ti in enumerate(t):
        if ti < 0:
            continue
        out[ti][ops[i].engine].append(ops[i])
    # Convert defaultdicts to dicts
    return [dict(b) for b in out]
