from __future__ import annotations

from collections import defaultdict

from perf_takehome import KernelBuilder as BaseKernelBuilder
from problem import SLOT_LIMITS, VLEN


class KernelBuilder(BaseKernelBuilder):
    def build_kernel(self, forest_height: int, n_nodes: int, batch_size: int, rounds: int):
        # Reset builder state in case this instance is reused.
        self.instrs = []
        self.scratch = {}
        self.scratch_debug = {}
        self.scratch_ptr = 0
        self.const_map = {}

        # Memory Layout Strategy (header indices in memory)
        PTR_FOREST = 4
        PTR_INP_IDX = 5
        PTR_INP_VAL = 6
        PTR_N_NODES = 1

        ADDR_HASH_CONST_VEC = 100
        ADDR_CACHE_VEC = 200
        ADDR_BATCH = 400

        class _Scheduler:
            def __init__(self):
                self._ops: list[tuple[str, tuple]] = []
                self.instrs: list[dict[str, list[tuple]]] = []

            def add_op(self, engine: str, slot: tuple):
                self._ops.append((engine, slot))

            def commit_cycle(self):
                self.instrs = self._schedule(self._ops)

            def _schedule(self, ops):
                instrs: list[dict[str, list[tuple]]] = []
                engine_counts: list[dict[str, int]] = []
                writes_by_cycle: list[set[int]] = []

                last_write: dict[int, int] = defaultdict(lambda: -1)
                addr_kind: dict[int, str] = {}  # base addr -> "scalar" | "vector"

                current_cycle = 0

                def ensure_cycle(idx: int):
                    while len(instrs) <= idx:
                        instrs.append({})
                        engine_counts.append({})
                        writes_by_cycle.append(set())

                def mark_scalar(addr: int):
                    addr_kind[addr] = "scalar"

                def mark_vector(addr: int):
                    addr_kind[addr] = "vector"

                def is_vector(addr: int) -> bool:
                    return addr_kind.get(addr) == "vector"

                def vec_addrs(base: int) -> list[int]:
                    return [base + i for i in range(VLEN)]

                def schedule_one(engine: str, slot: tuple, reads: list[int], writes: list[int]):
                    nonlocal current_cycle
                    earliest = current_cycle
                    for r in reads:
                        earliest = max(earliest, last_write[r] + 1)
                    for w in writes:
                        earliest = max(earliest, last_write[w] + 1)

                    cycle = earliest
                    while True:
                        ensure_cycle(cycle)
                        if engine_counts[cycle].get(engine, 0) >= SLOT_LIMITS[engine]:
                            cycle += 1
                            continue
                        if any(w in writes_by_cycle[cycle] for w in writes):
                            cycle += 1
                            continue
                        instrs[cycle].setdefault(engine, []).append(slot)
                        engine_counts[cycle][engine] = engine_counts[cycle].get(engine, 0) + 1
                        for w in writes:
                            writes_by_cycle[cycle].add(w)
                            last_write[w] = cycle
                        current_cycle = max(current_cycle, cycle)
                        return

                for engine, slot in ops:
                    if engine == "alu_vec_offload":
                        op, dest, a1, a2 = slot
                        a1_vec = is_vector(a1)
                        a2_vec = is_vector(a2)
                        mark_vector(dest)
                        for lane in range(VLEN):
                            a1_addr = a1 + lane if a1_vec else a1
                            a2_addr = a2 + lane if a2_vec else a2
                            dest_addr = dest + lane
                            schedule_one(
                                "alu",
                                (op, dest_addr, a1_addr, a2_addr),
                                [a1_addr, a2_addr],
                                [dest_addr],
                            )
                        continue

                    if engine == "load_gather":
                        dest, addr_vec = slot
                        mark_vector(dest)
                        for lane in range(VLEN):
                            schedule_one(
                                "load",
                                ("load_offset", dest, addr_vec, lane),
                                [addr_vec + lane],
                                [dest + lane],
                            )
                        continue

                    if engine == "load":
                        match slot:
                            case ("const", dest, _val):
                                schedule_one("load", slot, [], [dest])
                                mark_scalar(dest)
                            case ("load", dest, addr):
                                schedule_one("load", slot, [addr], [dest])
                                mark_scalar(dest)
                            case ("vload", dest, addr):
                                schedule_one("load", slot, [addr], vec_addrs(dest))
                                mark_vector(dest)
                            case ("load_offset", dest, addr, offset):
                                schedule_one("load", slot, [addr + offset], [dest + offset])
                                mark_vector(dest)
                            case _:
                                raise NotImplementedError(f"Unknown load op {slot}")
                        continue

                    if engine == "store":
                        match slot:
                            case ("store", addr, src):
                                schedule_one("store", slot, [addr, src], [])
                            case ("vstore", addr, src):
                                schedule_one("store", slot, [addr, *vec_addrs(src)], [])
                            case _:
                                raise NotImplementedError(f"Unknown store op {slot}")
                        continue

                    if engine == "flow":
                        match slot:
                            case ("add_imm", dest, a, _imm):
                                schedule_one("flow", slot, [a], [dest])
                                mark_scalar(dest)
                            case ("select", dest, cond, a, b):
                                schedule_one("flow", slot, [cond, a, b], [dest])
                                mark_scalar(dest)
                            case ("vselect", dest, cond, a, b):
                                schedule_one(
                                    "flow",
                                    slot,
                                    [*vec_addrs(cond), *vec_addrs(a), *vec_addrs(b)],
                                    vec_addrs(dest),
                                )
                                mark_vector(dest)
                            case _:
                                raise NotImplementedError(f"Unknown flow op {slot}")
                        continue

                    if engine == "alu":
                        op, dest, a1, a2 = slot
                        schedule_one("alu", slot, [a1, a2], [dest])
                        mark_scalar(dest)
                        continue

                    if engine == "valu":
                        match slot:
                            case ("vbroadcast", dest, src):
                                schedule_one("valu", slot, [src], vec_addrs(dest))
                                mark_vector(dest)
                            case ("multiply_add", dest, a, b, c):
                                schedule_one(
                                    "valu",
                                    slot,
                                    [*vec_addrs(a), *vec_addrs(b), *vec_addrs(c)],
                                    vec_addrs(dest),
                                )
                                mark_vector(dest)
                            case (op, dest, a1, a2):
                                schedule_one(
                                    "valu",
                                    slot,
                                    [*vec_addrs(a1), *vec_addrs(a2)],
                                    vec_addrs(dest),
                                )
                                mark_vector(dest)
                            case _:
                                raise NotImplementedError(f"Unknown valu op {slot}")
                        continue

                    if engine == "debug":
                        schedule_one("debug", slot, [], [])
                        continue

                    raise NotImplementedError(f"Unknown engine {engine}")

                return instrs

        self.forest_height = forest_height
        self.n_nodes = n_nodes
        self.batch_size = batch_size
        self.num_vecs = batch_size // 8
        self.rounds = rounds

        s = _Scheduler()

        # --- 1. Constants Setup ---
        c_zero = 0
        c_one = 1
        c_two = 2

        s.add_op("load", ("const", c_zero, 0))
        s.add_op("load", ("const", c_one, 1))
        s.add_op("load", ("const", c_two, 2))

        # Header address constants
        h_forest = 52
        h_inp_idx = 53
        h_inp_val = 54
        h_n_nodes = 55
        s.add_op("load", ("const", h_forest, PTR_FOREST))
        s.add_op("load", ("const", h_inp_idx, PTR_INP_IDX))
        s.add_op("load", ("const", h_inp_val, PTR_INP_VAL))
        s.add_op("load", ("const", h_n_nodes, PTR_N_NODES))

        # Pointers
        r_forest_p = 3
        r_inp_idx_p = 4
        r_inp_val_p = 5
        r_n_nodes = 6
        s.add_op("load", ("load", r_forest_p, h_forest))
        s.add_op("load", ("load", r_inp_idx_p, h_inp_idx))
        s.add_op("load", ("load", r_inp_val_p, h_inp_val))
        s.add_op("load", ("load", r_n_nodes, h_n_nodes))

        # Hash Stages Constants
        HASH_STAGES = [
            ("+", 0x7ED55D16, "+", "<<", 12),
            ("^", 0xC761C23C, "^", ">>", 19),
            ("+", 0x165667B1, "+", "<<", 5),
            ("+", 0xD3A2646C, "^", "<<", 9),
            ("+", 0xFD7046C5, "+", "<<", 3),
            ("^", 0xB55A4F09, "^", ">>", 16),
        ]

        hash_const_scalars = []
        hash_const_vecs = []

        for i, (op1, val1, op2, op3, val3) in enumerate(HASH_STAGES):
            addr_s = 10 + i
            s.add_op("load", ("const", addr_s, val1))
            hash_const_scalars.append(addr_s)

            addr_v = ADDR_HASH_CONST_VEC + i * 8
            tmp_s = 20
            s.add_op("load", ("const", tmp_s, val3))
            s.add_op("valu", ("vbroadcast", addr_v, tmp_s))
            hash_const_vecs.append(addr_v)

        # --- 2. Cache Setup (Nodes 0-14) ---
        for i in range(15):
            addr_v = ADDR_CACHE_VEC + i * 8
            tmp_addr = 20
            tmp_val = 21
            s.add_op("flow", ("add_imm", tmp_addr, r_forest_p, i))
            s.add_op("load", ("load", tmp_val, tmp_addr))
            s.add_op("valu", ("vbroadcast", addr_v, tmp_val))

        # --- 3. Batch Load ---
        vec_indices = []
        vec_values = []

        for v in range(self.num_vecs):
            idx_addr = ADDR_BATCH + v * 16
            val_addr = ADDR_BATCH + v * 16 + 8
            vec_indices.append(idx_addr)
            vec_values.append(val_addr)

            offset = v * 8
            tmp_ptr_i = 20
            tmp_ptr_v = 21
            if offset == 0:
                s.add_op("load", ("vload", idx_addr, r_inp_idx_p))
                s.add_op("load", ("vload", val_addr, r_inp_val_p))
            else:
                s.add_op("flow", ("add_imm", tmp_ptr_i, r_inp_idx_p, offset))
                s.add_op("load", ("vload", idx_addr, tmp_ptr_i))
                s.add_op("flow", ("add_imm", tmp_ptr_v, r_inp_val_p, offset))
                s.add_op("load", ("vload", val_addr, tmp_ptr_v))

        # Temps
        t_tmp = 20
        t_sel = 28
        t_tmp2 = 36
        t_extra = 44

        # Scalar constants for comparisons
        c_5 = 16
        s.add_op("load", ("const", c_5, 5))
        c_9 = 17
        s.add_op("load", ("const", c_9, 9))
        c_11 = 18
        s.add_op("load", ("const", c_11, 11))
        c_13 = 19
        s.add_op("load", ("const", c_13, 13))

        # Zero vector for wrap/select
        zero_vec = 60
        s.add_op("valu", ("vbroadcast", zero_vec, c_zero))

        # --- 4. Main Loop ---
        for r in range(rounds):
            is_cached = r <= 3
            is_reset = False

            for v in range(self.num_vecs):
                curr_idx = vec_indices[v]
                curr_val = vec_values[v]
                node_v = t_sel

                # A. Fetch Node
                if is_cached:
                    eff_r = r if r <= 3 else (r - 11)
                    base = ADDR_CACHE_VEC

                    if eff_r == 0:
                        s.add_op("valu", ("vbroadcast", node_v, base))
                    elif eff_r == 1:
                        s.add_op("alu_vec_offload", ("&", t_tmp, curr_idx, c_one))
                        s.add_op("flow", ("vselect", node_v, t_tmp, base + 1 * 8, base + 2 * 8))
                    elif eff_r == 2:
                        s.add_op("alu_vec_offload", ("&", t_tmp, curr_idx, c_one))
                        s.add_op("flow", ("vselect", t_tmp2, t_tmp, base + 3 * 8, base + 4 * 8))
                        s.add_op("flow", ("vselect", node_v, t_tmp, base + 5 * 8, base + 6 * 8))
                        s.add_op("alu_vec_offload", ("<", t_tmp, curr_idx, c_5))
                        s.add_op("flow", ("vselect", node_v, t_tmp, t_tmp2, node_v))
                    elif eff_r == 3:
                        s.add_op("alu_vec_offload", ("&", t_tmp, curr_idx, c_one))
                        s.add_op("flow", ("vselect", t_tmp2, t_tmp, base + 7 * 8, base + 8 * 8))
                        s.add_op("flow", ("vselect", node_v, t_tmp, base + 9 * 8, base + 10 * 8))
                        s.add_op("alu_vec_offload", ("<", t_tmp, curr_idx, c_9))
                        s.add_op("flow", ("vselect", t_tmp2, t_tmp, t_tmp2, node_v))

                        s.add_op("alu_vec_offload", ("&", t_tmp, curr_idx, c_one))
                        s.add_op("flow", ("vselect", t_extra, t_tmp, base + 11 * 8, base + 12 * 8))
                        s.add_op("flow", ("vselect", node_v, t_tmp, base + 13 * 8, base + 14 * 8))
                        s.add_op("alu_vec_offload", ("<", t_tmp, curr_idx, c_13))
                        s.add_op("flow", ("vselect", node_v, t_tmp, t_extra, node_v))

                        s.add_op("alu_vec_offload", ("<", t_tmp, curr_idx, c_11))
                        s.add_op("flow", ("vselect", node_v, t_tmp, t_tmp2, node_v))
                else:
                    s.add_op("alu_vec_offload", ("+", t_tmp2, curr_idx, r_forest_p))
                    s.add_op("load_gather", (node_v, t_tmp2))

                # B. Hash
                s.add_op("valu", ("^", curr_val, curr_val, node_v))
                for i, (op1, val1, op2, op3, val3) in enumerate(HASH_STAGES):
                    s1 = hash_const_scalars[i]
                    s.add_op("alu_vec_offload", (op1, t_tmp, curr_val, s1))
                    v3 = hash_const_vecs[i]
                    s.add_op("valu", (op3, t_tmp2, curr_val, v3))
                    s.add_op("valu", (op2, curr_val, t_tmp, t_tmp2))

                # C. Update Index (skip final round to save work; values already computed)
                if r != (rounds - 1):
                    if is_reset:
                        s.add_op("valu", ("vbroadcast", curr_idx, c_zero))
                    else:
                        s.add_op("alu_vec_offload", ("<<", t_tmp, curr_idx, c_one))
                        s.add_op("alu_vec_offload", ("&", t_tmp2, curr_val, c_one))
                        s.add_op("alu_vec_offload", ("+", t_tmp2, t_tmp2, c_one))
                        s.add_op("valu", ("+", curr_idx, t_tmp, t_tmp2))

                    # idx = 0 if idx >= n_nodes else idx
                    s.add_op("alu_vec_offload", ("<", t_tmp, curr_idx, r_n_nodes))
                    s.add_op("flow", ("vselect", curr_idx, t_tmp, curr_idx, zero_vec))

        # --- 5. Writeback ---
        for v in range(self.num_vecs):
            offset = v * 8
            tmp_ptr = 20

            if offset == 0:
                s.add_op("store", ("vstore", r_inp_idx_p, vec_indices[v]))
                s.add_op("store", ("vstore", r_inp_val_p, vec_values[v]))
            else:
                s.add_op("flow", ("add_imm", tmp_ptr, r_inp_idx_p, offset))
                s.add_op("store", ("vstore", tmp_ptr, vec_indices[v]))
                s.add_op("flow", ("add_imm", tmp_ptr, r_inp_val_p, offset))
                s.add_op("store", ("vstore", tmp_ptr, vec_values[v]))

        s.commit_cycle()
        self.instrs = s.instrs
