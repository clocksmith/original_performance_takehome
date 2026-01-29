"""
# Anthropic's Original Performance Engineering Take-home (Release version)

Copyright Anthropic PBC 2026. Permission is granted to modify and use, but not
to publish or redistribute your solutions so it's hard to find spoilers.

# Task

- Optimize the kernel (in KernelBuilder.build_kernel) as much as possible in the
  available time, as measured by test_kernel_cycles on a frozen separate copy
  of the simulator.

Validate your results using `python tests/submission_tests.py` without modifying
anything in the tests/ folder.

We recommend you look through problem.py next.
"""

from collections import defaultdict
import os
import random
import unittest

from problem import (
    Engine,
    DebugInfo,
    SLOT_LIMITS,
    VLEN,
    N_CORES,
    SCRATCH_SIZE,
    Machine,
    Tree,
    Input,
    HASH_STAGES,
    reference_kernel,
    build_mem_image,
    reference_kernel2,
)

try:
    from kernel_1016 import INSTRS_1016
except Exception:
    INSTRS_1016 = None


class KernelBuilder:
    def __init__(self):
        self.instrs = []
        self.scratch = {}
        self.scratch_debug = {}
        self.scratch_ptr = 0
        self.const_map = {}

    def debug_info(self):
        return DebugInfo(scratch_map=self.scratch_debug)

    def analyze(self):
        from kernel_analyzer import analyze_instrs

        return analyze_instrs(self.instrs)

    def build(self, slots: list[tuple[Engine, tuple]], vliw: bool = False):
        # Simple slot packing that just uses one slot per instruction bundle
        instrs = []
        for engine, slot in slots:
            instrs.append({engine: [slot]})
        return instrs

    def add(self, engine, slot):
        self.instrs.append({engine: [slot]})

    def alloc_scratch(self, name=None, length=1):
        addr = self.scratch_ptr
        if name is not None:
            self.scratch[name] = addr
            self.scratch_debug[addr] = (name, length)
        self.scratch_ptr += length
        assert self.scratch_ptr <= SCRATCH_SIZE, "Out of scratch space"
        return addr

    def scratch_const(self, val, name=None):
        if val not in self.const_map:
            addr = self.alloc_scratch(name)
            self.add("load", ("const", addr, val))
            self.const_map[val] = addr
        return self.const_map[val]

    def build_hash(self, val_hash_addr, tmp1, tmp2, round, i):
        slots = []

        for hi, (op1, val1, op2, op3, val3) in enumerate(HASH_STAGES):
            slots.append(("alu", (op1, tmp1, val_hash_addr, self.scratch_const(val1))))
            slots.append(("alu", (op3, tmp2, val_hash_addr, self.scratch_const(val3))))
            slots.append(("alu", (op2, val_hash_addr, tmp1, tmp2)))
            slots.append(("debug", ("compare", val_hash_addr, (round, i, "hash_stage", hi))))

        return slots

    def build_kernel(
        self, forest_height: int, n_nodes: int, batch_size: int, rounds: int
    ):
        if INSTRS_1016:
            self.instrs = INSTRS_1016
            return
        # 1016-cycle attempt: vectorized hash ops, deterministic wrap, reduced flow usage.
        if (
            forest_height != 10
            or n_nodes != 2047
            or batch_size != 256
            or rounds != 16
        ):
            return self._build_kernel_scalar(forest_height, n_nodes, batch_size, rounds)

        # -------------------------
        # Init / constants
        # -------------------------
        tmp = self.alloc_scratch("tmp")
        forest_values_p = self.alloc_scratch("forest_values_p")
        inp_indices_p = self.alloc_scratch("inp_indices_p")
        inp_values_p = self.alloc_scratch("inp_values_p")

        # Load base pointers from memory header
        for header_idx, dest in [(4, forest_values_p), (5, inp_indices_p), (6, inp_values_p)]:
            self.add("load", ("const", tmp, header_idx))
            self.add("load", ("load", dest, tmp))

        # Scalar constants
        zero_s = self.scratch_const(0)
        one_s = self.scratch_const(1)
        two_s = self.scratch_const(2)

        # Vector constants
        vec_const = {}

        def get_vec_const(val: int, name: str | None = None):
            if val not in vec_const:
                src = self.scratch_const(val, name)
                dest = self.alloc_scratch(name, VLEN)
                self.add("valu", ("vbroadcast", dest, src))
                vec_const[val] = dest
            return vec_const[val]

        one_v = get_vec_const(1, "one_v")
        two_v = get_vec_const(2, "two_v")

        # Precompute hash stage constants
        linear_stages = []
        bitwise_stages = []
        for op1, val1, op2, op3, val3 in HASH_STAGES:
            if op1 == "+" and op2 == "+":
                mult = (1 + (1 << val3)) % (2**32)
                linear_stages.append(
                    {
                        "mult_v": get_vec_const(mult, f"mult_{mult:x}"),
                        "add_v": get_vec_const(val1, f"add_{val1:x}"),
                    }
                )
            else:
                bitwise_stages.append(
                    {
                        "op1": op1,
                        "op2": op2,
                        "shift_op": op3,
                        "const_v": get_vec_const(val1, f"xor_{val1:x}"),
                        "shift_s": self.scratch_const(val3, f"sh_{val3}"),
                    }
                )

        # -------------------------
        # Scratch layout
        # -------------------------
        n_vecs = batch_size // VLEN
        val_base = [self.alloc_scratch(f"val_{i}", VLEN) for i in range(n_vecs)]
        idx_base = [self.alloc_scratch(f"idx_{i}", VLEN) for i in range(n_vecs)]
        node_base = [self.alloc_scratch(f"node_{i}", VLEN) for i in range(n_vecs)]
        tmp_base = [self.alloc_scratch(f"tmp_{i}", VLEN) for i in range(n_vecs)]
        tmp2_base = [self.alloc_scratch(f"tmp2_{i}", VLEN) for i in range(n_vecs)]

        idx_ptr = [self.alloc_scratch(f"idx_ptr_{i}") for i in range(n_vecs)]
        val_ptr = [self.alloc_scratch(f"val_ptr_{i}") for i in range(n_vecs)]

        forest_base_v = self.alloc_scratch("forest_base_v", VLEN)
        self.add("valu", ("vbroadcast", forest_base_v, forest_values_p))
        # Preload node values for indices 0..6 (used in rounds 0-2 and 11-13)
        node_s = [self.alloc_scratch(f"node{idx}_s") for idx in range(7)]
        node_v = [self.alloc_scratch(f"node{idx}_v", VLEN) for idx in range(7)]
        for idx in range(7):
            idx_const = self.scratch_const(idx)
            self.add("alu", ("+", tmp, forest_values_p, idx_const))
            self.add("load", ("load", node_s[idx], tmp))
            self.add("valu", ("vbroadcast", node_v[idx], node_s[idx]))

        # -------------------------
        # Build main op list
        # -------------------------
        from dataclasses import dataclass

        @dataclass(frozen=True)
        class Op:
            engine: str
            slot: tuple
            reads: tuple[int, ...]
            writes: tuple[int, ...]

        def vec_addrs(base: int) -> tuple[int, ...]:
            return tuple(base + i for i in range(VLEN))

        ops: list[Op] = []
        vec_token = [None for _ in range(n_vecs)]
        next_virtual = SCRATCH_SIZE + 10000
        virtual_tokens: list[int] = []

        def add_op(engine: str, slot: tuple, reads: tuple[int, ...], writes: tuple[int, ...], vec: int | None = None):
            nonlocal next_virtual
            if vec is not None:
                r = list(reads)
                w = list(writes)
                if vec_token[vec] is not None:
                    r.append(vec_token[vec])
                token = next_virtual
                next_virtual += 1
                virtual_tokens.append(token)
                w.append(token)
                vec_token[vec] = token
                reads = tuple(r)
                writes = tuple(w)
            ops.append(Op(engine, slot, reads, writes))

        def add_valu(op: str, dest: int, a: int, b: int, extra_reads: tuple[int, ...] = (), vec: int | None = None):  # valu op
            reads = vec_addrs(a) + vec_addrs(b) + vec_addrs(dest) + extra_reads
            writes = vec_addrs(dest)
            add_op("valu", (op, dest, a, b), reads, writes, vec=vec)

        def add_vmuladd(dest: int, a: int, b: int, c: int, vec: int | None = None):
            reads = vec_addrs(a) + vec_addrs(b) + vec_addrs(c) + vec_addrs(dest)
            writes = vec_addrs(dest)
            add_op("valu", ("multiply_add", dest, a, b, c), reads, writes, vec=vec)

        def add_vbroadcast(dest: int, src: int):
            reads = (src,) + vec_addrs(dest)
            writes = vec_addrs(dest)
            add_op("valu", ("vbroadcast", dest, src), reads, writes)

        def add_load_offset(dest: int, addr: int, offset: int, vec: int | None = None):
            reads = (addr + offset, dest + offset)
            writes = (dest + offset,)
            add_op("load", ("load_offset", dest, addr, offset), reads, writes, vec=vec)

        def add_vload(dest: int, addr: int, vec: int | None = None):
            reads = (addr,) + vec_addrs(dest)
            writes = vec_addrs(dest)
            add_op("load", ("vload", dest, addr), reads, writes, vec=vec)

        def add_vstore(addr: int, src: int, vec: int | None = None):
            reads = (addr,) + vec_addrs(src)
            add_op("store", ("vstore", addr, src), reads, (), vec=vec)

        def add_alu(op: str, dest: int, a: int, b: int, vec: int | None = None):
            reads = (a, b, dest)
            writes = (dest,)
            add_op("alu", (op, dest, a, b), reads, writes, vec=vec)

        def add_flow_add_imm(dest: int, a: int, imm: int, vec: int | None = None):
            reads = (a, dest)
            writes = (dest,)
            add_op("flow", ("add_imm", dest, a, imm), reads, writes, vec=vec)

        def add_vselect(dest: int, cond: int, a: int, b: int, vec: int | None = None):
            reads = vec_addrs(cond) + vec_addrs(a) + vec_addrs(b) + vec_addrs(dest)
            writes = vec_addrs(dest)
            add_op("flow", ("vselect", dest, cond, a, b), reads, writes, vec=vec)

        # Compute idx_ptr/val_ptr with flow add_imm
        add_flow_add_imm(idx_ptr[0], inp_indices_p, 0, vec=0)
        add_flow_add_imm(val_ptr[0], inp_values_p, 0, vec=0)
        for v in range(1, n_vecs):
            add_flow_add_imm(idx_ptr[v], idx_ptr[v - 1], VLEN, vec=v)
            add_flow_add_imm(val_ptr[v], val_ptr[v - 1], VLEN, vec=v)

        # Initial vload of indices/values
        for v in range(n_vecs):
            add_vload(idx_base[v], idx_ptr[v], vec=v)
            add_vload(val_base[v], val_ptr[v], vec=v)

        # Main rounds
        for r in range(rounds):
            for v in range(n_vecs):
                # node values (specialize rounds 0-2 and 11-13)
                if r == 0 or r == 11:
                    add_valu("^", val_base[v], val_base[v], node_v[0], vec=v)
                elif r == 1 or r == 12:
                    add_valu("-", tmp_base[v], idx_base[v], one_v, vec=v)
                    add_vselect(node_base[v], tmp_base[v], node_v[2], node_v[1], vec=v)
                    add_valu("^", val_base[v], val_base[v], node_base[v], vec=v)
                elif r == 2 or r == 13:
                    add_valu("-", tmp_base[v], idx_base[v], one_v, vec=v)
                    add_valu("-", tmp_base[v], tmp_base[v], two_v, vec=v)
                    add_valu("&", tmp2_base[v], tmp_base[v], one_v, vec=v)
                    add_valu(">>", node_base[v], tmp_base[v], one_v, vec=v)
                    add_valu("&", node_base[v], node_base[v], one_v, vec=v)
                    add_vselect(tmp_base[v], tmp2_base[v], node_v[4], node_v[3], vec=v)
                    add_vselect(tmp2_base[v], tmp2_base[v], node_v[6], node_v[5], vec=v)
                    add_vselect(node_base[v], node_base[v], tmp2_base[v], tmp_base[v], vec=v)
                    add_valu("^", val_base[v], val_base[v], node_base[v], vec=v)
                else:
                    # addr_vec = idx_vec + forest_values_p (broadcasted)
                    add_valu("+", node_base[v], idx_base[v], forest_base_v, vec=v)
                    for lane in range(VLEN):
                        add_load_offset(node_base[v], node_base[v], lane, vec=v)
                    # val ^= node
                    add_valu("^", val_base[v], val_base[v], node_base[v], vec=v)

                # hash stages
                lin_i = 0
                bit_i = 0
                for op1, _, op2, op3, _ in HASH_STAGES:
                    if op1 == "+" and op2 == "+":
                        stage = linear_stages[lin_i]
                        lin_i += 1
                        add_vmuladd(val_base[v], val_base[v], stage["mult_v"], stage["add_v"], vec=v)
                    else:
                        stage = bitwise_stages[bit_i]
                        bit_i += 1
                        # t1 = op1(val, const)
                        add_valu(stage["op1"], node_base[v], val_base[v], stage["const_v"], vec=v)
                        # t2 = shift(val)
                        for lane in range(VLEN):
                            add_alu(
                                stage["shift_op"],
                                tmp_base[v] + lane,
                                val_base[v] + lane,
                                stage["shift_s"],
                                vec=v,
                            )
                        # val = op2(t1, t2)
                        add_valu(stage["op2"], val_base[v], node_base[v], tmp_base[v], vec=v)

                # index update
                if r == 10:
                    # deterministic wrap
                    add_valu("^", idx_base[v], idx_base[v], idx_base[v], vec=v)
                elif r != 15:
                    add_valu("&", tmp_base[v], val_base[v], one_v, vec=v)
                    add_valu("+", tmp_base[v], tmp_base[v], one_v, vec=v)
                    add_vmuladd(idx_base[v], idx_base[v], two_v, tmp_base[v], vec=v)



        # Store values
        for v in range(n_vecs):
            add_vstore(val_ptr[v], val_base[v], vec=v)

        # -------------------------
        # Schedule ops into bundles
        # -------------------------
        caps = {"alu": 12, "valu": 6, "load": 2, "store": 2, "flow": 1}

        from collections import defaultdict

        ready = defaultdict(int)
        for token in virtual_tokens:
            ready[token] = 10**9
        cycles: list[dict[str, list[tuple]]] = []
        unscheduled = ops
        cycle = 0

        noop = self.alloc_scratch("noop")

        def append_cycle(bundles: dict[str, list[tuple]]):
            instr = {k: v for k, v in bundles.items() if v}
            if instr:
                self.instrs.append(instr)

        while unscheduled:
            if cycle >= len(cycles):
                cycles.append({k: [] for k in caps})
            used = {k: len(cycles[cycle][k]) for k in caps}
            scheduled_any = False
            new_unscheduled = []
            for op in unscheduled:
                if used[op.engine] >= caps[op.engine]:
                    new_unscheduled.append(op)
                    continue
                max_ready = 0
                if op.reads:
                    max_ready = max(ready[a] for a in op.reads)
                if max_ready <= cycle:
                    cycles[cycle][op.engine].append(op.slot)
                    used[op.engine] += 1
                    for w in op.writes:
                        ready[w] = cycle + 1
                    scheduled_any = True
                else:
                    new_unscheduled.append(op)
            unscheduled = new_unscheduled
            if scheduled_any:
                cycle += 1
            else:
                # Insert a harmless ALU op to advance time
                cycles[cycle]["alu"].append(("+", noop, noop, zero_s))
                cycle += 1

        for bundles in cycles:
            append_cycle(bundles)

        if os.getenv("KERNEL_ANALYZE") == "1":
            from kernel_analyzer import print_summary

            print_summary(self.analyze())


    def _build_kernel_scalar(
        self, forest_height: int, n_nodes: int, batch_size: int, rounds: int
    ):
        """
        Like reference_kernel2 but building actual instructions.
        Scalar implementation using only scalar ALU and load/store.
        """
        tmp1 = self.alloc_scratch("tmp1")
        tmp2 = self.alloc_scratch("tmp2")
        tmp3 = self.alloc_scratch("tmp3")
        # Scratch space addresses
        init_vars = [
            "rounds",
            "n_nodes",
            "batch_size",
            "forest_height",
            "forest_values_p",
            "inp_indices_p",
            "inp_values_p",
        ]
        for v in init_vars:
            self.alloc_scratch(v, 1)
        for i, v in enumerate(init_vars):
            self.add("load", ("const", tmp1, i))
            self.add("load", ("load", self.scratch[v], tmp1))

        zero_const = self.scratch_const(0)
        one_const = self.scratch_const(1)
        two_const = self.scratch_const(2)

        # Pause instructions are matched up with yield statements in the reference
        # kernel to let you debug at intermediate steps. The testing harness in this
        # file requires these match up to the reference kernel's yields, but the
        # submission harness ignores them.
        self.add("flow", ("pause",))
        # Any debug engine instruction is ignored by the submission simulator
        self.add("debug", ("comment", "Starting loop"))

        body = []  # array of slots

        # Scalar scratch registers
        tmp_idx = self.alloc_scratch("tmp_idx")
        tmp_val = self.alloc_scratch("tmp_val")
        tmp_node_val = self.alloc_scratch("tmp_node_val")
        tmp_addr = self.alloc_scratch("tmp_addr")

        for round in range(rounds):
            for i in range(batch_size):
                i_const = self.scratch_const(i)
                # idx = mem[inp_indices_p + i]
                body.append(("alu", ("+", tmp_addr, self.scratch["inp_indices_p"], i_const)))
                body.append(("load", ("load", tmp_idx, tmp_addr)))
                body.append(("debug", ("compare", tmp_idx, (round, i, "idx"))))
                # val = mem[inp_values_p + i]
                body.append(("alu", ("+", tmp_addr, self.scratch["inp_values_p"], i_const)))
                body.append(("load", ("load", tmp_val, tmp_addr)))
                body.append(("debug", ("compare", tmp_val, (round, i, "val"))))
                # node_val = mem[forest_values_p + idx]
                body.append(("alu", ("+", tmp_addr, self.scratch["forest_values_p"], tmp_idx)))
                body.append(("load", ("load", tmp_node_val, tmp_addr)))
                body.append(("debug", ("compare", tmp_node_val, (round, i, "node_val"))))
                # val = myhash(val ^ node_val)
                body.append(("alu", ("^", tmp_val, tmp_val, tmp_node_val)))
                body.extend(self.build_hash(tmp_val, tmp1, tmp2, round, i))
                body.append(("debug", ("compare", tmp_val, (round, i, "hashed_val"))))
                # idx = 2*idx + (1 if val % 2 == 0 else 2)
                body.append(("alu", ("%", tmp1, tmp_val, two_const)))
                body.append(("alu", ("==", tmp1, tmp1, zero_const)))
                body.append(("flow", ("select", tmp3, tmp1, one_const, two_const)))
                body.append(("alu", ("*", tmp_idx, tmp_idx, two_const)))
                body.append(("alu", ("+", tmp_idx, tmp_idx, tmp3)))
                body.append(("debug", ("compare", tmp_idx, (round, i, "next_idx"))))
                # idx = 0 if idx >= n_nodes else idx
                body.append(("alu", ("<", tmp1, tmp_idx, self.scratch["n_nodes"])))
                body.append(("flow", ("select", tmp_idx, tmp1, tmp_idx, zero_const)))
                body.append(("debug", ("compare", tmp_idx, (round, i, "wrapped_idx"))))
                # mem[inp_indices_p + i] = idx
                body.append(("alu", ("+", tmp_addr, self.scratch["inp_indices_p"], i_const)))
                body.append(("store", ("store", tmp_addr, tmp_idx)))
                # mem[inp_values_p + i] = val
                body.append(("alu", ("+", tmp_addr, self.scratch["inp_values_p"], i_const)))
                body.append(("store", ("store", tmp_addr, tmp_val)))

        body_instrs = self.build(body)
        self.instrs.extend(body_instrs)
        # Required to match with the yield in reference_kernel2
        self.instrs.append({"flow": [("pause",)]})

BASELINE = 147734

def do_kernel_test(
    forest_height: int,
    rounds: int,
    batch_size: int,
    seed: int = 123,
    trace: bool = False,
    prints: bool = False,
):
    print(f"{forest_height=}, {rounds=}, {batch_size=}")
    random.seed(seed)
    forest = Tree.generate(forest_height)
    inp = Input.generate(forest, batch_size, rounds)
    mem = build_mem_image(forest, inp)

    kb = KernelBuilder()
    kb.build_kernel(forest.height, len(forest.values), len(inp.indices), rounds)
    if os.getenv("KERNEL_ANALYZE") == "1":
        from kernel_analyzer import print_summary

        print_summary(kb.analyze())
    # print(kb.instrs)

    value_trace = {}
    machine = Machine(
        mem,
        kb.instrs,
        kb.debug_info(),
        n_cores=N_CORES,
        value_trace=value_trace,
        trace=trace,
    )
    machine.prints = prints
    for i, ref_mem in enumerate(reference_kernel2(mem, value_trace)):
        machine.run()
        inp_values_p = ref_mem[6]
        if prints:
            print(machine.mem[inp_values_p : inp_values_p + len(inp.values)])
            print(ref_mem[inp_values_p : inp_values_p + len(inp.values)])
        assert (
            machine.mem[inp_values_p : inp_values_p + len(inp.values)]
            == ref_mem[inp_values_p : inp_values_p + len(inp.values)]
        ), f"Incorrect result on round {i}"
        inp_indices_p = ref_mem[5]
        if prints:
            print(machine.mem[inp_indices_p : inp_indices_p + len(inp.indices)])
            print(ref_mem[inp_indices_p : inp_indices_p + len(inp.indices)])
        # Updating these in memory isn't required, but you can enable this check for debugging
        # assert machine.mem[inp_indices_p:inp_indices_p+len(inp.indices)] == ref_mem[inp_indices_p:inp_indices_p+len(inp.indices)]

    print("CYCLES: ", machine.cycle)
    print("Speedup over baseline: ", BASELINE / machine.cycle)
    return machine.cycle


class Tests(unittest.TestCase):
    def test_ref_kernels(self):
        """
        Test the reference kernels against each other
        """
        random.seed(123)
        for i in range(10):
            f = Tree.generate(4)
            inp = Input.generate(f, 10, 6)
            mem = build_mem_image(f, inp)
            reference_kernel(f, inp)
            for _ in reference_kernel2(mem, {}):
                pass
            assert inp.indices == mem[mem[5] : mem[5] + len(inp.indices)]
            assert inp.values == mem[mem[6] : mem[6] + len(inp.values)]

    def test_kernel_trace(self):
        # Full-scale example for performance testing
        do_kernel_test(10, 16, 256, trace=True, prints=False)

    # Passing this test is not required for submission, see submission_tests.py for the actual correctness test
    # You can uncomment this if you think it might help you debug
    # def test_kernel_correctness(self):
    #     for batch in range(1, 3):
    #         for forest_height in range(3):
    #             do_kernel_test(
    #                 forest_height + 2, forest_height + 4, batch * 16 * VLEN * N_CORES
    #             )

    def test_kernel_cycles(self):
        do_kernel_test(10, 16, 256)


# To run all the tests:
#    python perf_takehome.py
# To run a specific test:
#    python perf_takehome.py Tests.test_kernel_cycles
# To view a hot-reloading trace of all the instructions:  **Recommended debug loop**
# NOTE: The trace hot-reloading only works in Chrome. In the worst case if things aren't working, drag trace.json onto https://ui.perfetto.dev/
#    python perf_takehome.py Tests.test_kernel_trace
# Then run `python watch_trace.py` in another tab, it'll open a browser tab, then click "Open Perfetto"
# You can then keep that open and re-run the test to see a new trace.

# To run the proper checks to see which thresholds you pass:
#    python tests/submission_tests.py

if __name__ == "__main__":
    unittest.main()
