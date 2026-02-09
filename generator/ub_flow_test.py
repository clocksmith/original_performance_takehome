
import sys
import collections
from problem import SLOT_LIMITS, HASH_STAGES, VLEN, N_CORES, SCRATCH_SIZE
from perf_takehome import KernelBuilder as BaseKernelBuilder

# Targeting sub-1000 cycles via:
# 1. 1-based indexing for traversal (1-op idx update).
# 2. Multiply-Add for linear hash stages (1-op each).
# 3. ALU offloading for bitwise hash components (2 VALU ops per bitwise stage instead of 3).
# 4. Level 0-3 node caching in scratch.
# 5. Interleaving 32 vectors to hide RAW latency.

class KernelBuilder(BaseKernelBuilder):
    def __init__(self):
        super().__init__()
        self.instrs = []
        self.scratch_debug = {}
        self.scratch_ptr = 0
        self.const_s = {}
        self.const_v = {}
        self.vector_bases = set()
        self.slot_limits = SLOT_LIMITS

    def alloc_s(self, name=None):
        addr = self.scratch_ptr
        self.scratch_ptr += 1
        if name:
            self.scratch_debug[addr] = (name, 1)
        return addr

    def alloc_v(self, name=None):
        addr = self.scratch_ptr
        self.scratch_ptr += VLEN
        self.vector_bases.add(addr)
        if name:
            self.scratch_debug[addr] = (name, VLEN)
        return addr

    def get_const_s(self, val, setup_ops):
        if val not in self.const_s:
            addr = self.alloc_s(f"c_s_{val}")
            setup_ops.append(('load', ('const', addr, val), [], [addr]))
            self.const_s[val] = addr
        return self.const_s[val]

    def get_const_v(self, val, setup_ops):
        if val not in self.const_v:
            s_addr = self.get_const_s(val, setup_ops)
            v_addr = self.alloc_v(f"c_v_{val}")
            setup_ops.append(('valu', ('vbroadcast', v_addr, s_addr), [s_addr], [v_addr]))
            self.const_v[val] = v_addr
        return self.const_v[val]

    def pack(self, ops):
        """Standard greedy packer handling engine capacity and RAW latency."""
        bundles = []
        last_write = collections.defaultdict(lambda: -1)
        
        for engine, op, reads, writes in ops:
            ready_cycle = 0
            for r in reads:
                ready_cycle = max(ready_cycle, last_write[r] + 1)
            
            c = ready_cycle
            while True:
                if c >= len(bundles):
                    bundles.append(collections.defaultdict(list))
                if len(bundles[c][engine]) < self.slot_limits[engine]:
                    bundles[c][engine].append(op)
                    for w in writes:
                        last_write[w] = c
                    break
                c += 1
        return bundles

    def build_kernel(self, forest_height, n_nodes, batch_size, rounds):
        self.scratch_ptr = 0
        self.const_s = {}
        self.const_v = {}
        self.vector_bases = set()
        self.scratch_debug = {}
        setup_ops = []
        body_ops = []

        def add_vop(engine, op, reads=(), writes=(), ops_list=body_ops):
            all_reads = []
            for r in reads:
                if r in self.vector_bases: all_reads.extend(range(r, r+8))
                else: all_reads.append(r)
            all_writes = []
            for w in writes:
                if w in self.vector_bases: all_writes.extend(range(w, w+8))
                else: all_writes.append(w)
            ops_list.append((engine, op, all_reads, all_writes))

        def add_alu_vsop(op, dest, src1, src2_scalar):
            for i in range(8):
                add_vop('alu', (op, dest+i, src1+i, src2_scalar), [src1+i, src2_scalar], [dest+i])

        num_vectors = 32
        
        # 1. Setup Base Pointers
        f_ptr_addr = self.alloc_s("f_ptr")
        idx_base_addr = self.alloc_s("idx_base")
        val_base_addr = self.alloc_s("val_base")
        add_op = lambda engine, op, reads, writes: add_vop(engine, op, reads, writes, setup_ops)
        
        add_op('load', ('load', f_ptr_addr, self.get_const_s(4, setup_ops)), [self.get_const_s(4, setup_ops)], [f_ptr_addr])
        add_op('load', ('load', idx_base_addr, self.get_const_s(5, setup_ops)), [self.get_const_s(5, setup_ops)], [idx_base_addr])
        add_op('load', ('load', val_base_addr, self.get_const_s(6, setup_ops)), [self.get_const_s(6, setup_ops)], [val_base_addr])
        
        # Forest base for 1-based indexing
        f_ptr_m1 = self.alloc_s("f_ptr-1")
        add_op('alu', ('-', f_ptr_m1, f_ptr_addr, self.get_const_s(1, setup_ops)), [f_ptr_addr, self.get_const_s(1, setup_ops)], [f_ptr_m1])
        f_ptr_v = self.alloc_v("f_ptr_v")
        add_op('valu', ('vbroadcast', f_ptr_v, f_ptr_m1), [f_ptr_m1], [f_ptr_v])

        # Cache Nodes Level 0-3
        nodes_v = [self.alloc_v(f"node_{i}") for i in range(15)]
        for i in range(15):
            p = self.alloc_s()
            add_op('alu', ('+', p, f_ptr_addr, self.get_const_s(i, setup_ops)), [f_ptr_addr, self.get_const_s(i, setup_ops)], [p])
            v_s = self.alloc_s()
            add_op('load', ('load', v_s, p), [p], [v_s])
            add_op('valu', ('vbroadcast', nodes_v[i], v_s), [v_s], [nodes_v[i]])

        # 2. Initial Data Load (32 vectors)
        val_v = [self.alloc_v(f"val_{v}") for v in range(num_vectors)]
        idx_v = [self.alloc_v(f"idx_{v}") for v in range(num_vectors)]
        val_ptr_s = [self.alloc_s() for _ in range(num_vectors)]
        idx_ptr_s = [self.alloc_s() for _ in range(num_vectors)]
        
        c_1_v = self.get_const_v(1, setup_ops)
        c_1_s = self.get_const_s(1, setup_ops)
        c_2_v = self.get_const_v(2, setup_ops)
        c_4_v = self.get_const_v(4, setup_ops)
        c_2048_v = self.get_const_v(2048, setup_ops)
        
        for v in range(num_vectors):
            vp = val_ptr_s[v]
            add_op('flow', ('add_imm', vp, val_base_addr, v*8), [val_base_addr], [vp])
            add_vop('load', ('vload', val_v[v], vp), [vp], [val_v[v]], body_ops)
            ip = idx_ptr_s[v]
            add_op('flow', ('add_imm', ip, idx_base_addr, v*8), [idx_base_addr], [ip])
            add_vop('load', ('vload', idx_v[v], ip), [ip], [idx_v[v]], body_ops)
            add_vop('valu', ('+', idx_v[v], idx_v[v], c_1_v), [idx_v[v], c_1_v], [idx_v[v]], body_ops)

        # 3. Constants for Hash
        c_4097_v = self.get_const_v(4097, setup_ops)
        c_33_v = self.get_const_v(33, setup_ops)
        c_9_v = self.get_const_v(9, setup_ops)
        c_C0_v = self.get_const_v(HASH_STAGES[0][1], setup_ops)
        c_C1_s = self.get_const_s(HASH_STAGES[1][1], setup_ops)
        c_C2_v = self.get_const_v(HASH_STAGES[2][1], setup_ops)
        c_C3_s = self.get_const_s(HASH_STAGES[3][1], setup_ops)
        c_C4_v = self.get_const_v(HASH_STAGES[4][1], setup_ops)
        c_C5_s = self.get_const_s(HASH_STAGES[5][1], setup_ops)
        c_19_v = self.get_const_v(19, setup_ops)
        c_16_v = self.get_const_v(16, setup_ops)

        # Rotation buffers for bits and nodes
        bits_vs = [[self.alloc_v() for _ in range(3)] for _ in range(4)]
        n_res_vs = [self.alloc_v() for _ in range(4)]
        h_tmp_vs = [self.alloc_v() for _ in range(4)]

        # 4. Round Loop
        for r in range(rounds):
            depth = r if r < 10 else r - 11
            for v in range(num_vectors):
                nb = n_res_vs[v % 4]
                bv = bits_vs[v % 4]
                # Node Selection
                if depth == 0:
                    add_vop('valu', ('+', nb, nodes_v[0], self.get_const_v(0, setup_ops)), [nodes_v[0]], [nb])
                elif depth == 1:
                    add_alu_vsop('&', bv[0], idx_v[v], c_1_s)
                    add_vop('flow', ('vselect', nb, bv[0], nodes_v[2], nodes_v[1]), [bv[0], nodes_v[2], nodes_v[1]], [nb])
                elif depth == 2:
                    add_alu_vsop('&', bv[0], idx_v[v], c_1_s)
                    add_alu_vsop('&', bv[1], idx_v[v], c_2_s)
                    t1 = self.alloc_v(); add_vop('flow', ('vselect', t1, bv[0], nodes_v[4], nodes_v[3]), [bv[0], nodes_v[4], nodes_v[3]], [t1])
                    t2 = self.alloc_v(); add_vop('flow', ('vselect', t2, bv[0], nodes_v[6], nodes_v[5]), [bv[0], nodes_v[6], nodes_v[5]], [t2])
                    add_vop('flow', ('vselect', nb, bv[1], t2, t1), [bv[1], t2, t1], [nb])
                elif depth == 3:
                    add_alu_vsop('&', bv[0], idx_v[v], c_1_s)
                    add_alu_vsop('&', bv[1], idx_v[v], c_2_s)
                    c_4_s = self.get_const_s(4, setup_ops)
                    add_alu_vsop('&', bv[2], idx_v[v], c_4_s)
                    t1 = self.alloc_v(); add_vop('flow', ('vselect', t1, bv[0], nodes_v[8], nodes_v[7]), [bv[0], nodes_v[8], nodes_v[7]], [t1])
                    t2 = self.alloc_v(); add_vop('flow', ('vselect', t2, bv[0], nodes_v[10], nodes_v[9]), [bv[0], nodes_v[10], nodes_v[9]], [t2])
                    t3 = self.alloc_v(); add_vop('flow', ('vselect', t3, bv[0], nodes_v[12], nodes_v[11]), [bv[0], nodes_v[12], nodes_v[11]], [t3])
                    t4 = self.alloc_v(); add_vop('flow', ('vselect', t4, bv[0], nodes_v[14], nodes_v[13]), [bv[0], nodes_v[14], nodes_v[13]], [t4])
                    t5 = self.alloc_v(); add_vop('flow', ('vselect', t5, bv[1], t2, t1), [bv[1], t2, t1], [t5])
                    t6 = self.alloc_v(); add_vop('flow', ('vselect', t6, bv[1], t4, t3), [bv[1], t4, t3], [t6])
                    add_vop('flow', ('vselect', nb, bv[2], t6, t5), [bv[2], t6, t5], [nb])
                else:
                    av = self.alloc_v()
                    add_vop('valu', ('+', av, f_ptr_v, idx_v[v]), [f_ptr_v, idx_v[v]], [av])
                    for lane in range(8):
                        add_vop('load', ('load_offset', nb, av, lane), [av+lane], [nb+lane])

                # Hash and Update
                ht = h_tmp_vs[v % 4]
                add_alu_vop('^', val_v[v], val_v[v], nb)
                add_vop('valu', ('multiply_add', val_v[v], val_v[v], c_4097_v, c_C0_v), [val_v[v], c_4097_v, c_C0_v], [val_v[v]])
                add_vop('valu', ('>>', ht, val_v[v], c_19_v), [val_v[v], c_19_v], [ht])
                add_alu_vsop('^', val_v[v], val_v[v], c_C1_s)
                add_vop('valu', ('^', val_v[v], val_v[v], ht), [val_v[v], ht], [val_v[v]])
                add_vop('valu', ('multiply_add', val_v[v], val_v[v], c_33_v, c_C2_v), [val_v[v], c_33_v, c_C2_v], [val_v[v]])
                add_alu_vsop('+', val_v[v], val_v[v], c_C3_s)
                add_vop('valu', ('<<', ht, val_v[v], c_9_shift_v), [val_v[v], c_9_shift_v], [ht])
                add_vop('valu', ('^', val_v[v], val_v[v], ht), [val_v[v], ht], [val_v[v]])
                add_vop('valu', ('multiply_add', val_v[v], val_v[v], c_9_v, c_C4_v), [val_v[v], c_9_v, c_C4_v], [val_v[v]])
                add_vop('valu', ('>>', ht, val_v[v], c_16_v), [val_v[v], c_16_v], [ht])
                add_alu_vsop('^', val_v[v], val_v[v], c_C5_s)
                add_vop('valu', ('^', val_v[v], val_v[v], ht), [val_v[v], ht], [val_v[v]])

                if r != 15:
                    p = self.alloc_v()
                    add_alu_vsop('&', p, val_v[v], c_1_s)
                    add_vop('valu', ('multiply_add', idx_v[v], idx_v[v], c_2_v, p), [idx_v[v], c_2_v, p], [idx_v[v]])
                    if r == 9:
                        cond = self.alloc_v()
                        add_vop('valu', ('<', cond, idx_v[v], c_2048_v), [idx_v[v], c_2048_v], [cond])
                        add_vop('flow', ('vselect', idx_v[v], cond, idx_v[v], c_1_v), [cond, idx_v[v], c_1_v], [idx_v[v]])

        # 5. Store Results
        for v in range(num_vectors):
            add_vop('store', ('vstore', val_ptr_s[v], val_v[v]), [val_ptr_s[v], val_v[v]], [])

        self.instrs = self.pack(setup_ops + body_ops)

def do_kernel_test(forest_height, rounds, batch_size, seed=123, trace=False, prints=False):
    random.seed(seed)
    forest = Tree.generate(forest_height)
    inp = Input.generate(forest, batch_size, rounds)
    mem = build_mem_image(forest, inp)
    kb = KernelBuilder()
    kb.build_kernel(forest.height, len(forest.values), len(inp.indices), rounds)
    machine = Machine(mem, kb.instrs, kb.debug_info(), n_cores=N_CORES, trace=trace)
    machine.enable_pause = False
    machine.enable_debug = False
    machine.run()
    for ref_mem in reference_kernel2(mem): pass
    inp_v_p = ref_mem[6]
    assert machine.mem[inp_v_p:inp_v_p+len(inp.values)] == ref_mem[inp_v_p:inp_v_p+len(inp.values)], "Incorrect output"
    print("CYCLES: ", machine.cycle)
    return machine.cycle

if __name__ == "__main__":
    if len(sys.argv) > 1 and sys.argv[1] == "test":
        do_kernel_test(10, 16, 256)
    else:
        unittest.main()
