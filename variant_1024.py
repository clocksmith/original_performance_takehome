
from __future__ import annotations
from dataclasses import replace
from generator.ub_energy_bundle_1291 import SPEC_UB_ENERGY_BUNDLE_1291
from generator.build_kernel_base import build_base_instrs
from perf_takehome import KernelBuilder as BaseKernelBuilder

# Targeting 1024 cycles by balancing VALU and ALU.
# VALU capacity: 1024 * 6 = 6144 slots.
# ALU capacity: 1024 * 12 = 12288 slots.
# Total vector-equivalent capacity: 6 + 1.5 = 7.5 ops/cycle.
# Total ops needed: 512 vector-rounds * 15 ops = 7680 ops.
# 7680 / 7.5 = 1024 cycles.

SPEC_1024 = replace(
    SPEC_UB_ENERGY_BUNDLE_1291,
    idx_shifted=True,
    valu_select=False, # Use Flow for selection (704 slots < 1024)
    offload_mode="prefix",
    offload_op1=1536, # Offload 3 ops per vector-round
    offload_hash_op1=True,
    offload_hash_shift=True,
    offload_hash_op2=True,
    offload_parity=True,
    offload_node_xor=True,
    cached_nodes=15,
    base_cached_rounds=(0, 1, 2, 3, 11, 12, 13, 14),
    depth4_rounds=0,
    extra_vecs=3,
    sched_restarts=100,
    total_cycles=1024,
)

class KernelBuilder(BaseKernelBuilder):
    def build_kernel(self, forest_height: int, n_nodes: int, batch_size: int, rounds: int):
        self.instrs = build_base_instrs(spec=SPEC_1024)
