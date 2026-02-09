
from __future__ import annotations
from dataclasses import replace
from generator.ub_energy_bundle_1291 import SPEC_UB_ENERGY_BUNDLE_1291
from generator.build_kernel_base import build_base_instrs
from perf_takehome import KernelBuilder as BaseKernelBuilder

SPEC_1100 = replace(
    SPEC_UB_ENERGY_BUNDLE_1291,
    idx_shifted=True,
    valu_select=True,
    offload_parity=True,
    offload_node_xor=True,
    offload_hash_op1=True,
    offload_op1=826,
    cached_nodes=15,
    base_cached_rounds=(0, 1, 2, 3, 11, 12, 13, 14),
    depth4_rounds=0,
    extra_vecs=0,
    vector_block=1,
    sched_restarts=50,
    total_cycles=1100,
)

class KernelBuilder(BaseKernelBuilder):
    def build_kernel(self, forest_height: int, n_nodes: int, batch_size: int, rounds: int):
        self.instrs = build_base_instrs(spec=SPEC_1100)
