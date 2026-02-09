
from __future__ import annotations
from dataclasses import replace
from generator.ub_energy_bundle_1291 import SPEC_UB_ENERGY_BUNDLE_1291
from generator.build_kernel_base import build_base_instrs
from perf_takehome import KernelBuilder as BaseKernelBuilder

SPEC_MAX = replace(
    SPEC_UB_ENERGY_BUNDLE_1291,
    offload_mode="prefix",
    offload_op1=2000,
    offload_hash_op1=True,
    offload_hash_shift=True,
    offload_hash_op2=True,
    offload_parity=True,
    offload_node_xor=True,
    selection_mode="eq",
    selection_mode_by_round={},
)

class KernelBuilder(BaseKernelBuilder):
    def build_kernel(self, forest_height: int, n_nodes: int, batch_size: int, rounds: int):
        self.instrs = build_base_instrs(spec=SPEC_MAX)
