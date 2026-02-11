from __future__ import annotations

from dataclasses import replace

from generator.ub_energy_bundle_1291 import SPEC_UB_ENERGY_BUNDLE_1291
from generator.build_kernel_base import build_base_instrs
from perf_takehome import KernelBuilder as BaseKernelBuilder


SPEC_OFFLOAD_MORE_GANG = replace(
    SPEC_UB_ENERGY_BUNDLE_1291,
    offload_budget_parity=448,
    offload_budget_node_xor=512,
    sched_policy="baseline_gang_offload",
)


class KernelBuilder(BaseKernelBuilder):
    def build_kernel(self, forest_height: int, n_nodes: int, batch_size: int, rounds: int):
        self.instrs = build_base_instrs(spec=SPEC_OFFLOAD_MORE_GANG)

