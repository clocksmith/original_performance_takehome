from __future__ import annotations
from dataclasses import replace
from generator.spec_base import SPEC_BASE, with_offload_defaults
from generator.build_kernel_base import build_base_instrs
from perf_takehome import KernelBuilder as BaseKernelBuilder

SPEC_1174 = with_offload_defaults(
    idx_shifted=True,
    use_bitmask_selection=True,
    selection_mode="bitmask",
    extra_vecs=3,
    sched_restarts=100,
)

class KernelBuilder(BaseKernelBuilder):
    def build_kernel(self, forest_height: int, n_nodes: int, batch_size: int, rounds: int):
        self.instrs = build_base_instrs(spec=SPEC_1174)