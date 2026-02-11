
from __future__ import annotations
from dataclasses import replace
from generator.cache_top4_d4x15_reset_offload_1013 import SPEC_PROOF_1013
from generator.build_kernel_base import build_base_instrs
from perf_takehome import KernelBuilder as BaseKernelBuilder

SPEC_REAL_1013 = replace(
    SPEC_PROOF_1013,
    use_bitmask_selection=True,
    selection_mode="bitmask",
    extra_vecs=3,
    proof_assume_shifted_input=False,
    proof_reset_single_op=False,
    proof_skip_const_zero=False,
    sched_restarts=50,
)

class KernelBuilder(BaseKernelBuilder):
    def build_kernel(self, forest_height: int, n_nodes: int, batch_size: int, rounds: int):
        self.instrs = build_base_instrs(spec=SPEC_REAL_1013)
