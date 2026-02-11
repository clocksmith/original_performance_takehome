from __future__ import annotations

from dataclasses import replace

from generator.ub_energy_bundle_1291 import SPEC_UB_ENERGY_BUNDLE_1291
from generator.build_kernel_base import build_base_instrs
from perf_takehome import KernelBuilder as BaseKernelBuilder


SPEC_LEAF_VALU_SELECT_1000 = replace(
    SPEC_UB_ENERGY_BUNDLE_1291,
    valu_select=False,
    valu_select_leaf_pairs=True,
    valu_select_precompute_diffs=True,
    sched_restarts=2000,
    sched_seed=0,
    sched_jitter=0.2,
)


class KernelBuilder(BaseKernelBuilder):
    def build_kernel(self, forest_height: int, n_nodes: int, batch_size: int, rounds: int):
        self.instrs = build_base_instrs(spec=SPEC_LEAF_VALU_SELECT_1000)

