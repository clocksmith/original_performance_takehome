from __future__ import annotations

from dataclasses import replace

from generator.ub_energy_bundle_1291 import SPEC_UB_ENERGY_BUNDLE_1291
from generator.build_kernel_base import build_base_instrs
from perf_takehome import KernelBuilder as BaseKernelBuilder


# Trade cached depth3 selection in round 14 (7 vselects per vec) for gathers:
# +256 load_offset ops total, but removes a long FLOW chain late in the program.
SPEC_UNCACHE14 = replace(
    SPEC_UB_ENERGY_BUNDLE_1291,
    base_cached_rounds=(0, 1, 2, 3, 11, 12, 13),  # drop 14
)


class KernelBuilder(BaseKernelBuilder):
    def build_kernel(self, forest_height: int, n_nodes: int, batch_size: int, rounds: int):
        self.instrs = build_base_instrs(spec=SPEC_UNCACHE14)

