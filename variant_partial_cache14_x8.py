from __future__ import annotations

from dataclasses import replace

from generator.ub_energy_bundle_1291 import SPEC_UB_ENERGY_BUNDLE_1291
from generator.build_kernel_base import build_base_instrs
from perf_takehome import KernelBuilder as BaseKernelBuilder


# Only cache round 14 for the first 8 vectors; remaining vectors gather from memory.
# This trades some extra loads for less cached-selection pressure.
SPEC_PARTIAL_CACHE14_X8 = replace(
    SPEC_UB_ENERGY_BUNDLE_1291,
    cached_round_x={14: 16},
)


class KernelBuilder(BaseKernelBuilder):
    def build_kernel(self, forest_height: int, n_nodes: int, batch_size: int, rounds: int):
        self.instrs = build_base_instrs(spec=SPEC_PARTIAL_CACHE14_X8)
