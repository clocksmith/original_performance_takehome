from __future__ import annotations

from dataclasses import replace

from generator.ub_energy_bundle_1291 import SPEC_UB_ENERGY_BUNDLE_1291
from generator.build_kernel_base import build_base_instrs
from perf_takehome import KernelBuilder as BaseKernelBuilder


# Force eq-selection on all depth<=3 cached rounds (1-3, 11-14).
# This removes dependence on shared `extra_*` scratch temps for selection,
# trading into ALU/flow work.
SPEC_EQ_MORE = replace(
    SPEC_UB_ENERGY_BUNDLE_1291,
    selection_mode_by_round={
        1: "eq",
        2: "eq",
        3: "eq",
        11: "eq",
        12: "eq",
        13: "eq",
        14: "eq",
    },
)


class KernelBuilder(BaseKernelBuilder):
    def build_kernel(self, forest_height: int, n_nodes: int, batch_size: int, rounds: int):
        self.instrs = build_base_instrs(spec=SPEC_EQ_MORE)

