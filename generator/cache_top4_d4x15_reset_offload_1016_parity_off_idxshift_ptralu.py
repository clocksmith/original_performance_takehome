from __future__ import annotations

from dataclasses import replace

from generator.spec_1016 import SPEC_1016
from generator.build_kernel_1016 import build_1016_instrs

SPEC_CACHE_TOP4_D4X15_RESET_OFFLOAD_1016_PARITY_OFF_IDXSHIFT_PTRALU = replace(
    SPEC_1016,
    offload_hash_op1=False,
    offload_parity=True,
    offload_op1=448,
    idx_shifted=True,
    ptr_setup_engine="alu",
    flow_setup=0,
    total_cycles=1645,
)


def build_instrs():
    return build_1016_instrs(spec=SPEC_CACHE_TOP4_D4X15_RESET_OFFLOAD_1016_PARITY_OFF_IDXSHIFT_PTRALU)
