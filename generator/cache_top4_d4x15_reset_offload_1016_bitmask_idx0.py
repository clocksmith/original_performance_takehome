from __future__ import annotations

from dataclasses import replace

from generator.spec_1016 import SPEC_1016
from generator.build_kernel_1016 import build_1016_instrs

SPEC_CACHE_TOP4_D4X15_RESET_OFFLOAD_1016_BITMASK_IDX0 = replace(
    SPEC_1016,
    use_bitmask_selection=True,
    vector_block=32,
    extra_vecs=2,
    offload_op1=0,
    idx_shifted=False,
)

def build_instrs():
    return build_1016_instrs(spec=SPEC_CACHE_TOP4_D4X15_RESET_OFFLOAD_1016_BITMASK_IDX0)
