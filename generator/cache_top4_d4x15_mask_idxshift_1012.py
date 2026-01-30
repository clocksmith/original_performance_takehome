from __future__ import annotations

from dataclasses import replace

from generator.spec_1013 import SPEC_1013
from generator.build_kernel_1013 import build_1013_instrs

SPEC_CACHE_TOP4_D4X15_MASK_IDXSHIFT_1012 = replace(
    SPEC_1013,
    selection_mode='mask',
    idx_shifted=True,
    extra_vecs=4,
    vector_block=4,
    offload_op1=1518,
    total_cycles=1012,
    include_setup=False,
)

def build_instrs():
    return build_1013_instrs(spec=SPEC_CACHE_TOP4_D4X15_MASK_IDXSHIFT_1012)
