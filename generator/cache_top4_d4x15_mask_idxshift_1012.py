from __future__ import annotations

from generator.spec_base import with_offload_defaults
from generator.build_kernel_base import build_base_instrs

SPEC_CACHE_TOP4_D4X15_MASK_IDXSHIFT_1012 = with_offload_defaults(
    selection_mode='mask',
    idx_shifted=True,
    extra_vecs=4,
    vector_block=4,
    offload_op1=1518,
    total_cycles=1012,
)

def build_instrs():
    return build_base_instrs(spec=SPEC_CACHE_TOP4_D4X15_MASK_IDXSHIFT_1012)
