from __future__ import annotations

from dataclasses import replace

from generator.spec_base import SPEC_BASE
from generator.build_kernel_base import build_base_instrs

SPEC_CACHE_TOP4_MASK_IDXSHIFT_OFF1200 = replace(
    SPEC_BASE,
    selection_mode='mask',
    idx_shifted=True,
    offload_op1=1200,
    extra_vecs=2,
)

def build_instrs():
    return build_base_instrs(spec=SPEC_CACHE_TOP4_MASK_IDXSHIFT_OFF1200)
