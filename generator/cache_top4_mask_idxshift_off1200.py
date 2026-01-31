from __future__ import annotations

from dataclasses import replace

from generator.spec_1016 import SPEC_1016
from generator.build_kernel_1016 import build_1016_instrs

SPEC_CACHE_TOP4_MASK_IDXSHIFT_OFF1200 = replace(
    SPEC_1016,
    selection_mode='mask',
    idx_shifted=True,
    offload_op1=1200,
    extra_vecs=2,
)

def build_instrs():
    return build_1016_instrs(spec=SPEC_CACHE_TOP4_MASK_IDXSHIFT_OFF1200)
