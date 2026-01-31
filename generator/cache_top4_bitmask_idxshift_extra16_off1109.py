from __future__ import annotations

from dataclasses import replace

from generator.spec_base import SPEC_BASE
from generator.build_kernel_base import build_base_instrs

SPEC_CACHE_TOP4_BITMASK_IDXSHIFT_EXTRA16_OFF1109 = replace(
    SPEC_BASE,
    use_bitmask_selection=True,
    selection_mode='bitmask',
    idx_shifted=True,
    reset_on_valu=False,
    offload_op1=1109,
    total_cycles=1084,
    depth4_rounds=0,
    depth4_cached_rounds=(),
    x4=0,
    extra_vecs=16,
)

def build_instrs():
    return build_base_instrs(spec=SPEC_CACHE_TOP4_BITMASK_IDXSHIFT_EXTRA16_OFF1109)
