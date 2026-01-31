from __future__ import annotations

from dataclasses import replace

from generator.spec_base import SPEC_BASE
from generator.build_kernel_base import build_base_instrs

SPEC_CACHE_TOP4_BITMASK_IDXSHIFT_OFF1117_1088 = replace(
    SPEC_BASE,
    use_bitmask_selection=True,
    selection_mode="bitmask",
    idx_shifted=True,
    offload_op1=1117,
    total_cycles=1088,
    depth4_rounds=0,
    depth4_cached_rounds=(),
    x4=0,
)

def build_instrs():
    return build_base_instrs(spec=SPEC_CACHE_TOP4_BITMASK_IDXSHIFT_OFF1117_1088)
