from __future__ import annotations

from dataclasses import replace

from generator.spec_1016 import SPEC_1016
from generator.build_kernel_1016 import build_1016_instrs

SPEC_CACHE_TOP4_BITMASK_IDXSHIFT_RESETFLOW_OFF1109_1084 = replace(
    SPEC_1016,
    use_bitmask_selection=True,
    selection_mode='bitmask',
    idx_shifted=True,
    reset_on_valu=False,
    offload_op1=1109,
    total_cycles=1084,
    depth4_rounds=0,
    depth4_cached_rounds=(),
    x4=0,
)

def build_instrs():
    return build_1016_instrs(spec=SPEC_CACHE_TOP4_BITMASK_IDXSHIFT_RESETFLOW_OFF1109_1084)
