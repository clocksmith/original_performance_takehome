from __future__ import annotations

from dataclasses import replace

from generator.spec_1016 import SPEC_1016
from generator.build_kernel_1016 import build_1016_instrs

SPEC_CACHE_TOP4_BITMASK_IDXSHIFT_RESETFLOW_PARITY_1118 = replace(
    SPEC_1016,
    selection_mode='bitmask',
    use_bitmask_selection=True,
    idx_shifted=True,
    depth4_rounds=0,
    depth4_cached_rounds=(),
    x4=0,
    reset_on_valu=False,
    offload_parity=True,
    offload_op1=1161,
    total_cycles=1118,
)

def build_instrs():
    return build_1016_instrs(spec=SPEC_CACHE_TOP4_BITMASK_IDXSHIFT_RESETFLOW_PARITY_1118)
