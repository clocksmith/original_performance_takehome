from __future__ import annotations

from dataclasses import replace

from generator.spec_base import SPEC_BASE
from generator.build_kernel_base import build_base_instrs

SPEC_CACHE_TOP4_D4X15_SKIP_R3_R13_1509 = replace(
    SPEC_BASE,
    base_cached_rounds=(0, 1, 2, 11, 12, 14),
    depth4_rounds=1,
    depth4_cached_rounds=(4,),
    x4=15,
    cached_nodes=31,
    idx_shifted=True,
    offload_hash_op1=False,
    offload_parity=True,
    offload_op1=448,
    use_bitmask_selection=False,
)

def build_instrs():
    return build_base_instrs(spec=SPEC_CACHE_TOP4_D4X15_SKIP_R3_R13_1509)
