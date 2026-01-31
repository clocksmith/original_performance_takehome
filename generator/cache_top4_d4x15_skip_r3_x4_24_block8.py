from __future__ import annotations

from dataclasses import replace

from generator.spec_1016 import SPEC_1016
from generator.build_kernel_1016 import build_1016_instrs

SPEC_CACHE_TOP4_D4X15_SKIP_R3_X4_24_BLOCK8 = replace(
    SPEC_1016,
    base_cached_rounds=(0, 1, 2, 11, 12, 13, 14),
    depth4_rounds=1,
    depth4_cached_rounds=(4,),
    x4=24,
    cached_nodes=31,
    idx_shifted=True,
    offload_hash_op1=False,
    offload_parity=True,
    offload_op1=448,
    use_bitmask_selection=False,
    vector_block=8,
)

def build_instrs():
    return build_1016_instrs(spec=SPEC_CACHE_TOP4_D4X15_SKIP_R3_X4_24_BLOCK8)
