from __future__ import annotations

from dataclasses import replace

from generator.spec_base import SPEC_BASE
from generator.build_kernel_base import build_base_instrs

SPEC_CACHE_TOP4_D4X15_RESET_OFFLOAD_1016_BITMASK = replace(
    SPEC_BASE,
    use_bitmask_selection=True,
    vector_block=32,
    extra_vecs=2,
    offload_op1=0,
    total_cycles=1577,
)

def build_instrs():
    return build_base_instrs(spec=SPEC_CACHE_TOP4_D4X15_RESET_OFFLOAD_1016_BITMASK)
