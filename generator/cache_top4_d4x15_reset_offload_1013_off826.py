from __future__ import annotations

from dataclasses import replace

from generator.spec_1013 import SPEC_1013
from generator.build_kernel_1013 import build_1013_instrs

SPEC_CACHE_TOP4_D4X15_RESET_OFFLOAD_1013_OFF826 = replace(
    SPEC_1013,
    depth4_rounds=1,
    x4=15,
    depth4_cached_rounds=(4,),
    offload_op1=826,
    use_bitmask_selection=False,
    include_setup=False,
    total_cycles=1174,
)

def build_instrs():
    return build_1013_instrs(spec=SPEC_CACHE_TOP4_D4X15_RESET_OFFLOAD_1013_OFF826)
