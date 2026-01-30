from __future__ import annotations

from dataclasses import replace

from .spec_1013 import SPEC_1013
from .build_kernel_1013 import build_1013_instrs

SPEC_AUTOGEN_EQ_5 = replace(
    SPEC_1013,
    depth4_rounds=0,
    x4=8,
    depth4_cached_rounds=(),
    offload_op1=0,
    use_bitmask_selection=False,
    total_cycles=1013,
)

def build_instrs():
    return build_1013_instrs(spec=SPEC_AUTOGEN_EQ_5)
