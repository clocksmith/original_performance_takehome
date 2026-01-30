from __future__ import annotations

from dataclasses import replace

from generator.build_kernel_1013 import build_1013_instrs
from generator.spec_1013 import SPEC_1013


SPEC_PROOF_1227 = replace(
    SPEC_1013,
    depth4_rounds=1,
    x4=15,
    depth4_cached_rounds=(4,),
    offload_op1=911,
    use_bitmask_selection=False,
    include_setup=False,
    total_cycles=1227,
)


def build_instrs():
    return build_1013_instrs(spec=SPEC_PROOF_1227)
