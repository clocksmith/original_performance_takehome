from __future__ import annotations

from generator.build_kernel_base import build_base_instrs
from generator.spec_base import with_offload_defaults


SPEC_PROOF_1227 = with_offload_defaults(
    depth4_rounds=1,
    x4=15,
    depth4_cached_rounds=(4,),
    offload_op1=911,
    use_bitmask_selection=False,
    total_cycles=1227,
)


def build_instrs():
    return build_base_instrs(spec=SPEC_PROOF_1227)
