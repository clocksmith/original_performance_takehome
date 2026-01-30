from __future__ import annotations

from dataclasses import replace

from .build_kernel_1013 import build_1013_instrs
from .spec_1013 import SPEC_1013


SPEC_LOADBOUND_1316 = replace(
    SPEC_1013,
    # Top-3 caching only: rounds 0-2 and 11-13.
    base_cached_rounds=(0, 1, 2, 11, 12, 13),
    depth4_rounds=0,
    x4=0,
    x5=0,
    depth4_cached_rounds=(),
    # Offload all bitwise op1 stages needed for 1007-cycle compute window.
    offload_op1=1510,
    use_bitmask_selection=False,
    include_setup=False,
    cached_nodes=7,
    ptr_setup_engine="alu",
    total_cycles=1316,
)


def build_instrs():
    return build_1013_instrs(spec=SPEC_LOADBOUND_1316)
