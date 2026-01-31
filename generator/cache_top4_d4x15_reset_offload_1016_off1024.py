from __future__ import annotations

from dataclasses import replace

from generator.spec_base import SPEC_BASE
from generator.build_kernel_base import build_base_instrs

SPEC_CACHE_TOP4_D4X15_RESET_OFFLOAD_1016_OFF1024 = replace(
    SPEC_BASE,
    offload_op1=1024,
    total_cycles=1726,
)

def build_instrs():
    return build_base_instrs(spec=SPEC_CACHE_TOP4_D4X15_RESET_OFFLOAD_1016_OFF1024)
