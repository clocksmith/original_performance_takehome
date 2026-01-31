from __future__ import annotations

from .build_kernel_base import build_base_instrs
from .cache_top4_d4x15_reset_offload_1013 import SPEC_PROOF_1013


def build_instrs():
    return build_base_instrs(spec=SPEC_PROOF_1013)
