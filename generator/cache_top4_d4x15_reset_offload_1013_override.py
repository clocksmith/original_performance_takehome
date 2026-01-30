from __future__ import annotations

from .build_kernel_1013 import build_1013_instrs
from .cache_top4_d4x15_reset_offload_1013 import SPEC_PROOF_1013


def build_instrs():
    return build_1013_instrs(spec=SPEC_PROOF_1013)
