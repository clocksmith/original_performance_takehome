from __future__ import annotations

from .build_kernel_base import build_base_instrs
from .spec_base import SPEC_BASE


SPEC_PROOF_1016 = SPEC_BASE


def build_instrs():
    return build_base_instrs(spec=SPEC_PROOF_1016)
