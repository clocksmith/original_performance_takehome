from __future__ import annotations

from .build_kernel_1016 import build_1016_instrs
from .spec_1016 import SPEC_1016


SPEC_PROOF_1016 = SPEC_1016


def build_instrs():
    return build_1016_instrs(spec=SPEC_PROOF_1016)
