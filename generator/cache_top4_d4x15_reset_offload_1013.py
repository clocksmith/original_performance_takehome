from __future__ import annotations

from .build_kernel_base import build_base_instrs
from .spec_base import with_offload_defaults


SPEC_PROOF_1013 = with_offload_defaults(
    depth4_rounds=1,
    x4=15,
    depth4_cached_rounds=(4,),
    use_bitmask_selection=False,
    idx_shifted=True,
    # Align codegen counts with the Lean proof model.
    proof_assume_shifted_input=True,
    proof_reset_single_op=True,
    proof_skip_const_zero=True,
)


def build_instrs():
    return build_base_instrs(spec=SPEC_PROOF_1013)
