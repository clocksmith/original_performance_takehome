from __future__ import annotations

from dataclasses import replace

from generator.spec_base import SPEC_BASE
from generator.build_kernel_base import build_base_instrs

SPEC_UB_1124_BITMASK_FREECACHE = replace(
    SPEC_BASE,
    selection_mode='bitmask',
    idx_shifted=False,
    ptr_setup_engine='alu',
    vector_block=8,
    extra_vecs=0,
    offload_op1=1600,
    offload_hash_op1=True,
    offload_hash_shift=False,
    offload_hash_op2=False,
    offload_parity=True,
    offload_node_xor=True,
    reset_on_valu=False,
    shifts_on_valu=False,
    depth4_rounds=0,
    depth4_cached_rounds=(),
    x4=0,
    x5=0,
    base_cached_rounds=(),
    cached_round_depth={0: 0, 1: 0, 2: 0, 3: 0, 4: 0, 5: 0, 6: 0, 7: 0, 8: 0, 9: 0, 10: 0, 11: 0, 12: 0, 13: 0, 14: 0, 15: 0},
    cached_round_aliases={},
    cached_round_x={},
)

def build_instrs():
    return build_base_instrs(spec=SPEC_UB_1124_BITMASK_FREECACHE)
