from __future__ import annotations

from dataclasses import replace

from generator.spec_base import SPEC_BASE
from generator.build_kernel_base import build_base_instrs

SPEC_UB_ENERGY_BUNDLE_1486 = replace(
    SPEC_BASE,
    rounds=16,
    vectors=32,
    vlen=8,
    depth4_rounds=1,
    x4=24,
    x5=0,
    flow_setup=64,
    reset_on_valu=True,
    shifts_on_valu=False,
    offload_op1=400,
    offload_hash_op1=False,
    offload_hash_shift=False,
    offload_hash_op2=False,
    offload_parity=True,
    offload_node_xor=False,
    use_bitmask_selection=False,
    selection_mode='mask_precompute',
    valu_select=False,
    node_ptr_incremental=False,
    idx_shifted=False,
    ptr_setup_engine='flow',
    setup_style='inline',
    include_setup=True,
    proof_assume_shifted_input=False,
    proof_reset_single_op=False,
    proof_skip_const_zero=False,
    valu_pad_cycles=0,
    vector_block=8,
    extra_vecs=4,
    cached_nodes=None,
    base_cached_rounds=(0, 1, 2, 11, 12, 13, 14),
    depth4_cached_rounds=(4,),
    cached_round_aliases={},
    cached_round_depth={},
    cached_round_x={},
    valu_cap=6,
    alu_cap=12,
    flow_cap=1,
    load_cap=2,
    store_cap=2,
    total_cycles=1312,
)

def build_instrs():
    return build_base_instrs(spec=SPEC_UB_ENERGY_BUNDLE_1486)
