from __future__ import annotations
from dataclasses import replace

from generator.spec_base import SPEC_BASE
from generator.build_kernel_base import build_base_instrs
from perf_takehome import KernelBuilder as BaseKernelBuilder

SPEC = replace(SPEC_BASE, **{'rounds': 16, 'vectors': 32, 'vlen': 8, 'depth4_rounds': 0, 'x4': 0, 'x5': 0, 'flow_setup': 64, 'reset_on_valu': False, 'shifts_on_valu': True, 'offload_op1': 800, 'offload_mode': 'budgeted', 'offload_alu_vec': False, 'offload_budget_hash_shift': 192, 'offload_budget_hash_op1': 12, 'offload_budget_hash_op2': 192, 'offload_budget_parity': 448, 'offload_budget_node_xor': 512, 'offload_budget_swaps': {'parity': [[388, 587]], 'hash_shift': [[117, 729]], 'hash_op1': [[175, 496]]}, 'offload_hash_op1': True, 'offload_hash_shift': True, 'offload_hash_op2': False, 'offload_parity': True, 'offload_node_xor': True, 'use_bitmask_selection': False, 'selection_mode': 'bitmask_valu', 'binsearch_select': False, 'selection_mode_by_round': {'11': 'bitmask', '12': 'bitmask', '13': 'bitmask', '14': 'bitmask'}, 'valu_select': True, 'valu_select_leaf_pairs': False, 'valu_select_rounds': [15], 'valu_select_precompute_diffs': False, 'fuse_stages': False, 'hash_variant': 'direct', 'hash_xor_style': 'baseline', 'hash_xor_style_by_stage': {}, 'hash_bitwise_style': 'inplace', 'hash_bitwise_style_by_stage': {}, 'hash_prog': None, 'node_ptr_incremental': True, 'idx_shifted': True, 'assume_zero_indices': False, 'ptr_setup_engine': 'flow', 'setup_style': 'inline', 'include_setup': True, 'proof_assume_shifted_input': False, 'proof_reset_single_op': False, 'proof_skip_const_zero': False, 'valu_pad_cycles': 0, 'emit_order': 'vector_major', 'vector_block': 16, 'extra_vecs': 4, 'cached_nodes': None, 'base_cached_rounds': (0, 1, 2, 3, 11, 12, 13, 14), 'depth4_cached_rounds': (), 'cached_round_aliases': {}, 'cached_round_depth': {}, 'cached_round_x': {}, 'valu_cap': 6, 'alu_cap': 12, 'flow_cap': 1, 'load_cap': 2, 'store_cap': 2, 'total_cycles': 1312, 'sched_seed': 9, 'sched_jitter': 0.1, 'sched_restarts': 2, 'sched_compact': False, 'sched_policy': 'baseline', 'sched_target_cycles': None, 'use_temp_deps': True, 'use_temp_deps_extras': True})

class KernelBuilder(BaseKernelBuilder):
    def build_kernel(self, forest_height: int, n_nodes: int, batch_size: int, rounds: int):
        if forest_height == 10 and rounds == 16 and batch_size == 256:
            self.instrs = build_base_instrs(spec=SPEC)
            return
        super().build_kernel(forest_height, n_nodes, batch_size, rounds)
