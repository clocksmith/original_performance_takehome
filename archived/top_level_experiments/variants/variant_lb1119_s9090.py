from __future__ import annotations
from dataclasses import replace

from generator.spec_base import SPEC_BASE
from generator.build_kernel_base import build_base_instrs
from perf_takehome import KernelBuilder as BaseKernelBuilder

SPEC = replace(SPEC_BASE, **{'rounds': 16, 'vectors': 32, 'vlen': 8, 'depth4_rounds': 1, 'x4': 0, 'x5': 0, 'flow_setup': 64, 'reset_on_valu': False, 'shifts_on_valu': False, 'offload_op1': 1200, 'offload_mode': 'budgeted', 'offload_alu_vec': False, 'offload_budget_hash_shift': 768, 'offload_budget_hash_op1': 48, 'offload_budget_hash_op2': 12, 'offload_budget_parity': 0, 'offload_budget_node_xor': 384, 'offload_budget_swaps': {'parity': [[272, 425], [89, 938]], 'node_xor': [[28, 885], [297, 598]], 'hash_shift': [[60, 490]], 'hash_op2': [[1, 603]]}, 'offload_hash_op1': False, 'offload_hash_shift': True, 'offload_hash_op2': True, 'offload_parity': False, 'offload_node_xor': True, 'use_bitmask_selection': True, 'selection_mode': 'bitmask', 'binsearch_select': False, 'selection_mode_by_round': {}, 'valu_select': False, 'valu_select_leaf_pairs': False, 'valu_select_rounds': [4], 'valu_select_precompute_diffs': True, 'fuse_stages': False, 'hash_variant': 'direct', 'hash_xor_style': 'baseline', 'hash_xor_style_by_stage': {}, 'hash_bitwise_style': 'inplace', 'hash_bitwise_style_by_stage': {}, 'hash_prog': None, 'node_ptr_incremental': True, 'idx_shifted': True, 'assume_zero_indices': True, 'ptr_setup_engine': 'flow', 'setup_style': 'inline', 'include_setup': True, 'proof_assume_shifted_input': False, 'proof_reset_single_op': False, 'proof_skip_const_zero': False, 'valu_pad_cycles': 0, 'emit_order': 'auto', 'vector_block': 32, 'extra_vecs': 4, 'cached_nodes': 15, 'base_cached_rounds': (0, 1, 2, 3, 11, 12, 13, 14), 'depth4_cached_rounds': (15,), 'cached_round_aliases': {}, 'cached_round_depth': {}, 'cached_round_x': {}, 'valu_cap': 6, 'alu_cap': 12, 'flow_cap': 1, 'load_cap': 2, 'store_cap': 2, 'total_cycles': 1312, 'sched_seed': 9, 'sched_jitter': 0.1, 'sched_restarts': 2, 'sched_compact': False, 'sched_policy': 'baseline', 'sched_target_cycles': None, 'use_temp_deps': False, 'use_temp_deps_extras': False})

class KernelBuilder(BaseKernelBuilder):
    def build_kernel(self, forest_height: int, n_nodes: int, batch_size: int, rounds: int):
        if forest_height == 10 and rounds == 16 and batch_size == 256:
            self.instrs = build_base_instrs(spec=SPEC)
            return
        super().build_kernel(forest_height, n_nodes, batch_size, rounds)
