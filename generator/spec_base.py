from __future__ import annotations

from dataclasses import dataclass, field, replace


@dataclass(frozen=True)
class SpecBase:
    rounds: int = 16
    vectors: int = 32
    vlen: int = 8

    # Tuple params
    depth4_rounds: int = 1
    x4: int = 15
    x5: int = 0
    flow_setup: int = 64
    reset_on_valu: bool = True
    shifts_on_valu: bool = True
    # Proof-aligned: equality selection with offload.
    offload_op1: int = 0
    # Offload controls
    # offload_mode:
    #   - "prefix": offload the first `offload_op1` offloadable ops in program order (legacy behavior)
    #   - "budgeted": offload up to per-category budgets (see offload_budget_* fields)
    offload_mode: str = "prefix"
    offload_budget_hash_shift: int = 0
    offload_budget_hash_op1: int = 0
    offload_budget_hash_op2: int = 0
    offload_budget_parity: int = 0
    offload_budget_node_xor: int = 0
    offload_hash_op1: bool = True
    offload_hash_shift: bool = False
    offload_hash_op2: bool = False
    offload_parity: bool = False
    offload_node_xor: bool = False
    use_bitmask_selection: bool = False
    # Selection modes: "eq", "bitmask", "bitmask_valu", "mask", "mask_precompute".
    selection_mode: str = "eq"
    # Use binary search tree for selection to reduce flow ops from N-1 to log2(N).
    binsearch_select: bool = False
    # Optional per-round selection override (e.g. {4: "mask_precompute"}).
    selection_mode_by_round: dict[int, str] = field(default_factory=dict)
    # Use VALU arithmetic to emulate vselect (reduces flow ops).
    valu_select: bool = False
    # Fuse last hash stage XOR with next node XOR.
    fuse_stages: bool = False
    # Hash lowering options (affects how we emit ops for the fixed myhash circuit).
    # Hash implementation variant:
    # - "direct": current hand-written lowering in generator/op_list.py
    # - "ir": build/rewrite a tiny myhash IR, then emit ops (should be semantically identical)
    hash_variant: str = "direct"
    # XOR-stage lowering (only affects stages where op1=op2="^" in HASH_STAGES).
    # - "baseline": tmp=shift(a_pre); a = a ^ C; a = a ^ tmp
    # - "swap":     tmp=shift(a_pre); a = a ^ tmp; a = a ^ C  (also swaps op1/op2 tags)
    # - "tmp_xor_const": tmp=shift(a_pre); tmp = tmp ^ C; a = a ^ tmp
    hash_xor_style: str = "baseline"
    # - "inplace": baseline emission (stage op1 updates val in-place).
    # - "tmp_op1": compute stage op1 into a temp vector, then combine with shift into val.
    #   This preserves semantics but changes WAR/WAW dependencies, which can improve scheduling.
    hash_bitwise_style: str = "inplace"
    # Custom hash program (only used when hash_variant="prog").
    # Each op is a dict: {"op": "+|^|<<|>>|muladd|mov", "dst": "val|tmp|tmp2",
    #   "a": src, "b": src, "c": src (muladd only), "stage": "shift|op1|op2" (optional)}.
    # Sources can be "val|tmp|tmp2" or integer constants (vector consts).
    hash_prog: list[dict] | None = None
    # Use incremental pointer for cached node preload to reduce const loads.
    node_ptr_incremental: bool = False
    # Use 1-based idx representation to drop the +1 in update.
    idx_shifted: bool = False
    # Pointer setup engine ("flow" or "alu").
    ptr_setup_engine: str = "flow"
    # Setup emission mode: "inline" (op_list), "packed" (builder prelude), or "none".
    setup_style: str = "inline"
    include_setup: bool = True
    # Proof-model flags (used to align codegen with Lean counting assumptions).
    proof_assume_shifted_input: bool = False
    proof_reset_single_op: bool = False
    proof_skip_const_zero: bool = False
    valu_pad_cycles: int = 0
    # Process vectors in blocks to avoid temp aliasing with static schedule.
    # Round-major ordering to minimize cross-vector temp dependencies.
    vector_block: int = 32
    extra_vecs: int = 2
    # Override cached node count (e.g., top-3 caching uses 7 nodes).
    cached_nodes: int | None = None

    # Cached rounds
    base_cached_rounds: tuple[int, ...] = (0, 1, 2, 3, 11, 12, 13, 14)
    depth4_cached_rounds: tuple[int, ...] = (4,)
    # Optional alias mapping to cache arbitrary rounds using an existing depth pattern.
    # Example: {10: 2} treats round 10 as depth-2 cached (like round 2).
    cached_round_aliases: dict[int, int] = field(default_factory=dict)
    # Optional per-round cache depth and partial caching control.
    # Example: cached_round_depth={10: 2}, cached_round_x={10: 5} caches first 5 vectors at depth-2 in round 10.
    cached_round_depth: dict[int, int] = field(default_factory=dict)
    cached_round_x: dict[int, int] = field(default_factory=dict)

    # Static schedule
    valu_cap: int = 6
    alu_cap: int = 12
    flow_cap: int = 1
    load_cap: int = 2
    store_cap: int = 2
    total_cycles: int = 1312
    sched_seed: int = 0
    sched_jitter: float = 0.0
    sched_restarts: int = 1
    use_temp_deps: bool = True


SPEC_BASE = SpecBase()

OFFLOAD_DEFAULTS: dict[str, object] = {
    "offload_op1": 826,
    "include_setup": False,
    "setup_style": "packed",
    "total_cycles": 1174,
}


def with_offload_defaults(**overrides) -> SpecBase:
    merged = {**OFFLOAD_DEFAULTS, **overrides}
    return replace(SPEC_BASE, **merged)
