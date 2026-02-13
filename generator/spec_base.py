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
    #   - "budgeted_spread": like "budgeted", but distributes the (typically small) set of
    #     non-offloaded ops across the stream to avoid a VALU tail.
    offload_mode: str = "prefix"
    # When True, represent offloaded vector ops as a single pseudo ALU op ("alu_vec", ...)
    # that consumes VLEN scalar ALU slots in one cycle. The scheduler accounts the true
    # per-cycle ALU capacity, and the pseudo op is expanded back into scalar slots when
    # emitting bundles for the simulator.
    offload_alu_vec: bool = False
    offload_budget_hash_shift: int = 0
    offload_budget_hash_op1: int = 0
    offload_budget_hash_op2: int = 0
    offload_budget_parity: int = 0
    offload_budget_node_xor: int = 0
    # Optional per-category position swaps for offload_mode="budgeted".
    # Positions are in category-local order among offloadable ops.
    # Each pair (a, b) means: keep position a on VALU and offload position b instead,
    # while preserving the same per-category offload budget.
    offload_budget_swaps: dict[str, tuple[tuple[int, int], ...]] = field(default_factory=dict)
    offload_hash_op1: bool = True
    offload_hash_shift: bool = False
    offload_hash_op2: bool = False
    offload_parity: bool = False
    offload_node_xor: bool = False
    use_bitmask_selection: bool = False
    # Selection modes: "eq", "bitmask", "bitmask_valu", "mask", "mask_precompute".
    selection_mode: str = "eq"
    # Use binary search tree for selection to reduce flow ops from N-1 to log2(N).
    # NOTE: currently not implemented in generator/op_list.py (kept for future work).
    binsearch_select: bool = False
    # Optional per-round selection override (e.g. {4: "mask_precompute"}).
    selection_mode_by_round: dict[int, str] = field(default_factory=dict)
    # Use VALU arithmetic to emulate vselect (reduces flow ops).
    valu_select: bool = False
    # Only lower leaf cached-node parity selects (the vselect_parity sites) into
    # a 1-op VALU muladd using precomputed node diffs. This avoids touching the
    # internal merge vselects (which often require the 2-op lowering).
    valu_select_leaf_pairs: bool = False
    # Optional: only apply VALU vselect-lowering for these rounds (by meta["round"]).
    # None means apply for all vselect sites.
    valu_select_rounds: tuple[int, ...] | None = None
    # Precompute (a-b) diffs for common cached-node vselect pairs.
    # Costs scratch (VLEN words each). Disable for large node caches to avoid overflow.
    valu_select_precompute_diffs: bool = True
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
    # Optional per-hash-stage overrides for xor stages (stage index in [0..]).
    hash_xor_style_by_stage: dict[int, str] = field(default_factory=dict)
    # - "inplace": baseline emission (stage op1 updates val in-place).
    # - "tmp_op1": compute stage op1 into a temp vector, then combine with shift into val.
    #   This preserves semantics but changes WAR/WAW dependencies, which can improve scheduling.
    hash_bitwise_style: str = "inplace"
    # Linear-stage lowering (stages with +,+,<< in HASH_STAGES):
    # - "muladd": single VALU multiply_add (current baseline)
    # - "shift_add": emit shift + add(const) + add(shifted), enabling
    #   offload via existing hash_shift/hash_op1/hash_op2 categories.
    hash_linear_style: str = "muladd"
    # Optional per-hash-stage overrides (stage index in [0..len(HASH_STAGES)-1]).
    # Only meaningful for bitwise stages (today: 1,3,5).
    hash_bitwise_style_by_stage: dict[int, str] = field(default_factory=dict)
    # Custom hash program (only used when hash_variant="prog").
    # Each op is a dict: {"op": "+|^|<<|>>|muladd|mov", "dst": "val|tmp|tmp2",
    #   "a": src, "b": src, "c": src (muladd only), "stage": "shift|op1|op2" (optional)}.
    # Sources can be "val|tmp|tmp2" or integer constants (vector consts).
    hash_prog: list[dict] | None = None
    # Named hash program preset used when hash_variant="prog" and hash_prog is None.
    # Presets: none, baseline, swap_xor, tmp_xor_const, tmp_op1, pingpong.
    hash_prog_variant: str = "none"
    # Use incremental pointer for cached node preload to reduce const loads.
    node_ptr_incremental: bool = False
    # Use 1-based idx representation to drop the +1 in update.
    idx_shifted: bool = False
    # Assume input indices are all zero and skip loading them from memory.
    # This matches the benchmark harness (Input.generate initializes indices to 0).
    assume_zero_indices: bool = False
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
    # Op emission order for generator/op_list.py:
    # - "auto": current behavior (vector-major when using shared selection temps)
    # - "vector_major": force (v, then r)
    # - "round_major": force (r, then v)
    # - "block": use vector_block ordering
    emit_order: str = "auto"
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
    sched_compact: bool = False
    # Dependency-family suffix applied by builder to sched_policy.
    # Variants: full, nowar, nowaw, nowaw_nowar, waw0, waw0_nowar, waw0all, waw0all_nowar.
    sched_deps_variant: str = "full"
    # Deterministic post-scheduler local repair.
    sched_repair_passes: int = 0
    sched_repair_try_swap: bool = False
    # Dependency scheduler policy (see generator/schedule_dep.py).
    # - "baseline": current critical-path list scheduling.
    # - "bottleneck_valu": bias non-VALU ops that unlock future VALU work.
    sched_policy: str = "baseline"
    # Optional early-stop threshold for the scheduler restarts loop.
    # If set, scheduling stops once a restart achieves <= this many cycles.
    sched_target_cycles: int | None = None
    use_temp_deps: bool = True
    # When use_temp_deps is enabled, generator/op_list.py can optionally add
    # extra serialization edges for shared selection scratch temps (extra_*).
    # Disabling this keeps only address-based deps for those temps.
    use_temp_deps_extras: bool = True
    # Optional temp-tag rewriting before scheduling (affects only temp hazards).
    # Modes: off, round, vec, op, window.
    temp_rename_mode: str = "off"
    temp_rename_window: int = 8


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
