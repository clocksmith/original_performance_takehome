from __future__ import annotations

from dataclasses import dataclass


@dataclass(frozen=True)
class Spec1016:
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
    # Tuned for full-ISA schedule (no offload variant)
    offload_op1: int = 0
    # Offload controls
    offload_hash_op1: bool = True
    offload_parity: bool = False
    # Indexing mode (1-based) + pointer setup engine.
    idx_shifted: bool = False
    ptr_setup_engine: str = "flow"
    # Selection mode
    use_bitmask_selection: bool = False
    selection_mode: str = "eq"
    # Use incremental pointer for cached node preload to reduce const loads.
    node_ptr_incremental: bool = False
    extra_vecs: int = 2
    vector_block: int = 32
    # Override cached node count if needed.
    cached_nodes: int | None = None

    # Cached rounds
    base_cached_rounds: tuple[int, ...] = (0, 1, 2, 3, 11, 12, 13, 14)
    depth4_cached_rounds: tuple[int, ...] = (4,)

    # Static schedule
    valu_cap: int = 6
    alu_cap: int = 12
    flow_cap: int = 1
    load_cap: int = 2
    store_cap: int = 2
    total_cycles: int = 1312


SPEC_1016 = Spec1016()
