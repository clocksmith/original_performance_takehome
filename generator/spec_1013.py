from __future__ import annotations

from dataclasses import dataclass


@dataclass(frozen=True)
class Spec1013:
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
    offload_op1: int = 826
    # Offload controls
    offload_hash_op1: bool = True
    offload_parity: bool = False
    use_bitmask_selection: bool = False
    # Use 1-based idx representation to drop the +1 in update.
    idx_shifted: bool = False
    # Pointer setup engine ("flow" or "alu").
    ptr_setup_engine: str = "flow"
    include_setup: bool = False
    valu_pad_cycles: int = 0
    # Process vectors in blocks to avoid temp aliasing with static schedule.
    # Round-major ordering to minimize cross-vector temp dependencies.
    vector_block: int = 32
    extra_vecs: int = 2
    # Override cached node count (e.g., top-3 caching uses 7 nodes).
    cached_nodes: int | None = None
    # Pointer setup engine ("flow" or "alu").
    ptr_setup_engine: str = "flow"

    # Cached rounds
    base_cached_rounds: tuple[int, ...] = (0, 1, 2, 3, 11, 12, 13, 14)
    depth4_cached_rounds: tuple[int, ...] = (4,)

    # Static schedule
    valu_cap: int = 6
    alu_cap: int = 12
    flow_cap: int = 1
    load_cap: int = 2
    store_cap: int = 2
    total_cycles: int = 1174


SPEC_1013 = Spec1013()
