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
    offload_op1: int = 1506

    # Cached rounds
    base_cached_rounds: tuple[int, ...] = (0, 1, 2, 3, 11, 12, 13, 14)
    depth4_cached_rounds: tuple[int, ...] = (4,)

    # Static schedule
    valu_cap: int = 6
    alu_cap: int = 12
    flow_cap: int = 1
    load_cap: int = 2
    store_cap: int = 2
    total_cycles: int = 1013


SPEC_1013 = Spec1013()
