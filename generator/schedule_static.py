from __future__ import annotations

from collections import defaultdict
from typing import Any

from .offload import OffloadedOps


def _ensure_cycle(instrs: list[dict[str, list[tuple]]], idx: int) -> None:
    while len(instrs) <= idx:
        instrs.append({})


def _add_slot(instrs: list[dict[str, list[tuple]]], cycle: int, engine: str, slot: tuple[Any, ...]):
    _ensure_cycle(instrs, cycle)
    if engine not in instrs[cycle]:
        instrs[cycle][engine] = []
    instrs[cycle][engine].append(slot)


def schedule_ops(spec, ops: OffloadedOps) -> list[dict[str, list[tuple]]]:
    instrs: list[dict[str, list[tuple]]] = []

    # VALU: fixed mapping
    for m, op in enumerate(ops.valu_ops):
        cycle = m // spec.valu_cap
        slot = op.slot
        if cycle >= spec.total_cycles:
            raise RuntimeError("VALU schedule exceeds total cycles")
        _add_slot(instrs, cycle, "valu", slot)

    # ALU: sequential packing
    for k, op in enumerate(ops.alu_ops):
        cycle = k // spec.alu_cap
        if cycle >= spec.total_cycles:
            raise RuntimeError("ALU schedule exceeds total cycles")
        _add_slot(instrs, cycle, "alu", op.slot)

    # Flow: sequential
    for i, op in enumerate(ops.flow_ops):
        cycle = i
        if cycle >= spec.total_cycles:
            raise RuntimeError("Flow schedule exceeds total cycles")
        _add_slot(instrs, cycle, "flow", op.slot)

    # Load: sequential
    for i, op in enumerate(ops.load_ops):
        cycle = i // spec.load_cap
        if cycle >= spec.total_cycles:
            raise RuntimeError("Load schedule exceeds total cycles")
        _add_slot(instrs, cycle, "load", op.slot)

    # Store: sequential
    for i, op in enumerate(ops.store_ops):
        cycle = i // spec.store_cap
        if cycle >= spec.total_cycles:
            raise RuntimeError("Store schedule exceeds total cycles")
        _add_slot(instrs, cycle, "store", op.slot)

    # Ensure total length exactly total_cycles
    if len(instrs) < spec.total_cycles:
        instrs.extend({} for _ in range(spec.total_cycles - len(instrs)))

    return instrs
