from __future__ import annotations

from dataclasses import dataclass

from problem import VLEN

from .ops import Op, OpLists


@dataclass
class OffloadedOps:
    valu_ops: list[Op]
    alu_ops: list[Op]
    flow_ops: list[Op]
    load_ops: list[Op]
    store_ops: list[Op]

def _offload_category(op: Op) -> str | None:
    meta = op.meta or {}
    stage = meta.get("stage")
    if stage == "shift":
        return "hash_shift"
    if stage == "op1":
        return "hash_op1"
    if stage == "op2":
        return "hash_op2"
    # Non-hash offloadables (parity/node_xor) don't carry a stage tag today.
    if op.engine == "valu":
        op_name = op.slot[0]
        if op_name == "&":
            return "parity"
        if op_name == "^":
            return "node_xor"
    return None


def apply_offload_stream(spec, ops: list[Op]) -> list[Op]:
    """
    Apply vector->scalar offload to an in-order op stream.

    This must stay in sync with scripts/graph_dp_auto_search.build_final_ops and
    generator/build_kernel_base.build_base_instrs so energy_search scores match
    real kernels.
    """
    mode = getattr(spec, "offload_mode", "prefix")
    if mode not in {"prefix", "budgeted"}:
        raise ValueError(f"unknown offload_mode {mode!r}")

    budgets = {
        "hash_shift": int(getattr(spec, "offload_budget_hash_shift", 0)),
        "hash_op1": int(getattr(spec, "offload_budget_hash_op1", 0)),
        "hash_op2": int(getattr(spec, "offload_budget_hash_op2", 0)),
        "parity": int(getattr(spec, "offload_budget_parity", 0)),
        "node_xor": int(getattr(spec, "offload_budget_node_xor", 0)),
    }
    used = {k: 0 for k in budgets}

    offload_prefix_cap = int(getattr(spec, "offload_op1", 0))
    offloaded_prefix = 0

    out: list[Op] = []
    for op in ops:
        do_offload = False
        if op.offloadable:
            if mode == "prefix":
                do_offload = offloaded_prefix < offload_prefix_cap
            else:
                cat = _offload_category(op)
                if cat is not None:
                    cap = budgets.get(cat, 0)
                    do_offload = used[cat] < cap
                    if do_offload:
                        used[cat] += 1

        if not do_offload:
            out.append(op)
            continue

        # Expand to scalar ALU ops (one per lane).
        # NOTE: Only supports binary vector ops: (op, dest, a, b).
        op_name, dest, a, b = op.slot
        for lane in range(VLEN):
            out.append(
                Op(
                    engine="alu",
                    slot=(op_name, dest + lane, a + lane, b + lane),
                    meta=op.meta,
                )
            )
        offloaded_prefix += 1

    return out


def apply_offload(spec, ops: OpLists) -> OffloadedOps:
    alu_ops: list[Op] = list(ops.alu_ops)
    valu_ops: list[Op] = []

    offloaded = 0
    for op in ops.valu_ops:
        if op.offloadable and offloaded < spec.offload_op1:
            # Expand to scalar ALU ops (one per lane)
            _, dest, a, b = op.slot
            for lane in range(VLEN):
                alu_ops.append(Op(engine="alu", slot=(op.slot[0], dest + lane, a + lane, b + lane), meta=op.meta))
            offloaded += 1
        else:
            valu_ops.append(op)

    return OffloadedOps(
        valu_ops=valu_ops,
        alu_ops=alu_ops,
        flow_ops=ops.flow_ops,
        load_ops=ops.load_ops,
        store_ops=ops.store_ops,
    )
