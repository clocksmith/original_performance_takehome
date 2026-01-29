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
