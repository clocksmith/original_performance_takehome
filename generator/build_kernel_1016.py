from __future__ import annotations

from .spec_1016 import SPEC_1016, Spec1016
from .scratch_layout import ScratchAlloc, build_layout
from .op_list import build_ops
from .ops import Op
from .schedule_dep import schedule_ops_dep
from problem import VLEN


def build_1016_instrs(spec: Spec1016 | None = None):
    if spec is None:
        spec = SPEC_1016
    scratch = ScratchAlloc()
    layout = build_layout(spec, scratch)

    ordered_ops: list[Op] = []
    build_ops(spec, layout, ordered_ops=ordered_ops)

    final_ops: list[Op] = []
    offloaded = 0
    for op in ordered_ops:
        if op.offloadable and offloaded < spec.offload_op1:
            op_name, dest, a, b = op.slot
            for lane in range(VLEN):
                final_ops.append(
                    Op(
                        engine="alu",
                        slot=(op_name, dest + lane, a + lane, b + lane),
                        meta=op.meta,
                    )
                )
            offloaded += 1
        else:
            final_ops.append(op)

    instrs = schedule_ops_dep(final_ops)
    return instrs
