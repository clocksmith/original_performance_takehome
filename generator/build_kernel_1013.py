from __future__ import annotations

from .spec_1013 import SPEC_1013
from .scratch_layout import ScratchAlloc, build_layout
from .op_list import build_ops
from .offload import apply_offload
from .schedule_static import schedule_ops


def build_1013_instrs():
    spec = SPEC_1013
    scratch = ScratchAlloc()
    layout = build_layout(spec, scratch)

    ops = build_ops(spec, layout)
    off = apply_offload(spec, ops)
    instrs = schedule_ops(spec, off)
    return instrs
