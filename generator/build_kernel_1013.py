from __future__ import annotations

from .spec_1013 import SPEC_1013
from .scratch_layout import ScratchAlloc, build_layout
from .op_list import build_ops
from .ops import Op
from problem import SLOT_LIMITS, VLEN

from .schedule_dep import schedule_ops_dep


def build_1013_instrs():
    spec = SPEC_1013
    scratch = ScratchAlloc()
    layout = build_layout(spec, scratch)

    setup_instrs: list[dict[str, list[tuple]]] = []

    def _pack(engine: str, slots: list[tuple]) -> None:
        cap = SLOT_LIMITS[engine]
        for i in range(0, len(slots), cap):
            setup_instrs.append({engine: slots[i : i + cap]})

    # --- Setup phase (dependency-safe, packed per engine) ---
    # Load scalar constants.
    const_loads = [("const", addr, val) for val, addr in sorted(layout.const_s.items())]
    _pack("load", const_loads)

    # Load base pointers from mem[4], mem[5], mem[6].
    ptr_loads = [
        ("load", layout.forest_values_p, layout.const_s[4]),
        ("load", layout.inp_indices_p, layout.const_s[5]),
        ("load", layout.inp_values_p, layout.const_s[6]),
    ]
    _pack("load", ptr_loads)

    # Pointer setup (flow add_imm).
    flow_setup = [
        ("add_imm", layout.idx_ptr[0], layout.inp_indices_p, 0),
        ("add_imm", layout.val_ptr[0], layout.inp_values_p, 0),
    ]
    for v in range(1, spec.vectors):
        flow_setup.append(("add_imm", layout.idx_ptr[v], layout.idx_ptr[v - 1], VLEN))
        flow_setup.append(("add_imm", layout.val_ptr[v], layout.val_ptr[v - 1], VLEN))
    _pack("flow", flow_setup)

    # Cached node loads + broadcasts (sequential to preserve node_tmp dependency).
    for i, vaddr in enumerate(layout.node_v):
        setup_instrs.append({"alu": [("+", layout.node_tmp, layout.forest_values_p, layout.const_s[i])]})
        setup_instrs.append({"load": [("load", layout.node_tmp, layout.node_tmp)]})
        setup_instrs.append({"valu": [("vbroadcast", vaddr, layout.node_tmp)]})

    # Broadcast constants into vectors.
    const_v_broadcasts = [
        ("vbroadcast", vaddr, layout.const_s[val]) for val, vaddr in sorted(layout.const_v.items())
    ]
    _pack("valu", const_v_broadcasts)

    # Initial vloads (indices + values).
    vloads = []
    for v in range(spec.vectors):
        vloads.append(("vload", layout.idx[v], layout.idx_ptr[v]))
        vloads.append(("vload", layout.val[v], layout.val_ptr[v]))
    _pack("load", vloads)

    # --- Main scheduled phase ---
    ordered_ops: list[Op] = []
    build_ops(spec, layout, ordered_ops=ordered_ops)

    # Apply offload in-order to build the final op stream.
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

    pad_cycles = getattr(spec, "valu_pad_cycles", 0)
    if pad_cycles:
        pad_count = pad_cycles * spec.valu_cap
        pad_dest = layout.tmp[0]
        for _ in range(pad_count):
            final_ops.insert(0, Op(engine="valu", slot=("^", pad_dest, pad_dest, pad_dest)))

    instrs = schedule_ops_dep(final_ops)
    return setup_instrs + instrs
