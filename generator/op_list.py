from __future__ import annotations

from dataclasses import dataclass

from problem import HASH_STAGES, VLEN

from .ops import Op, OpLists


@dataclass(frozen=True)
class LinearStage:
    mult: int
    add: int


@dataclass(frozen=True)
class BitwiseStage:
    op1: str
    const: int
    op2: str
    shift_op: str
    shift: int


def _split_hash_stages() -> tuple[list[LinearStage], list[BitwiseStage]]:
    linear: list[LinearStage] = []
    bitwise: list[BitwiseStage] = []
    for op1, val1, op2, op3, val3 in HASH_STAGES:
        if op1 == "+" and op2 == "+":
            mult = (1 + (1 << val3)) % (2**32)
            linear.append(LinearStage(mult=mult, add=val1))
        else:
            bitwise.append(BitwiseStage(op1=op1, const=val1, op2=op2, shift_op=op3, shift=val3))
    return linear, bitwise


def _vaddr(base: int) -> tuple[int, ...]:
    return tuple(base + i for i in range(VLEN))


def _add_valu(ops: list[Op], op: str, dest: int, a: int, b: int, meta=None, offloadable=False):
    ops.append(Op(engine="valu", slot=(op, dest, a, b), offloadable=offloadable, meta=meta))


def _add_vmuladd(ops: list[Op], dest: int, a: int, b: int, c: int, meta=None):
    ops.append(Op(engine="valu", slot=("multiply_add", dest, a, b, c), meta=meta))


def _add_vselect(ops: list[Op], dest: int, cond: int, a: int, b: int, meta=None):
    ops.append(Op(engine="flow", slot=("vselect", dest, cond, a, b), meta=meta))


def _add_flow_add_imm(ops: list[Op], dest: int, a: int, imm: int, meta=None):
    ops.append(Op(engine="flow", slot=("add_imm", dest, a, imm), meta=meta))


def _add_vbroadcast(ops: list[Op], dest: int, src: int, meta=None):
    ops.append(Op(engine="valu", slot=("vbroadcast", dest, src), meta=meta))


def _add_load(ops: list[Op], dest: int, addr: int, meta=None):
    ops.append(Op(engine="load", slot=("load", dest, addr), meta=meta))


def _add_const(ops: list[Op], dest: int, val: int, meta=None):
    ops.append(Op(engine="load", slot=("const", dest, val), meta=meta))


def _add_alu_vec(ops: list[Op], op: str, dest: int, a: int, b_scalar: int, meta=None):
    for lane in range(VLEN):
        ops.append(Op(engine="alu", slot=(op, dest + lane, a + lane, b_scalar), meta=meta))


def _add_alu(ops: list[Op], op: str, dest: int, a: int, b: int, meta=None):
    ops.append(Op(engine="alu", slot=(op, dest, a, b), meta=meta))


def _select_by_eq_alu(
    alu_ops: list[Op],
    flow_ops: list[Op],
    tmp: int,
    sel: int,
    idx: int,
    nodes: list[tuple[int, int]],
    const_s: dict[int, int],
    const_v: dict[int, int],
    meta=None,
):
    if not nodes:
        raise ValueError("empty node list")
    base_addr = nodes[0][1]
    first = True
    for node_idx, node_addr in nodes[1:]:
        _add_alu_vec(alu_ops, "==", sel, idx, const_s[node_idx], meta=meta)
        if first:
            _add_vselect(flow_ops, tmp, sel, node_addr, base_addr, meta=meta)
            first = False
        else:
            _add_vselect(flow_ops, tmp, sel, node_addr, tmp, meta=meta)
    return tmp

def _add_vload(ops: list[Op], dest: int, addr: int, meta=None):
    ops.append(Op(engine="load", slot=("vload", dest, addr), meta=meta))


def _add_load_offset(ops: list[Op], dest: int, addr: int, offset: int, meta=None):
    ops.append(Op(engine="load", slot=("load_offset", dest, addr, offset), meta=meta))


def _add_vstore(ops: list[Op], addr: int, src: int, meta=None):
    ops.append(Op(engine="store", slot=("vstore", addr, src), meta=meta))



def build_ops(spec, layout) -> OpLists:
    valu_ops: list[Op] = []
    alu_ops: list[Op] = []
    flow_ops: list[Op] = []
    load_ops: list[Op] = []
    store_ops: list[Op] = []

    linear, bitwise = _split_hash_stages()

    # Scalar constants
    for val, addr in sorted(layout.const_s.items()):
        _add_const(load_ops, addr, val, meta={"setup": True, "const": val})

    # Load base pointers from mem[4], mem[5], mem[6]
    _add_load(load_ops, layout.forest_values_p, layout.const_s[4], meta={"setup": True, "ptr": "forest_values_p"})
    _add_load(load_ops, layout.inp_indices_p, layout.const_s[5], meta={"setup": True, "ptr": "inp_indices_p"})
    _add_load(load_ops, layout.inp_values_p, layout.const_s[6], meta={"setup": True, "ptr": "inp_values_p"})

    # Pointer setup (flow)
    _add_flow_add_imm(flow_ops, layout.idx_ptr[0], layout.inp_indices_p, 0, meta={"setup": True})
    _add_flow_add_imm(flow_ops, layout.val_ptr[0], layout.inp_values_p, 0, meta={"setup": True})
    for v in range(1, spec.vectors):
        _add_flow_add_imm(flow_ops, layout.idx_ptr[v], layout.idx_ptr[v - 1], VLEN, meta={"setup": True})
        _add_flow_add_imm(flow_ops, layout.val_ptr[v], layout.val_ptr[v - 1], VLEN, meta={"setup": True})

    # Broadcast constants into vectors
    for val, vaddr in sorted(layout.const_v.items()):
        _add_vbroadcast(valu_ops, vaddr, layout.const_s[val], meta={"setup": True, "const": val})

    # Broadcast forest base pointer into vector
    _add_vbroadcast(valu_ops, layout.forest_base_v, layout.forest_values_p, meta={"setup": True})

    # Cached node loads + broadcasts (0..30)
    for i, vaddr in enumerate(layout.node_v):
        _add_alu(alu_ops, "+", layout.node_tmp, layout.forest_values_p, layout.const_s[i], meta={"setup": True, "node": i})
        _add_load(load_ops, layout.node_tmp, layout.node_tmp, meta={"setup": True, "node": i})
        _add_vbroadcast(valu_ops, vaddr, layout.node_tmp, meta={"setup": True, "node": i})

    # Initial vloads
    for v in range(spec.vectors):
        _add_vload(load_ops, layout.idx[v], layout.idx_ptr[v], meta={"vec": v})
        _add_vload(load_ops, layout.val[v], layout.val_ptr[v], meta={"vec": v})

    # Rounds
    for r in range(spec.rounds):
        for v in range(spec.vectors):
            tmp = layout.tmp[v]
            sel = layout.sel[v]
            idx = layout.idx[v]
            val = layout.val[v]

            if r in spec.base_cached_rounds:
                if r in (0, 11):
                    _add_valu(valu_ops, "^", val, val, layout.node_v[0], meta={"round": r, "vec": v})
                elif r in (1, 12):
                    nodes = [(1, layout.node_v[1]), (2, layout.node_v[2])]
                    _select_by_eq_alu(alu_ops, flow_ops, tmp, sel, idx, nodes, layout.const_s, layout.const_v, meta={"round": r, "vec": v})
                    _add_valu(valu_ops, "^", val, val, tmp, meta={"round": r, "vec": v})
                elif r in (2, 13):
                    nodes = [(i, layout.node_v[i]) for i in range(3, 7)]
                    _select_by_eq_alu(alu_ops, flow_ops, tmp, sel, idx, nodes, layout.const_s, layout.const_v, meta={"round": r, "vec": v})
                    _add_valu(valu_ops, "^", val, val, tmp, meta={"round": r, "vec": v})
                elif r in (3, 14):
                    nodes = [(i, layout.node_v[i]) for i in range(7, 15)]
                    _select_by_eq_alu(alu_ops, flow_ops, tmp, sel, idx, nodes, layout.const_s, layout.const_v, meta={"round": r, "vec": v})
                    _add_valu(valu_ops, "^", val, val, tmp, meta={"round": r, "vec": v})
                else:
                    # Shouldn't happen for current spec, but keep uncached fallback.
                    _add_valu(valu_ops, "+", sel, idx, layout.forest_base_v, meta={"round": r, "vec": v})
                    for lane in range(VLEN):
                        _add_load_offset(load_ops, tmp, sel, lane, meta={"round": r, "vec": v, "lane": lane})
                    _add_valu(valu_ops, "^", val, val, tmp, meta={"round": r, "vec": v})
            elif r in spec.depth4_cached_rounds and v < spec.x4:
                nodes = [(i, layout.node_v[i]) for i in range(15, 31)]
                _select_by_eq_alu(alu_ops, flow_ops, tmp, sel, idx, nodes, layout.const_s, layout.const_v, meta={"round": r, "vec": v})
                _add_valu(valu_ops, "^", val, val, tmp, meta={"round": r, "vec": v})
            else:
                # Uncached: load node values
                _add_valu(valu_ops, "+", sel, idx, layout.forest_base_v, meta={"round": r, "vec": v})
                for lane in range(VLEN):
                    _add_load_offset(load_ops, tmp, sel, lane, meta={"round": r, "vec": v, "lane": lane})
                _add_valu(valu_ops, "^", val, val, tmp, meta={"round": r, "vec": v})

            # Hash stages
            lin_i = 0
            bit_i = 0
            for op1, _, op2, op3, _ in HASH_STAGES:
                if op1 == "+" and op2 == "+":
                    stage = linear[lin_i]
                    lin_i += 1
                    mult_v = layout.const_v[stage.mult]
                    add_v = layout.const_v[stage.add]
                    _add_vmuladd(valu_ops, val, val, mult_v, add_v, meta={"round": r, "vec": v, "stage": "linear"})
                else:
                    stage = bitwise[bit_i]
                    bit_i += 1
                    const_v = layout.const_v[stage.const]
                    shift_v = layout.const_v[stage.shift]
                    _add_valu(valu_ops, stage.shift_op, tmp, val, shift_v, meta={"round": r, "vec": v, "stage": "shift"})
                    _add_valu(valu_ops, stage.op1, val, val, const_v, meta={"round": r, "vec": v, "stage": "op1"}, offloadable=True)
                    _add_valu(valu_ops, stage.op2, val, val, tmp, meta={"round": r, "vec": v, "stage": "op2"})

            # Index update
            if r == 10 and spec.reset_on_valu:
                _add_valu(valu_ops, "^", idx, idx, idx, meta={"round": r, "vec": v})
            elif r != 15:
                one_v = layout.const_v[1]
                two_v = layout.const_v[2]
                _add_valu(valu_ops, "&", tmp, val, one_v, meta={"round": r, "vec": v})
                _add_vmuladd(valu_ops, idx, idx, two_v, tmp, meta={"round": r, "vec": v})

    # Final stores
    for v in range(spec.vectors):
        _add_vstore(store_ops, layout.val_ptr[v], layout.val[v], meta={"vec": v})

    return OpLists(valu_ops=valu_ops, alu_ops=alu_ops, flow_ops=flow_ops, load_ops=load_ops, store_ops=store_ops)
