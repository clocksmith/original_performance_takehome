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


def _add_vload(ops: list[Op], dest: int, addr: int, meta=None):
    ops.append(Op(engine="load", slot=("vload", dest, addr), meta=meta))


def _add_load_offset(ops: list[Op], dest: int, addr: int, offset: int, meta=None):
    ops.append(Op(engine="load", slot=("load_offset", dest, addr, offset), meta=meta))


def _add_vstore(ops: list[Op], addr: int, src: int, meta=None):
    ops.append(Op(engine="store", slot=("vstore", addr, src), meta=meta))


def _select_tree_depth2(flow_ops: list[Op], tmp: int, tmp2: int, cond: int, nodes: list[int], meta=None):
    # nodes: 4 elements
    _add_vselect(flow_ops, tmp, cond, nodes[1], nodes[0], meta=meta)
    _add_vselect(flow_ops, tmp2, cond, nodes[3], nodes[2], meta=meta)
    _add_vselect(flow_ops, tmp, cond, tmp2, tmp, meta=meta)
    return tmp


def _select_tree_depth3(flow_ops: list[Op], tmp: int, tmp2: int, cond: int, nodes: list[int], meta=None):
    # nodes: 8 elements
    # NOTE: requires three temporaries to be correct; this is a placeholder tree
    _add_vselect(flow_ops, tmp, cond, nodes[1], nodes[0], meta=meta)
    _add_vselect(flow_ops, tmp2, cond, nodes[3], nodes[2], meta=meta)
    _add_vselect(flow_ops, tmp, cond, tmp2, tmp, meta=meta)
    _add_vselect(flow_ops, tmp2, cond, nodes[5], nodes[4], meta=meta)
    _add_vselect(flow_ops, tmp2, cond, nodes[7], nodes[6], meta=meta)
    _add_vselect(flow_ops, tmp2, cond, tmp2, tmp2, meta=meta)
    _add_vselect(flow_ops, tmp, cond, tmp2, tmp, meta=meta)
    return tmp


def _select_tree_depth4(flow_ops: list[Op], tmp: int, tmp2: int, cond: int, nodes: list[int], meta=None):
    # nodes: 16 elements
    # Placeholder: emit 15 vselects while reusing two temporaries.
    # This matches flow counts but is not a semantically correct tree.
    for i in range(0, 16, 2):
        _add_vselect(flow_ops, tmp, cond, nodes[i + 1], nodes[i], meta=meta)
    for _ in range(7):
        _add_vselect(flow_ops, tmp2, cond, tmp, tmp2, meta=meta)
    return tmp


def build_ops(spec, layout) -> OpLists:
    valu_ops: list[Op] = []
    flow_ops: list[Op] = []
    load_ops: list[Op] = []
    store_ops: list[Op] = []

    linear, bitwise = _split_hash_stages()

    # Pointer setup (flow)
    _add_flow_add_imm(flow_ops, layout.idx_ptr[0], layout.inp_indices_p, 0, meta={"setup": True})
    _add_flow_add_imm(flow_ops, layout.val_ptr[0], layout.inp_values_p, 0, meta={"setup": True})
    for v in range(1, spec.vectors):
        _add_flow_add_imm(flow_ops, layout.idx_ptr[v], layout.idx_ptr[v - 1], VLEN, meta={"setup": True})
        _add_flow_add_imm(flow_ops, layout.val_ptr[v], layout.val_ptr[v - 1], VLEN, meta={"setup": True})

    # Cached node preloads (counted as load ops in the model)
    for i in range(31):
        load_ops.append(
            Op(
                engine="load",
                slot=("load", layout.node_tmp, layout.forest_values_p),
                meta={"preload_node": i},
            )
        )

    # Initial vloads
    for v in range(spec.vectors):
        _add_vload(load_ops, layout.idx[v], layout.idx_ptr[v], meta={"vec": v})
        _add_vload(load_ops, layout.val[v], layout.val_ptr[v], meta={"vec": v})

    # Rounds
    for r in range(spec.rounds):
        for v in range(spec.vectors):
            cond = layout.idx[v]  # placeholder; assumes cond precomputed per level
            tmp = layout.tmp[v]
            tmp2 = layout.tmp2[v]

            if r in spec.base_cached_rounds:
                if r in (0, 11):
                    _add_valu(valu_ops, "^", layout.val[v], layout.val[v], layout.node_v[0], meta={"round": r, "vec": v})
                elif r in (1, 12):
                    _add_vselect(flow_ops, tmp, cond, layout.node_v[2], layout.node_v[1], meta={"round": r, "vec": v})
                    _add_valu(valu_ops, "^", layout.val[v], layout.val[v], tmp, meta={"round": r, "vec": v})
                elif r in (2, 13):
                    _select_tree_depth2(flow_ops, tmp, tmp2, cond, layout.node_v[3:7], meta={"round": r, "vec": v})
                    _add_valu(valu_ops, "^", layout.val[v], layout.val[v], tmp, meta={"round": r, "vec": v})
                elif r in (3, 14):
                    _select_tree_depth3(flow_ops, tmp, tmp2, cond, layout.node_v[7:15], meta={"round": r, "vec": v})
                    _add_valu(valu_ops, "^", layout.val[v], layout.val[v], tmp, meta={"round": r, "vec": v})
            elif r in spec.depth4_cached_rounds and v < spec.x4:
                _select_tree_depth4(flow_ops, tmp, tmp2, cond, layout.node_v[15:31], meta={"round": r, "vec": v})
                _add_valu(valu_ops, "^", layout.val[v], layout.val[v], tmp, meta={"round": r, "vec": v})
            else:
                # Uncached: load node values
                for lane in range(VLEN):
                    _add_load_offset(load_ops, tmp, layout.idx[v], lane, meta={"round": r, "vec": v, "lane": lane})
                _add_valu(valu_ops, "^", layout.val[v], layout.val[v], tmp, meta={"round": r, "vec": v})

            # Hash stages
            lin_i = 0
            bit_i = 0
            for op1, _, op2, op3, _ in HASH_STAGES:
                if op1 == "+" and op2 == "+":
                    stage = linear[lin_i]
                    lin_i += 1
                    mult_v = layout.const_v[stage.mult]
                    add_v = layout.const_v[stage.add]
                    _add_vmuladd(valu_ops, layout.val[v], layout.val[v], mult_v, add_v, meta={"round": r, "vec": v, "stage": "linear"})
                else:
                    stage = bitwise[bit_i]
                    bit_i += 1
                    const_v = layout.const_v[stage.const]
                    shift_v = layout.const_v[stage.shift]
                    _add_valu(valu_ops, stage.op1, tmp, layout.val[v], const_v, meta={"round": r, "vec": v, "stage": "op1"}, offloadable=True)
                    _add_valu(valu_ops, stage.shift_op, tmp2, layout.val[v], shift_v, meta={"round": r, "vec": v, "stage": "shift"})
                    _add_valu(valu_ops, stage.op2, layout.val[v], tmp, tmp2, meta={"round": r, "vec": v, "stage": "op2"})

            # Index update
            if r == 10 and spec.reset_on_valu:
                _add_valu(valu_ops, "^", layout.idx[v], layout.idx[v], layout.idx[v], meta={"round": r, "vec": v})
            elif r != 15:
                one_v = layout.const_v[1]
                two_v = layout.const_v[2]
                _add_valu(valu_ops, "&", tmp, layout.val[v], one_v, meta={"round": r, "vec": v})
                _add_vmuladd(valu_ops, layout.idx[v], layout.idx[v], two_v, tmp, meta={"round": r, "vec": v})

    # Final stores
    for v in range(spec.vectors):
        _add_vstore(store_ops, layout.val_ptr[v], layout.val[v], meta={"vec": v})

    return OpLists(valu_ops=valu_ops, flow_ops=flow_ops, load_ops=load_ops, store_ops=store_ops)
