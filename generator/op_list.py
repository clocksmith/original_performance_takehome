from __future__ import annotations

from dataclasses import dataclass

from problem import HASH_STAGES, VLEN

from .ops import Op, OpLists

_ORDERED_OPS: list[Op] | None = None
_SEQ = 0


def _record(op: Op) -> None:
    global _SEQ
    if _ORDERED_OPS is None:
        return
    _SEQ += 1
    if op.meta is None:
        op.meta = {}
    op.meta["_seq"] = _SEQ
    _ORDERED_OPS.append(op)


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
    new_op = Op(engine="valu", slot=(op, dest, a, b), offloadable=offloadable, meta=meta)
    _record(new_op)
    ops.append(new_op)


def _add_vmuladd(ops: list[Op], dest: int, a: int, b: int, c: int, meta=None):
    new_op = Op(engine="valu", slot=("multiply_add", dest, a, b, c), meta=meta)
    _record(new_op)
    ops.append(new_op)


def _add_vselect(ops: list[Op], dest: int, cond: int, a: int, b: int, meta=None):
    new_op = Op(engine="flow", slot=("vselect", dest, cond, a, b), meta=meta)
    _record(new_op)
    ops.append(new_op)


def _add_flow_add_imm(ops: list[Op], dest: int, a: int, imm: int, meta=None):
    new_op = Op(engine="flow", slot=("add_imm", dest, a, imm), meta=meta)
    _record(new_op)
    ops.append(new_op)


def _add_vbroadcast(ops: list[Op], dest: int, src: int, meta=None):
    new_op = Op(engine="valu", slot=("vbroadcast", dest, src), meta=meta)
    _record(new_op)
    ops.append(new_op)


def _add_load(ops: list[Op], dest: int, addr: int, meta=None):
    new_op = Op(engine="load", slot=("load", dest, addr), meta=meta)
    _record(new_op)
    ops.append(new_op)


def _add_const(ops: list[Op], dest: int, val: int, meta=None):
    new_op = Op(engine="load", slot=("const", dest, val), meta=meta)
    _record(new_op)
    ops.append(new_op)


def _add_alu_vec(ops: list[Op], op: str, dest: int, a: int, b_scalar: int, meta=None):
    for lane in range(VLEN):
        new_op = Op(engine="alu", slot=(op, dest + lane, a + lane, b_scalar), meta=meta)
        _record(new_op)
        ops.append(new_op)


def _add_alu(ops: list[Op], op: str, dest: int, a: int, b: int, meta=None):
    new_op = Op(engine="alu", slot=(op, dest, a, b), meta=meta)
    _record(new_op)
    ops.append(new_op)


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
    new_op = Op(engine="load", slot=("vload", dest, addr), meta=meta)
    _record(new_op)
    ops.append(new_op)


def _add_load_offset(ops: list[Op], dest: int, addr: int, offset: int, meta=None):
    new_op = Op(engine="load", slot=("load_offset", dest, addr, offset), meta=meta)
    _record(new_op)
    ops.append(new_op)


def _add_vstore(ops: list[Op], addr: int, src: int, meta=None):
    new_op = Op(engine="store", slot=("vstore", addr, src), meta=meta)
    _record(new_op)
    ops.append(new_op)



def build_ops(spec, layout, ordered_ops: list[Op] | None = None) -> OpLists:
    global _ORDERED_OPS, _SEQ
    _ORDERED_OPS = ordered_ops
    _SEQ = 0
    valu_ops: list[Op] = []
    alu_ops: list[Op] = []
    flow_ops: list[Op] = []
    load_ops: list[Op] = []
    store_ops: list[Op] = []

    linear, bitwise = _split_hash_stages()

    if getattr(spec, "include_setup", True):
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

        # Cached node loads + broadcasts
        for i, vaddr in enumerate(layout.node_v):
            _add_alu(alu_ops, "+", layout.node_tmp, layout.forest_values_p, layout.const_s[i], meta={"setup": True, "node": i})
            _add_load(load_ops, layout.node_tmp, layout.node_tmp, meta={"setup": True, "node": i})
            _add_vbroadcast(valu_ops, vaddr, layout.node_tmp, meta={"setup": True, "node": i})

        # Initial vloads
        for v in range(spec.vectors):
            _add_vload(load_ops, layout.idx[v], layout.idx_ptr[v], meta={"vec": v})
            _add_vload(load_ops, layout.val[v], layout.val_ptr[v], meta={"vec": v})

    # Rounds (blocked, round-major when using shared temp buffers)
    if getattr(spec, "use_bitmask_selection", False):
        block = getattr(spec, "vector_block", 0)
        if block:
            vec_round_pairs = []
            for block_start in range(0, spec.vectors, block):
                block_end = min(spec.vectors, block_start + block)
                for r in range(spec.rounds):
                    for v in range(block_start, block_end):
                        vec_round_pairs.append((v, r))
        else:
            vec_round_pairs = [(v, r) for v in range(spec.vectors) for r in range(spec.rounds)]
    else:
        vec_round_pairs = [(v, r) for r in range(spec.rounds) for v in range(spec.vectors)]

    for v, r in vec_round_pairs:
        tmp = layout.tmp[v]
        sel = layout.sel[v]
        extra = None
        extra2 = None
        if layout.extra:
            extra = layout.extra[v % len(layout.extra)]
            if len(layout.extra) > 1:
                extra2 = layout.extra[(v + 1) % len(layout.extra)]
        idx = layout.idx[v]
        val = layout.val[v]

        if r in spec.base_cached_rounds:
            if r in (0, 11):
                _add_valu(valu_ops, "^", val, val, layout.node_v[0], meta={"round": r, "vec": v})
            elif r in (1, 12):
                if getattr(spec, "use_bitmask_selection", False) and extra is not None:
                    _add_alu_vec(alu_ops, "&", tmp, idx, layout.const_s[1], meta={"round": r, "vec": v})
                    _add_vselect(flow_ops, sel, tmp, layout.node_v[1], layout.node_v[2], meta={"round": r, "vec": v})
                    _add_valu(valu_ops, "^", val, val, sel, meta={"round": r, "vec": v})
                else:
                    nodes = [(1, layout.node_v[1]), (2, layout.node_v[2])]
                    _select_by_eq_alu(alu_ops, flow_ops, tmp, sel, idx, nodes, layout.const_s, layout.const_v, meta={"round": r, "vec": v})
                    _add_valu(valu_ops, "^", val, val, tmp, meta={"round": r, "vec": v})
            elif r in (2, 13):
                if getattr(spec, "use_bitmask_selection", False) and extra is not None:
                    _add_alu_vec(alu_ops, "&", tmp, idx, layout.const_s[1], meta={"round": r, "vec": v})
                    _add_vselect(flow_ops, sel, tmp, layout.node_v[3], layout.node_v[4], meta={"round": r, "vec": v})
                    _add_vselect(flow_ops, extra, tmp, layout.node_v[5], layout.node_v[6], meta={"round": r, "vec": v})
                    _add_alu_vec(alu_ops, "<", tmp, idx, layout.const_s[5], meta={"round": r, "vec": v})
                    _add_vselect(flow_ops, sel, tmp, sel, extra, meta={"round": r, "vec": v})
                    _add_valu(valu_ops, "^", val, val, sel, meta={"round": r, "vec": v})
                else:
                    nodes = [(i, layout.node_v[i]) for i in range(3, 7)]
                    _select_by_eq_alu(alu_ops, flow_ops, tmp, sel, idx, nodes, layout.const_s, layout.const_v, meta={"round": r, "vec": v})
                    _add_valu(valu_ops, "^", val, val, tmp, meta={"round": r, "vec": v})
            elif r in (3, 14):
                if getattr(spec, "use_bitmask_selection", False) and extra is not None:
                    # Lower half: nodes 7..10
                    _add_alu_vec(alu_ops, "&", tmp, idx, layout.const_s[1], meta={"round": r, "vec": v})
                    _add_vselect(flow_ops, sel, tmp, layout.node_v[7], layout.node_v[8], meta={"round": r, "vec": v})
                    if extra2 is not None:
                        _add_vselect(flow_ops, extra2, tmp, layout.node_v[9], layout.node_v[10], meta={"round": r, "vec": v})
                        _add_alu_vec(alu_ops, "<", tmp, idx, layout.const_s[9], meta={"round": r, "vec": v})
                        _add_vselect(flow_ops, sel, tmp, sel, extra2, meta={"round": r, "vec": v})
                    else:
                        _add_vselect(flow_ops, extra, tmp, layout.node_v[9], layout.node_v[10], meta={"round": r, "vec": v})
                        _add_alu_vec(alu_ops, "<", tmp, idx, layout.const_s[9], meta={"round": r, "vec": v})
                        _add_vselect(flow_ops, sel, tmp, sel, extra, meta={"round": r, "vec": v})

                    # Upper half: nodes 11..14 (use LSB selection)
                    _add_alu_vec(alu_ops, "&", tmp, idx, layout.const_s[1], meta={"round": r, "vec": v})
                    _add_vselect(flow_ops, extra, tmp, layout.node_v[11], layout.node_v[12], meta={"round": r, "vec": v})
                    _add_vselect(
                        flow_ops,
                        extra2 if extra2 is not None else sel,
                        tmp,
                        layout.node_v[13],
                        layout.node_v[14],
                        meta={"round": r, "vec": v},
                    )
                    _add_alu_vec(alu_ops, "<", tmp, idx, layout.const_s[13], meta={"round": r, "vec": v})
                    _add_vselect(
                        flow_ops,
                        extra,
                        tmp,
                        extra,
                        extra2 if extra2 is not None else sel,
                        meta={"round": r, "vec": v},
                    )

                    # Final select between lower and upper
                    _add_alu_vec(alu_ops, "<", tmp, idx, layout.const_s[11], meta={"round": r, "vec": v})
                    _add_vselect(flow_ops, sel, tmp, sel, extra, meta={"round": r, "vec": v})
                    _add_valu(valu_ops, "^", val, val, sel, meta={"round": r, "vec": v})
                else:
                    nodes = [(i, layout.node_v[i]) for i in range(7, 15)]
                    _select_by_eq_alu(alu_ops, flow_ops, tmp, sel, idx, nodes, layout.const_s, layout.const_v, meta={"round": r, "vec": v})
                    _add_valu(valu_ops, "^", val, val, tmp, meta={"round": r, "vec": v})
            else:
                # Shouldn't happen for current spec, but keep uncached fallback.
                _add_alu_vec(alu_ops, "+", sel, idx, layout.forest_values_p, meta={"round": r, "vec": v})
                for lane in range(VLEN):
                    _add_load_offset(load_ops, tmp, sel, lane, meta={"round": r, "vec": v, "lane": lane})
                _add_valu(valu_ops, "^", val, val, tmp, meta={"round": r, "vec": v})
        elif r in spec.depth4_cached_rounds and v < spec.x4:
            nodes = [(i, layout.node_v[i]) for i in range(15, 31)]
            _select_by_eq_alu(alu_ops, flow_ops, tmp, sel, idx, nodes, layout.const_s, layout.const_v, meta={"round": r, "vec": v})
            _add_valu(valu_ops, "^", val, val, tmp, meta={"round": r, "vec": v})
        else:
            # Uncached: load node values
            _add_alu_vec(alu_ops, "+", sel, idx, layout.forest_values_p, meta={"round": r, "vec": v})
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
            _add_valu(valu_ops, "+", tmp, tmp, one_v, meta={"round": r, "vec": v})
            _add_vmuladd(valu_ops, idx, idx, two_v, tmp, meta={"round": r, "vec": v})

    # Final stores
    for v in range(spec.vectors):
        _add_vstore(store_ops, layout.val_ptr[v], layout.val[v], meta={"vec": v})

    _ORDERED_OPS = None
    return OpLists(valu_ops=valu_ops, alu_ops=alu_ops, flow_ops=flow_ops, load_ops=load_ops, store_ops=store_ops)
