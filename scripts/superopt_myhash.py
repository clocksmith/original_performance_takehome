from __future__ import annotations

"""
CEGIS-style superoptimizer for the full `myhash` function.

Goal: find a straight-line program with <= N ops that matches `problem.myhash`
for all 32-bit inputs, under a restricted opset and constant pool.

Run with the repo venv so `z3-solver` is available:
  ./.venv/bin/python scripts/superopt_myhash.py --n-ops 11
"""

import argparse
import os
import random
import sys
from array import array
from dataclasses import dataclass
from typing import Callable, Iterable

import z3

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
if ROOT not in sys.path:
    sys.path.insert(0, ROOT)

from problem import HASH_STAGES

MASK32 = (1 << 32) - 1


def _parse_list(s: str) -> list[str]:
    return [t.strip() for t in s.split(",") if t.strip()]


def _normalize_op(op: str) -> str:
    op = op.strip().lower()
    return {
        "add": "+",
        "+": "+",
        "xor": "^",
        "^": "^",
        "shl": "<<",
        "<<": "<<",
        "shr": ">>",
        ">>": ">>",
        "muladd": "muladd",
        "mov": "mov",
    }.get(op, op)


def _u32(x: int) -> int:
    return x & MASK32


def _u32(x: int) -> int:
    return x & MASK32


def _bv(x: int, width: int) -> z3.BitVecNumRef:
    mask = (1 << width) - 1
    return z3.BitVecVal(x & mask, width)


def _sel(values: list[z3.BitVecRef], idx: z3.IntNumRef | z3.ArithRef) -> z3.BitVecRef:
    assert values
    out: z3.BitVecRef = values[-1]
    for i in range(len(values) - 2, -1, -1):
        out = z3.If(idx == i, values[i], out)
    return out


DEFAULT_BINOPS = ["+", "^", "<<", ">>", "*"]


def _apply_binop(op: str, a: z3.BitVecRef, b: z3.BitVecRef) -> z3.BitVecRef:
    if op == "+":
        return a + b
    if op == "^":
        return a ^ b
    if op == "<<":
        return a << b
    if op == ">>":
        return z3.LShR(a, b)
    if op == "*":
        return a * b
    raise ValueError(f"unknown op: {op!r}")


DEFAULT_CONSTS = sorted(
    {
        0,
        1,
        2,
        3,
        4,
        8,
        16,
        32,
        # shift counts
        12,
        19,
        5,
        9,
        3,
        16,
        # hash constants
        0x7ED55D16,
        0xC761C23C,
        0x165667B1,
        0xD3A2646C,
        0xFD7046C5,
        0xB55A4F09,
        # mul constants for linear stages
        1 + (1 << 12),
        1 + (1 << 5),
        1 + (1 << 3),
    }
)

MINIMAL_CONSTS = sorted(
    {
        # small identities (keep 0/1 to avoid over-constraining)
        0,
        1,
        # shift counts
        12,
        19,
        5,
        9,
        3,
        16,
        # hash constants
        0x7ED55D16,
        0xC761C23C,
        0x165667B1,
        0xD3A2646C,
        0xFD7046C5,
        0xB55A4F09,
        # mul constants for linear stages
        1 + (1 << 12),
        1 + (1 << 5),
        1 + (1 << 3),
    }
)


@dataclass(frozen=True)
class Program:
    ops: list[str]
    a_idx: list[int]
    b_idx: list[int]
    c_idx: list[int]


@dataclass(frozen=True)
class Program2Reg:
    ops: list[str]
    dst_idx: list[int]
    a_idx: list[int]
    b_idx: list[int]
    c_idx: list[int]


@dataclass(frozen=True)
class MitmInst:
    op: str
    dst: str
    a: str | int
    b: str | int
    c: str | int | None
    reads_tmp: bool
    writes_tmp: bool


def _target_hash_block(a: z3.BitVecRef, *, start: int, count: int, width: int) -> z3.BitVecRef:
    out = a
    end = start + count
    for op1, val1, op2, op3, val3 in HASH_STAGES[start:end]:
        op1_out = _apply_binop(op1, out, _bv(val1, width))
        shift_out = _apply_binop(op3, out, _bv(val3, width))
        out = _apply_binop(op2, op1_out, shift_out)
    return out


def _target_myhash(a: z3.BitVecRef, *, width: int) -> z3.BitVecRef:
    return _target_hash_block(a, start=0, count=len(HASH_STAGES), width=width)


def _consts_for_stages(stage_indices: Iterable[int]) -> list[int]:
    consts = {0, 1}
    for idx in stage_indices:
        op1, val1, op2, op3, val3 = HASH_STAGES[idx]
        consts.add(val1)
        consts.add(val3)
        if op1 == "+" and op2 == "+" and op3 == "<<":
            consts.add(1 + (1 << val3))
    return sorted(consts)


def _eval_myhash_u32(a: int) -> int:
    a = _u32(a)
    for op1, val1, op2, op3, val3 in HASH_STAGES:
        if op3 == "<<":
            shifted = _u32(a << val3)
        else:
            shifted = _u32(a >> val3)
        if op1 == "+":
            op1_out = _u32(a + val1)
        else:
            op1_out = _u32(a ^ val1)
        if op2 == "+":
            a = _u32(op1_out + shifted)
        else:
            a = _u32(op1_out ^ shifted)
    return a


def _apply_u32(op: str, a: int, b: int, c: int | None = None) -> int:
    if op == "+":
        return _u32(a + b)
    if op == "^":
        return _u32(a ^ b)
    if op == "<<":
        return _u32(a << b)
    if op == ">>":
        return _u32(a >> b)
    if op == "muladd":
        assert c is not None
        return _u32(a * b + c)
    raise ValueError(f"unknown op: {op!r}")


def _apply_uw(op: str, a: int, b: int, c: int | None, *, mask: int) -> int:
    if op == "+":
        return (a + b) & mask
    if op == "^":
        return (a ^ b) & mask
    if op == "<<":
        return (a << b) & mask
    if op == ">>":
        return (a >> b) & mask
    if op == "*":
        return (a * b) & mask
    if op == "muladd":
        assert c is not None
        return (a * b + c) & mask
    raise ValueError(f"unknown op: {op!r}")


def _eval_myhash_width(a: int, *, width: int) -> int:
    mask = (1 << width) - 1
    a &= mask
    for op1, val1, op2, op3, val3 in HASH_STAGES:
        if op3 == "<<":
            shifted = (a << val3) & mask
        else:
            shifted = (a >> val3) & mask
        if op1 == "+":
            op1_out = (a + val1) & mask
        else:
            op1_out = (a ^ val1) & mask
        if op2 == "+":
            a = (op1_out + shifted) & mask
        else:
            a = (op1_out ^ shifted) & mask
    return a & mask


def _pack_table(table: list[int], *, width: int) -> bytes:
    if width <= 8:
        return bytes(table)
    if width <= 16:
        return array("H", table).tobytes()
    return array("I", table).tobytes()


def _eval_prog_table_val(
    prog: list[dict],
    *,
    width: int,
    inputs: list[int],
) -> list[int]:
    mask = (1 << width) - 1
    val = inputs[:]
    tmp = [0] * len(inputs)

    def _src(src, i: int) -> int:
        if src == "val":
            return val[i]
        if src == "tmp":
            return tmp[i]
        if isinstance(src, int):
            return src & mask
        raise ValueError(f"bad src {src!r}")

    for inst in prog:
        op = inst["op"]
        dst = inst["dst"]
        a = inst.get("a")
        b = inst.get("b")
        c = inst.get("c")
        out = [0] * len(inputs)
        if op == "muladd":
            if c is None:
                raise ValueError("muladd requires c")
            for i in range(len(inputs)):
                out[i] = _apply_uw(op, _src(a, i), _src(b, i), _src(c, i), mask=mask)
        else:
            for i in range(len(inputs)):
                out[i] = _apply_uw(op, _src(a, i), _src(b, i), None, mask=mask)
        if dst == "val":
            val = out
        elif dst == "tmp":
            tmp = out
        else:
            raise ValueError(f"bad dst {dst!r}")
    return val


def _mitm_build_insts(
    *,
    consts: list[int],
    shift_vals: set[int],
    allow_val_b: bool,
    allow_tmp_a: bool,
    allow_tmp_b: bool,
    shift_dst_tmp: bool,
    shift_src_val: bool,
    allow_muladd: bool,
    allow_mul: bool,
    restrict_ops: set[str] | None,
) -> list[MitmInst]:
    insts: list[MitmInst] = []

    def add_inst(op: str, dst: str, a: str | int, b: str | int, c: str | int | None = None):
        reads_tmp = (a == "tmp") or (b == "tmp") or (c == "tmp")
        writes_tmp = dst == "tmp"
        insts.append(MitmInst(op=op, dst=dst, a=a, b=b, c=c, reads_tmp=reads_tmp, writes_tmp=writes_tmp))

    consts = list(consts)
    shift_consts = sorted([c for c in shift_vals if 0 <= c <= 31])
    allow_ops = restrict_ops

    for op in ("<<", ">>"):
        if allow_ops is not None and op not in allow_ops:
            continue
        dst = "tmp" if shift_dst_tmp else "val"
        a_vals = ["val"] if shift_src_val else ["val", "tmp"]
        for a in a_vals:
            for k in shift_consts:
                add_inst(op, dst, a, k)

    for op in ("^", "+"):
        if allow_ops is not None and op not in allow_ops:
            continue
        b_vals: list[str | int] = list(consts)
        if allow_tmp_b:
            b_vals.append("tmp")
        if allow_val_b:
            b_vals.append("val")
        a_vals = ["val"] + (["tmp"] if allow_tmp_a else [])
        for a in a_vals:
            for b in b_vals:
                add_inst(op, "val", a, b)

    if allow_mul and (allow_ops is None or "*" in allow_ops):
        b_vals = list(consts)
        if allow_tmp_b:
            b_vals.append("tmp")
        if allow_val_b:
            b_vals.append("val")
        a_vals = ["val"] + (["tmp"] if allow_tmp_a else [])
        for a in a_vals:
            for b in b_vals:
                add_inst("*", "val", a, b)

    if allow_muladd and (allow_ops is None or "muladd" in allow_ops):
        a_vals = ["val"] + (["tmp"] if allow_tmp_a else [])
        for a in a_vals:
            for b in consts:
                for c in consts:
                    add_inst("muladd", "val", a, b, c)

    return insts


def _mitm_apply_inst_table(
    inst: MitmInst,
    *,
    width: int,
    val: list[int],
    tmp: list[int],
) -> tuple[list[int], list[int]]:
    mask = (1 << width) - 1
    n = len(val)

    def _src(src, i: int) -> int:
        if src == "val":
            return val[i]
        if src == "tmp":
            return tmp[i]
        if isinstance(src, int):
            return src & mask
        raise ValueError(f"bad src {src!r}")

    out = [0] * n
    if inst.op == "muladd":
        if inst.c is None:
            raise ValueError("muladd requires c")
        for i in range(n):
            out[i] = _apply_uw(inst.op, _src(inst.a, i), _src(inst.b, i), _src(inst.c, i), mask=mask)
    else:
        for i in range(n):
            out[i] = _apply_uw(inst.op, _src(inst.a, i), _src(inst.b, i), None, mask=mask)

    if inst.dst == "val":
        return out, tmp
    if inst.dst == "tmp":
        return val, out
    raise ValueError(f"bad dst {inst.dst!r}")


def _mitm_enum_programs(
    *,
    length: int,
    width: int,
    inputs: list[int],
    insts: list[MitmInst],
    allow_tmp_before_shift: bool,
    max_unique: int,
    budget: dict[str, int] | None,
) -> list[tuple[list[MitmInst], list[int], dict[str, int]]]:
    init_val = inputs[:]
    init_tmp = [0] * len(inputs)
    key = (False, _pack_table(init_val, width=width) + _pack_table(init_tmp, width=width))
    states: dict[tuple[bool, bytes], tuple[list[int], list[int], list[MitmInst], dict[str, int], bool]] = {
        key: (init_val, init_tmp, [], {}, False)
    }
    for _ in range(length):
        next_states: dict[tuple[bool, bytes], tuple[list[int], list[int], list[MitmInst], dict[str, int], bool]] = {}
        for val, tmp, prog, counts, tmp_ready in states.values():
            for inst in insts:
                if inst.reads_tmp and not tmp_ready and not allow_tmp_before_shift:
                    continue
                if budget is not None and inst.op not in budget:
                    continue
                if budget is not None:
                    used = counts.get(inst.op, 0)
                    if used + 1 > budget[inst.op]:
                        continue
                val2, tmp2 = _mitm_apply_inst_table(inst, width=width, val=val, tmp=tmp)
                new_ready = tmp_ready or inst.writes_tmp
                new_counts = counts
                if budget is not None:
                    new_counts = dict(counts)
                    new_counts[inst.op] = new_counts.get(inst.op, 0) + 1
                new_prog = prog + [inst]
                new_key = (new_ready, _pack_table(val2, width=width) + _pack_table(tmp2, width=width))
                if new_key in next_states:
                    continue
                next_states[new_key] = (val2, tmp2, new_prog, new_counts, new_ready)
                if max_unique and len(next_states) >= max_unique:
                    break
            if max_unique and len(next_states) >= max_unique:
                break
        states = next_states
        if not states:
            break

    out: list[tuple[list[MitmInst], list[int], dict[str, int]]] = []
    for val, _tmp, prog, counts, _ready in states.values():
        out.append((prog, val, counts))
    return out


def _mitm_prog_to_hash_prog(prog: list[MitmInst]) -> list[dict]:
    out: list[dict] = []
    for inst in prog:
        entry = {"op": inst.op, "dst": inst.dst, "a": inst.a, "b": inst.b}
        if inst.op == "muladd":
            if inst.c is None:
                raise ValueError("muladd requires c")
            entry["c"] = inst.c
        out.append(entry)
    return out


def _mitm_inverse_perm(table: list[int], *, size: int) -> list[int] | None:
    inv = [-1] * size
    for i, v in enumerate(table):
        if v < 0 or v >= size:
            return None
        if inv[v] != -1:
            return None
        inv[v] = i
    return inv


def mitm_search(
    *,
    width: int,
    l1: int,
    l2: int,
    consts: list[int],
    shift_vals: set[int],
    allow_tmp_before_shift: bool,
    allow_val_b: bool,
    allow_tmp_a: bool,
    shift_dst_tmp: bool,
    shift_src_val: bool,
    allow_muladd: bool,
    allow_mul: bool,
    budget: dict[str, int] | None,
    max_unique: int,
) -> list[dict] | None:
    inputs = list(range(1 << width))
    target = [_eval_myhash_width(a, width=width) for a in inputs]

    restrict_ops = set(budget.keys()) if budget is not None else None
    insts = _mitm_build_insts(
        consts=consts,
        shift_vals=shift_vals,
        allow_val_b=allow_val_b,
        allow_tmp_a=allow_tmp_a,
        allow_tmp_b=True,
        shift_dst_tmp=shift_dst_tmp,
        shift_src_val=shift_src_val,
        allow_muladd=allow_muladd,
        allow_mul=allow_mul,
        restrict_ops=restrict_ops,
    )

    g_states = _mitm_enum_programs(
        length=l2,
        width=width,
        inputs=inputs,
        insts=insts,
        allow_tmp_before_shift=allow_tmp_before_shift,
        max_unique=max_unique,
        budget=budget,
    )
    g_map: dict[bytes, tuple[list[MitmInst], dict[str, int]]] = {}
    for prog, val_table, counts in g_states:
        key = _pack_table(val_table, width=width)
        if key not in g_map:
            g_map[key] = (prog, counts)

    h_states = _mitm_enum_programs(
        length=l1,
        width=width,
        inputs=inputs,
        insts=insts,
        allow_tmp_before_shift=allow_tmp_before_shift,
        max_unique=max_unique,
        budget=budget,
    )
    total_budget = sum(budget.values()) if budget is not None else None
    if total_budget is not None and total_budget != l1 + l2:
        raise SystemExit("mitm: budget sum must equal l1+l2")

    for h_prog, h_table, h_counts in h_states:
        inv = _mitm_inverse_perm(h_table, size=len(inputs))
        if inv is None:
            continue
        g_req = [target[inv[y]] for y in range(len(inputs))]
        key = _pack_table(g_req, width=width)
        hit = g_map.get(key)
        if hit is None:
            continue
        g_prog, g_counts = hit
        if budget is not None:
            ok = True
            for op, cnt in budget.items():
                if h_counts.get(op, 0) + g_counts.get(op, 0) != cnt:
                    ok = False
                    break
            if not ok:
                continue
        full_prog = _mitm_prog_to_hash_prog(h_prog + g_prog)
        return full_prog
    return None


def _initial_samples(*, seed: int, n: int) -> list[int]:
    edge = [
        0,
        1,
        2,
        3,
        (1 << 31) - 1,
        1 << 31,
        (1 << 31) + 1,
        (1 << 32) - 2,
        (1 << 32) - 1,
    ]
    rng = random.Random(seed)
    extra = [rng.getrandbits(32) for _ in range(max(0, n - len(edge)))]
    return edge + extra


def _decode_model(
    m: z3.ModelRef,
    sym: dict[str, z3.ExprRef],
    n_ops: int,
    *,
    binops: list[str],
    op_muladd: int | None,
) -> Program:
    ops: list[str] = []
    a_idx: list[int] = []
    b_idx: list[int] = []
    c_idx: list[int] = []
    for i in range(n_ops):
        op_code = int(m.eval(sym[f"op{i}"], model_completion=True).as_long())
        if op_muladd is not None and op_code == op_muladd:
            op_name = "muladd"
        else:
            op_name = binops[op_code]
        ops.append(op_name)
        a_idx.append(int(m.eval(sym[f"a{i}"], model_completion=True).as_long()))
        b_idx.append(int(m.eval(sym[f"b{i}"], model_completion=True).as_long()))
        c_idx.append(int(m.eval(sym[f"c{i}"], model_completion=True).as_long()))
    return Program(ops=ops, a_idx=a_idx, b_idx=b_idx, c_idx=c_idx)


def _decode_model_2reg(
    m: z3.ModelRef,
    sym: dict[str, z3.ExprRef],
    n_ops: int,
    *,
    binops: list[str],
    op_muladd: int | None,
) -> Program2Reg:
    ops: list[str] = []
    dst_idx: list[int] = []
    a_idx: list[int] = []
    b_idx: list[int] = []
    c_idx: list[int] = []
    for i in range(n_ops):
        op_code = int(m.eval(sym[f"op{i}"], model_completion=True).as_long())
        if op_muladd is not None and op_code == op_muladd:
            op_name = "muladd"
        else:
            op_name = binops[op_code]
        ops.append(op_name)
        dst_idx.append(int(m.eval(sym[f"dst{i}"], model_completion=True).as_long()))
        a_idx.append(int(m.eval(sym[f"a{i}"], model_completion=True).as_long()))
        b_idx.append(int(m.eval(sym[f"b{i}"], model_completion=True).as_long()))
        c_idx.append(int(m.eval(sym[f"c{i}"], model_completion=True).as_long()))
    return Program2Reg(ops=ops, dst_idx=dst_idx, a_idx=a_idx, b_idx=b_idx, c_idx=c_idx)


def _pretty_program(prog: Program, consts: list[int]) -> str:
    lines: list[str] = []
    lines.append("const pool:")
    for i, v in enumerate(consts):
        lines.append(f"  k{i} = 0x{v:08x}")

    def src_label(srcs: list[str], idx: int) -> str:
        if idx < 0 or idx >= len(srcs):
            return f"<bad:{idx}>"
        return srcs[idx]

    for i, op in enumerate(prog.ops):
        srcs = ["a"] + [f"t{j}" for j in range(i)] + [f"k{j}" for j in range(len(consts))]
        a = src_label(srcs, prog.a_idx[i])
        b = src_label(srcs, prog.b_idx[i])
        c = src_label(srcs, prog.c_idx[i])
        if op == "muladd":
            lines.append(f"t{i} = muladd({a}, {b}, {c})")
        else:
            lines.append(f"t{i} = {op}({a}, {b})")
    return "\n".join(lines)


def _pretty_program_2reg(prog: Program2Reg, consts: list[int]) -> str:
    lines: list[str] = []
    lines.append("const pool:")
    for i, v in enumerate(consts):
        lines.append(f"  k{i} = 0x{v:08x}")

    def src_label(srcs: list[str], idx: int) -> str:
        if idx < 0 or idx >= len(srcs):
            return f"<bad:{idx}>"
        return srcs[idx]

    for i, op in enumerate(prog.ops):
        srcs = ["val", "tmp"] + [f"k{j}" for j in range(len(consts))]
        a = src_label(srcs, prog.a_idx[i])
        b = src_label(srcs, prog.b_idx[i])
        c = src_label(srcs, prog.c_idx[i])
        dst = "val" if prog.dst_idx[i] == 0 else "tmp"
        if op == "muladd":
            lines.append(f"{dst} = muladd({a}, {b}, {c})")
        else:
            lines.append(f"{dst} = {op}({a}, {b})")
    return "\n".join(lines)


def _build_template(
    *,
    n_ops: int,
    consts: list[int],
    binops: list[str],
    op_muladd: int | None,
    width: int,
    const_syms_override: list[z3.BitVecRef] | None = None,
) -> tuple[dict[str, z3.ExprRef], z3.BitVecRef, z3.BitVecRef]:
    a = z3.BitVec("a", width)
    const_syms = const_syms_override if const_syms_override is not None else [_bv(v, width) for v in consts]

    sym: dict[str, z3.ExprRef] = {}
    for i, k in enumerate(const_syms):
        sym[f"k{i}"] = k
    temps: list[z3.BitVecRef] = []

    for i in range(n_ops):
        op_i = z3.Int(f"op{i}")
        a_i = z3.Int(f"a{i}")
        b_i = z3.Int(f"b{i}")
        c_i = z3.Int(f"c{i}")
        sym[f"op{i}"] = op_i
        sym[f"a{i}"] = a_i
        sym[f"b{i}"] = b_i
        sym[f"c{i}"] = c_i

        srcs = [a] + temps + const_syms
        x = _sel(srcs, a_i)
        y = _sel(srcs, b_i)
        z = _sel(srcs, c_i)

        bin_exprs = [_apply_binop(op, x, y) for op in binops]
        if op_muladd is None:
            t = _sel(bin_exprs, op_i)
        else:
            t = z3.If(op_i == op_muladd, (x * y) + z, _sel(bin_exprs, op_i))
        temps.append(t)

    return sym, a, temps[-1]


def _build_template_2reg(
    *,
    n_ops: int,
    consts: list[int],
    binops: list[str],
    op_muladd: int | None,
    width: int,
    const_syms_override: list[z3.BitVecRef] | None = None,
) -> tuple[dict[str, z3.ExprRef], z3.BitVecRef, z3.BitVecRef, list[z3.BoolRef]]:
    a = z3.BitVec("a", width)
    const_syms = const_syms_override if const_syms_override is not None else [_bv(v, width) for v in consts]

    sym: dict[str, z3.ExprRef] = {}
    for i, k in enumerate(const_syms):
        sym[f"k{i}"] = k
    tmp_defined_flags: list[z3.BoolRef] = []

    val = a
    tmp = z3.BitVec("tmp_init", width)
    tmp_defined = z3.BoolVal(False)

    for i in range(n_ops):
        op_i = z3.Int(f"op{i}")
        dst_i = z3.Int(f"dst{i}")
        a_i = z3.Int(f"a{i}")
        b_i = z3.Int(f"b{i}")
        c_i = z3.Int(f"c{i}")
        sym[f"op{i}"] = op_i
        sym[f"dst{i}"] = dst_i
        sym[f"a{i}"] = a_i
        sym[f"b{i}"] = b_i
        sym[f"c{i}"] = c_i

        tmp_defined_flags.append(tmp_defined)

        srcs = [val, tmp] + const_syms
        x = _sel(srcs, a_i)
        y = _sel(srcs, b_i)
        z = _sel(srcs, c_i)

        bin_exprs = [_apply_binop(op, x, y) for op in binops]
        if op_muladd is None:
            expr = _sel(bin_exprs, op_i)
        else:
            expr = z3.If(op_i == op_muladd, (x * y) + z, _sel(bin_exprs, op_i))

        val_next = z3.If(dst_i == 0, expr, val)
        tmp_next = z3.If(dst_i == 1, expr, tmp)
        tmp_defined = z3.Or(tmp_defined, dst_i == 1)

        val, tmp = val_next, tmp_next

    return sym, a, val, tmp_defined_flags


def _domain_constraints(
    sym: dict[str, z3.ExprRef],
    *,
    n_ops: int,
    consts: list[int],
    shift_vals: set[int],
    binops: list[str],
    op_muladd: int | None,
    source_window: int | None,
) -> list[z3.BoolRef]:
    cons: list[z3.BoolRef] = []

    def in_range(v: z3.ArithRef, lo: int, hi_excl: int) -> z3.BoolRef:
        return z3.And(v >= lo, v < hi_excl)

    const_count = len(consts)

    for i in range(n_ops):
        op_i = sym[f"op{i}"]
        a_i = sym[f"a{i}"]
        b_i = sym[f"b{i}"]
        c_i = sym[f"c{i}"]

        # op code range
        cons.append(in_range(op_i, 0, len(binops) + (1 if op_muladd is not None else 0)))

        # operand ranges: [a] + [temps] + [consts]
        if source_window is None or source_window <= 0:
            temp_count = i
        else:
            temp_count = min(i, source_window)
        src_count = 1 + temp_count + const_count
        cons.append(in_range(a_i, 0, src_count))
        cons.append(in_range(b_i, 0, src_count))
        cons.append(in_range(c_i, 0, src_count))

        # If shift op, force b operand to be a constant shift amount.
        if shift_vals:
            const_offset = 1 + temp_count
            allowed = [const_offset + j for j, v in enumerate(consts) if v in shift_vals]
            if allowed:
                allowed_set = z3.Or([b_i == v for v in allowed])
                is_shift = z3.Or(op_i == binops.index("<<"), op_i == binops.index(">>"))
                cons.append(z3.Implies(is_shift, allowed_set))

    return cons


def _domain_constraints_2reg(
    sym: dict[str, z3.ExprRef],
    *,
    n_ops: int,
    consts: list[int],
    shift_vals: set[int],
    binops: list[str],
    op_muladd: int | None,
    tmp_defined_flags: list[z3.BoolRef],
    shift_src_val: bool,
    shift_dst_tmp: bool,
    muladd_dst_val: bool,
) -> list[z3.BoolRef]:
    cons: list[z3.BoolRef] = []

    def in_range(v: z3.ArithRef, lo: int, hi_excl: int) -> z3.BoolRef:
        return z3.And(v >= lo, v < hi_excl)

    const_count = len(consts)
    src_count = 2 + const_count  # val, tmp, consts

    for i in range(n_ops):
        op_i = sym[f"op{i}"]
        dst_i = sym[f"dst{i}"]
        a_i = sym[f"a{i}"]
        b_i = sym[f"b{i}"]
        c_i = sym[f"c{i}"]

        cons.append(in_range(op_i, 0, len(binops) + (1 if op_muladd is not None else 0)))
        cons.append(in_range(dst_i, 0, 2))
        cons.append(in_range(a_i, 0, src_count))
        cons.append(in_range(b_i, 0, src_count))
        cons.append(in_range(c_i, 0, src_count))

        # tmp cannot be used before it's defined.
        tmp_ok = tmp_defined_flags[i]
        cons.append(z3.Implies(a_i == 1, tmp_ok))
        cons.append(z3.Implies(b_i == 1, tmp_ok))
        cons.append(z3.Implies(c_i == 1, tmp_ok))

        if shift_vals:
            const_offset = 2
            allowed = [const_offset + j for j, v in enumerate(consts) if v in shift_vals]
            if allowed:
                allowed_set = z3.Or([b_i == v for v in allowed])
                is_shift = z3.Or(op_i == binops.index("<<"), op_i == binops.index(">>"))
                cons.append(z3.Implies(is_shift, allowed_set))
                if shift_src_val:
                    cons.append(z3.Implies(is_shift, a_i == 0))
                if shift_dst_tmp:
                    cons.append(z3.Implies(is_shift, dst_i == 1))
        if muladd_dst_val and op_muladd is not None:
            cons.append(z3.Implies(op_i == op_muladd, dst_i == 0))

    return cons


def cegis_superopt(
    *,
    n_ops: int,
    consts: list[int],
    shift_vals: set[int],
    binops: list[str],
    op_muladd: int | None,
    source_window: int | None,
    target_fn: Callable[[z3.BitVecRef], z3.BitVecRef],
    two_reg: bool,
    budget: dict[str, int] | None,
    shift_src_val: bool,
    shift_dst_tmp: bool,
    muladd_dst_val: bool,
    width: int,
    op_seq: list[str] | None,
    dst_seq: list[int] | None,
    src_seq_a: list[int] | None,
    src_seq_b: list[int] | None,
    src_seq_c: list[int] | None,
    const_assigns: dict[int, int] | None,
    const_syms_override: list[z3.BitVecRef] | None,
    init_samples: int,
    max_iters: int,
    seed: int,
    synth_timeout_ms: int,
    verify_timeout_ms: int,
) -> tuple[bool, str]:
    if two_reg:
        sym, a, out, tmp_flags = _build_template_2reg(
            n_ops=n_ops,
            consts=consts,
            binops=binops,
            op_muladd=op_muladd,
            width=width,
            const_syms_override=const_syms_override,
        )
        dom_cons = _domain_constraints_2reg(
            sym,
            n_ops=n_ops,
            consts=consts,
            shift_vals=shift_vals,
            binops=binops,
            op_muladd=op_muladd,
            tmp_defined_flags=tmp_flags,
            shift_src_val=shift_src_val,
            shift_dst_tmp=shift_dst_tmp,
            muladd_dst_val=muladd_dst_val,
        )
    else:
        sym, a, out = _build_template(
            n_ops=n_ops,
            consts=consts,
            binops=binops,
            op_muladd=op_muladd,
            width=width,
            const_syms_override=const_syms_override,
        )
        dom_cons = _domain_constraints(
            sym,
            n_ops=n_ops,
            consts=consts,
            shift_vals=shift_vals,
            binops=binops,
            op_muladd=op_muladd,
            source_window=source_window,
        )
    target = target_fn(a)

    # Optional op-count budget constraints.
    if budget:
        op_code_map = {op: i for i, op in enumerate(binops)}
        if op_muladd is not None:
            op_code_map["muladd"] = op_muladd
        for op, count in budget.items():
            code = op_code_map.get(op)
            if code is None:
                raise ValueError(f"budget op {op!r} not in opset")
            uses = []
            for i in range(n_ops):
                uses.append(z3.If(sym[f"op{i}"] == code, z3.IntVal(1), z3.IntVal(0)))
            dom_cons.append(z3.Sum(uses) == count)

    # Optional fixed op sequence / dst sequence constraints.
    if op_seq:
        if len(op_seq) != n_ops:
            raise ValueError(f"op_seq length {len(op_seq)} != n_ops {n_ops}")
        op_code_map = {op: i for i, op in enumerate(binops)}
        if op_muladd is not None:
            op_code_map["muladd"] = op_muladd
        for i, op_name in enumerate(op_seq):
            code = op_code_map.get(op_name)
            if code is None:
                raise ValueError(f"op_seq op {op_name!r} not in opset")
            dom_cons.append(sym[f"op{i}"] == code)
    if dst_seq:
        if not two_reg:
            raise ValueError("dst_seq only supported in two-reg mode")
        if len(dst_seq) != n_ops:
            raise ValueError(f"dst_seq length {len(dst_seq)} != n_ops {n_ops}")
        for i, dst in enumerate(dst_seq):
            if dst not in (0, 1):
                raise ValueError(f"dst_seq[{i}] must be 0 (val) or 1 (tmp)")
            dom_cons.append(sym[f"dst{i}"] == dst)

    if src_seq_a:
        if len(src_seq_a) != n_ops:
            raise ValueError(f"src_seq_a length {len(src_seq_a)} != n_ops {n_ops}")
        for i, idx in enumerate(src_seq_a):
            dom_cons.append(sym[f"a{i}"] == idx)
    if src_seq_b:
        if len(src_seq_b) != n_ops:
            raise ValueError(f"src_seq_b length {len(src_seq_b)} != n_ops {n_ops}")
        for i, idx in enumerate(src_seq_b):
            dom_cons.append(sym[f"b{i}"] == idx)
    if src_seq_c:
        if len(src_seq_c) != n_ops:
            raise ValueError(f"src_seq_c length {len(src_seq_c)} != n_ops {n_ops}")
        for i, idx in enumerate(src_seq_c):
            dom_cons.append(sym[f"c{i}"] == idx)

    if const_assigns:
        for k_idx, val in const_assigns.items():
            k_sym = sym.get(f"k{k_idx}")
            if k_sym is None:
                raise ValueError(f"const_assign uses k{k_idx} but no such symbol")
            dom_cons.append(k_sym == _bv(val, width))

    samples = _initial_samples(seed=seed, n=init_samples)
    seen = set(samples)

    for it in range(1, max_iters + 1):
        s = z3.Solver()
        s.set(timeout=synth_timeout_ms)
        s.add(dom_cons)
        for aval in samples:
            s.add(z3.substitute(out, (a, _bv(aval, width))) == z3.substitute(target, (a, _bv(aval, width))))
        res = s.check()
        if res == z3.unknown:
            return False, f"unknown (synthesis timed out) at iter {it} with {len(samples)} samples"
        if res == z3.unsat:
            return False, f"UNSAT: no program with {n_ops} ops under current opset/consts"

        model = s.model()
        if two_reg:
            prog2 = _decode_model_2reg(model, sym, n_ops, binops=binops, op_muladd=op_muladd)
        else:
            prog = _decode_model(model, sym, n_ops, binops=binops, op_muladd=op_muladd)

        subs = []
        for i in range(n_ops):
            if two_reg:
                op_name = prog2.ops[i]
                if op_name == "muladd":
                    if op_muladd is None:
                        raise RuntimeError("decoded muladd while muladd is disabled")
                    op_code = op_muladd
                else:
                    op_code = binops.index(op_name)
                subs.append((sym[f"op{i}"], z3.IntVal(op_code)))
                subs.append((sym[f"dst{i}"], z3.IntVal(prog2.dst_idx[i])))
                subs.append((sym[f"a{i}"], z3.IntVal(prog2.a_idx[i])))
                subs.append((sym[f"b{i}"], z3.IntVal(prog2.b_idx[i])))
                subs.append((sym[f"c{i}"], z3.IntVal(prog2.c_idx[i])))
            else:
                op_name = prog.ops[i]
                if op_name == "muladd":
                    if op_muladd is None:
                        raise RuntimeError("decoded muladd while muladd is disabled")
                    op_code = op_muladd
                else:
                    op_code = binops.index(op_name)
                subs.append((sym[f"op{i}"], z3.IntVal(op_code)))
                subs.append((sym[f"a{i}"], z3.IntVal(prog.a_idx[i])))
                subs.append((sym[f"b{i}"], z3.IntVal(prog.b_idx[i])))
                subs.append((sym[f"c{i}"], z3.IntVal(prog.c_idx[i])))

        out_m = z3.simplify(z3.substitute(out, *subs))

        v = z3.Solver()
        v.set(timeout=verify_timeout_ms)
        v.add(out_m != target)
        res = v.check()
        if res == z3.unknown:
            if two_reg:
                detail = _pretty_program_2reg(prog2, consts)
                if const_syms_override is not None:
                    kv = []
                    for i in range(len(consts)):
                        kv.append(f"k{i}=0x{int(model.eval(sym[f'k{i}'], model_completion=True).as_long()):08x}")
                    detail = detail + "\n" + "consts: " + ", ".join(kv)
                return False, f"unknown (verify timed out)\n{detail}"
            return False, f"unknown (verify timed out)\n{_pretty_program(prog, consts)}"
        if res == z3.unsat:
            if two_reg:
                detail = _pretty_program_2reg(prog2, consts)
                if const_syms_override is not None:
                    kv = []
                    for i in range(len(consts)):
                        kv.append(f"k{i}=0x{int(model.eval(sym[f'k{i}'], model_completion=True).as_long()):08x}")
                    detail = detail + "\n" + "consts: " + ", ".join(kv)
                return True, f"FOUND program with {n_ops} ops\n{detail}"
            return True, f"FOUND program with {n_ops} ops\n{_pretty_program(prog, consts)}"

        cex = v.model().eval(a, model_completion=True)
        aval = int(cex.as_long())
        if aval not in seen:
            samples.append(aval)
            seen.add(aval)

    return False, f"gave up after {max_iters} iters (still SAT on samples)"


def _rand_u32_samples(*, seed: int, n: int) -> list[int]:
    rng = random.Random(seed)
    return [rng.getrandbits(32) for _ in range(n)]


def _make_candidate_block12(
    *,
    c0: int,
    c1: int,
    c2: int,
    c3: int,
    k_xor1: int,
    k_xor2: int,
    k_add: int,
    op4: str,
) -> list[dict]:
    # 12-op skeleton:
    # 1) val = val * c0 + k_xor1
    # 2) tmp = val >> 19
    # 3) val = val ^ k_xor2
    # 4) val = val ^ tmp
    # 5) val = val * c1 + k_add
    # 6) tmp = val << 9
    # 7) val = val + k_add
    # 8) val = val op4 tmp
    # 9) val = val * c2 + k_add
    # 10) tmp = val >> 16
    # 11) val = val ^ k_xor2
    # 12) val = val ^ tmp
    return [
        {"op": "muladd", "dst": "val", "a": "val", "b": c0, "c": k_xor1, "stage": "op2"},
        {"op": ">>", "dst": "tmp", "a": "val", "b": 19, "stage": "shift"},
        {"op": "^", "dst": "val", "a": "val", "b": k_xor2, "stage": "op1"},
        {"op": "^", "dst": "val", "a": "val", "b": "tmp", "stage": "op2"},
        {"op": "muladd", "dst": "val", "a": "val", "b": c1, "c": k_add, "stage": "op2"},
        {"op": "<<", "dst": "tmp", "a": "val", "b": 9, "stage": "shift"},
        {"op": "+", "dst": "val", "a": "val", "b": k_add, "stage": "op1"},
        {"op": op4, "dst": "val", "a": "val", "b": "tmp", "stage": "op2"},
        {"op": "muladd", "dst": "val", "a": "val", "b": c2, "c": k_add, "stage": "op2"},
        {"op": ">>", "dst": "tmp", "a": "val", "b": 16, "stage": "shift"},
        {"op": "^", "dst": "val", "a": "val", "b": k_xor2, "stage": "op1"},
        {"op": "^", "dst": "val", "a": "val", "b": "tmp", "stage": "op2"},
    ]


def _make_candidate_block13(
    *,
    c0: int,
    c1: int,
    c2: int,
    k_xor1: int,
    k_xor2: int,
    k_add: int,
    k_extra: int,
    op4: str,
    extra_after: int,
) -> list[dict]:
    # 13-op skeleton: insert an extra op after step `extra_after` (0-based index).
    base = _make_candidate_block12(
        c0=c0,
        c1=c1,
        c2=c2,
        c3=c2,
        k_xor1=k_xor1,
        k_xor2=k_xor2,
        k_add=k_add,
        op4=op4,
    )
    extra = {"op": "^", "dst": "val", "a": "val", "b": k_extra, "stage": "op1"}
    return base[: extra_after + 1] + [extra] + base[extra_after + 1 :]


def _eval_prog_u32(a: int, prog: list[dict]) -> int:
    val = _u32(a)
    tmp = 0
    for inst in prog:
        op = inst["op"]
        dst = inst["dst"]
        a_src = inst.get("a")
        b_src = inst.get("b")
        c_src = inst.get("c")

        def src(v):
            if v == "val":
                return val
            if v == "tmp":
                return tmp
            if isinstance(v, int):
                return v
            raise ValueError(f"bad src {v!r}")

        aval = src(a_src)
        bval = src(b_src)
        cval = src(c_src) if c_src is not None else None
        out = _apply_u32(op, aval, bval, cval)
        if dst == "val":
            val = out
        elif dst == "tmp":
            tmp = out
        else:
            raise ValueError(f"bad dst {dst!r}")
    return val


def _build_prog_from_seqs(
    *,
    op_seq: list[str],
    dst_seq: list[int],
    src_seq_a: list[int],
    src_seq_b: list[int],
    src_seq_c: list[int] | None,
    const_values: dict[int, int],
) -> list[dict]:
    prog: list[dict] = []
    for i, op in enumerate(op_seq):
        dst = "val" if dst_seq[i] == 0 else "tmp"

        def _src(idx: int):
            if idx == 0:
                return "val"
            if idx == 1:
                return "tmp"
            k_idx = idx - 2
            if k_idx not in const_values:
                raise ValueError(f"missing const k{k_idx}")
            return const_values[k_idx]

        a = _src(src_seq_a[i])
        b = _src(src_seq_b[i])
        c = _src(src_seq_c[i]) if src_seq_c is not None else None
        inst = {"op": op, "dst": dst, "a": a, "b": b}
        if op == "muladd":
            if c is None:
                raise ValueError("muladd requires src_seq_c")
            inst["c"] = c
        prog.append(inst)
    return prog


def _search_template_random(
    *,
    attempts: int,
    seed: int,
    consts: list[int],
    op4: str,
    samples: list[int],
) -> list[dict] | None:
    rng = random.Random(seed)
    consts = [c for c in consts if isinstance(c, int)]
    if not consts:
        return None

    # Precompute target values for samples.
    target = {a: _eval_myhash_u32(a) for a in samples}

    for _ in range(attempts):
        c0 = rng.choice(consts)
        c1 = rng.choice(consts)
        c2 = rng.choice(consts)
        k_xor1 = rng.choice(consts)
        k_xor2 = rng.choice(consts)
        k_add = rng.choice(consts)
        prog = _make_candidate_block12(
            c0=c0, c1=c1, c2=c2, c3=c2, k_xor1=k_xor1, k_xor2=k_xor2, k_add=k_add, op4=op4
        )
        ok = True
        for a in samples:
            if _eval_prog_u32(a, prog) != target[a]:
                ok = False
                break
        if ok:
            return prog
    return None


def _verify_prog_z3(prog: list[dict]) -> bool:
    a = z3.BitVec("a", 32)
    val = a
    tmp = z3.BitVecVal(0, 32)

    def src(v):
        if v == "val":
            return val
        if v == "tmp":
            return tmp
        if isinstance(v, int):
            return _bv(v, 32)
        raise ValueError(f"bad src {v!r}")

    for inst in prog:
        op = inst["op"]
        dst = inst["dst"]
        aval = src(inst.get("a"))
        bval = src(inst.get("b"))
        cval = src(inst.get("c")) if inst.get("c") is not None else None
        if op == "muladd":
            assert cval is not None
            out = (aval * bval) + cval
        else:
            out = _apply_binop(op, aval, bval)
        if dst == "val":
            val = out
        elif dst == "tmp":
            tmp = out
        else:
            raise ValueError(f"bad dst {dst!r}")

    target = _target_myhash(a, width=32)
    v = z3.Solver()
    v.add(val != target)
    return v.check() == z3.unsat


def _const_hill_for_skeleton(
    *,
    op_seq: list[str],
    dst_seq: list[int],
    src_seq_a: list[int],
    src_seq_b: list[int],
    src_seq_c: list[int],
    const_assigns: dict[int, int],
    pool_random: int,
    hill_restarts: int,
    hill_steps: int,
    hill_samples: int,
    hill_seed: int,
) -> tuple[int, dict[int, int] | None]:
    def _build_const_pools_local(seed_for_pool: int):
        k_roles: dict[int, set[str]] = {}
        for i, op in enumerate(op_seq):
            for which, src_seq in (("a", src_seq_a), ("b", src_seq_b), ("c", src_seq_c)):
                idx = src_seq[i]
                if idx < 2:
                    continue
                k_idx = idx - 2
                if op == "muladd":
                    role = "mul_mult" if which == "b" else "mul_add"
                elif op in {"<<", ">>"} and which == "b":
                    role = "shift"
                elif op == "+" and which == "b":
                    role = "add"
                elif op == "^" and which == "b":
                    role = "xor"
                else:
                    role = "other"
                k_roles.setdefault(k_idx, set()).add(role)

        MULTS = {1 + (1 << 12), 1 + (1 << 5), 1 + (1 << 3)}
        HASH_CONSTS = {
            0x7ED55D16,
            0xC761C23C,
            0x165667B1,
            0xD3A2646C,
            0xFD7046C5,
            0xB55A4F09,
        }
        MULTS |= {0, 1}
        HASH_CONSTS |= {0, 1}
        MULTS |= {(-m) & MASK32 for m in list(MULTS)}
        HASH_CONSTS |= {(-c) & MASK32 for c in list(HASH_CONSTS)}
        if pool_random > 0:
            rng_pool = random.Random(seed_for_pool)
            for _ in range(pool_random):
                HASH_CONSTS.add(rng_pool.getrandbits(32))

        pools: dict[int, list[int]] = {}
        for k_idx, roles in k_roles.items():
            if "shift" in roles:
                pools[k_idx] = []
                continue
            if "mul_mult" in roles:
                pools[k_idx] = sorted(MULTS)
            elif roles & {"mul_add", "add", "xor"}:
                pools[k_idx] = sorted(HASH_CONSTS)
            else:
                pools[k_idx] = sorted(HASH_CONSTS)
        fixed = const_assigns or {}
        return pools, fixed

    pools, fixed = _build_const_pools_local(seed_for_pool=hill_seed)
    samples = _rand_u32_samples(seed=hill_seed, n=hill_samples)
    targets = [_eval_myhash_u32(a) for a in samples]
    rng = random.Random(hill_seed)
    mutable_keys = [k for k in pools.keys() if k not in fixed and pools[k]]
    if not mutable_keys:
        return 10**9, None

    def score_for(const_values: dict[int, int]) -> int:
        prog = _build_prog_from_seqs(
            op_seq=op_seq,
            dst_seq=dst_seq,
            src_seq_a=src_seq_a,
            src_seq_b=src_seq_b,
            src_seq_c=src_seq_c,
            const_values=const_values,
        )
        mismatches = 0
        for a, want in zip(samples, targets):
            if _eval_prog_u32(a, prog) != want:
                mismatches += 1
                break
        return mismatches

    best_overall = None
    best_score = 10**9
    for _ in range(hill_restarts):
        const_values = dict(fixed)
        for k in mutable_keys:
            const_values[k] = rng.choice(pools[k])
        score = score_for(const_values)
        if score < best_score:
            best_score = score
            best_overall = dict(const_values)
        for _ in range(hill_steps):
            k = rng.choice(mutable_keys)
            old = const_values[k]
            cand = rng.choice(pools[k])
            if cand == old:
                continue
            const_values[k] = cand
            new_score = score_for(const_values)
            if new_score <= score:
                score = new_score
                if score < best_score:
                    best_score = score
                    best_overall = dict(const_values)
            else:
                const_values[k] = old
            if score == 0:
                return 0, dict(const_values)
    return best_score, best_overall


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--n-ops", type=int, default=11)
    ap.add_argument("--init-samples", type=int, default=32)
    ap.add_argument("--max-iters", type=int, default=20)
    ap.add_argument("--seed", type=int, default=0)
    ap.add_argument("--synth-timeout-ms", type=int, default=20000)
    ap.add_argument("--verify-timeout-ms", type=int, default=20000)
    ap.add_argument("--no-shift-constraint", action="store_true",
                    help="Allow shift amounts from any source, not just constants")
    ap.add_argument("--const-pool", choices=["default", "minimal"], default="default",
                    help="Constant pool to expose to the superoptimizer.")
    ap.add_argument("--const-pool-target", action="store_true",
                    help="Use only constants needed for the target stage/block (plus 0/1).")
    ap.add_argument("--no-mul", action="store_true",
                    help="Disallow '*' (keeps muladd enabled). Can speed UNSAT.")
    ap.add_argument("--no-muladd", action="store_true",
                    help="Disallow muladd op (use only primitive binops).")
    ap.add_argument("--two-reg", action="store_true",
                    help="Restrict program to two registers (val/tmp) with explicit dst.")
    ap.add_argument("--budget", type=str, default="",
                    help="Exact op-count budget, e.g. 'muladd:3,shl:1,shr:2,xor:3,add:2'")
    ap.add_argument("--shift-src-val", action="store_true",
                    help="In two-reg mode, force shifts to use val as the left operand.")
    ap.add_argument("--shift-dst-tmp", action="store_true",
                    help="In two-reg mode, force shifts to write into tmp.")
    ap.add_argument("--muladd-dst-val", action="store_true",
                    help="In two-reg mode, force muladd ops to write into val.")
    ap.add_argument("--op-seq", type=str, default="",
                    help="Fixed op sequence (comma-separated), e.g. 'muladd,>>,^,^,...'")
    ap.add_argument("--dst-seq", type=str, default="",
                    help="Fixed dst sequence (comma-separated), use 'val' or 'tmp'.")
    ap.add_argument("--src-seq-a", type=str, default="",
                    help="Fixed src sequence for a (comma-separated: val,tmp,k0,k1,...)")
    ap.add_argument("--src-seq-b", type=str, default="",
                    help="Fixed src sequence for b (comma-separated: val,tmp,k0,k1,...)")
    ap.add_argument("--src-seq-c", type=str, default="",
                    help="Fixed src sequence for c (comma-separated: val,tmp,k0,k1,...)")
    ap.add_argument("--const-assign", type=str, default="",
                    help="Assign symbolic consts, e.g. 'k0=12,k1=19'")
    ap.add_argument("--shape", choices=["full", "stage", "block"], default="full",
                    help="Target: full myhash, one stage, or a block of stages.")
    ap.add_argument("--stage-idx", type=int, default=0,
                    help="Stage index for --shape stage.")
    ap.add_argument("--stage-start", type=int, default=0,
                    help="Starting stage for --shape block.")
    ap.add_argument("--stage-count", type=int, default=2,
                    help="Number of stages for --shape block.")
    ap.add_argument("--source-window", type=int, default=0,
                    help="Restrict operands to last K temps (0 = no restriction).")
    ap.add_argument("--width", type=int, default=32,
                    help="Bitwidth for synthesis (e.g., 8 or 12 for staged search).")
    ap.add_argument("--template-search", action="store_true",
                    help="Use fast randomized template search instead of SMT synthesis.")
    ap.add_argument("--template-attempts", type=int, default=20000)
    ap.add_argument("--template-seed", type=int, default=0)
    ap.add_argument("--template-op4", type=str, default="^",
                    help="op for stage4 combine in template: '^' or '+'.")
    ap.add_argument("--const-search", action="store_true",
                    help="Randomly search constant assignments for a fixed skeleton.")
    ap.add_argument("--const-attempts", type=int, default=200000)
    ap.add_argument("--const-seed", type=int, default=0)
    ap.add_argument("--pool-random", type=int, default=0,
                    help="Add N random constants to hash-const pool.")
    ap.add_argument("--const-hill", action="store_true",
                    help="Local-search constants for a fixed skeleton.")
    ap.add_argument("--hill-steps", type=int, default=2000)
    ap.add_argument("--hill-restarts", type=int, default=50)
    ap.add_argument("--hill-samples", type=int, default=256)
    ap.add_argument("--hill-seed", type=int, default=0)
    ap.add_argument("--mitm", action="store_true",
                    help="Meet-in-the-middle search over two-reg programs (small width).")
    ap.add_argument("--mitm-width", type=int, default=8)
    ap.add_argument("--mitm-l1", type=int, default=5)
    ap.add_argument("--mitm-l2", type=int, default=6)
    ap.add_argument("--mitm-max-unique", type=int, default=20000,
                    help="Cap unique semantics per depth (keeps enumeration bounded).")
    ap.add_argument("--mitm-allow-tmp-before-shift", action="store_true",
                    help="Allow tmp to be read before any shift writes it.")
    ap.add_argument("--mitm-allow-val-b", action="store_true",
                    help="Allow val as RHS operand for add/xor/mul in MITM.")
    ap.add_argument("--mitm-allow-tmp-a", action="store_true",
                    help="Allow tmp as LHS operand for add/xor/mul/muladd in MITM.")
    ap.add_argument("--mitm-shift-to-val", action="store_true",
                    help="Allow shifts to write into val instead of tmp.")
    ap.add_argument("--skeleton-11", action="store_true",
                    help="Run 11-op skeleton enumeration by deleting one op.")
    ap.add_argument("--skeleton-13", action="store_true",
                    help="Run 13-op skeleton enumeration with constant hill search.")
    args = ap.parse_args()

    if args.no_mul and "*" in DEFAULT_BINOPS:
        binops = [op for op in DEFAULT_BINOPS if op != "*"]
    else:
        binops = list(DEFAULT_BINOPS)

    if args.const_pool == "minimal":
        consts = list(MINIMAL_CONSTS)
        shift_vals = {3, 5, 9, 12, 16, 19}
    else:
        consts = list(DEFAULT_CONSTS)
        shift_vals = {v for v in consts if 0 <= v <= 31}
    if args.const_pool_target:
        if args.shape == "stage":
            consts = _consts_for_stages([args.stage_idx])
        elif args.shape == "block":
            stages = range(args.stage_start, args.stage_start + args.stage_count)
            consts = _consts_for_stages(stages)
        else:
            consts = _consts_for_stages(range(len(HASH_STAGES)))
        shift_vals = {v for v in consts if 0 <= v <= 31}
    if args.no_shift_constraint:
        shift_vals = set()

    op_muladd = None if args.no_muladd else len(binops)

    budget: dict[str, int] | None = None
    if args.budget:
        budget = {}
        for token in _parse_list(args.budget):
            if ":" not in token:
                continue
            raw_op, raw_val = token.split(":", 1)
            try:
                count = int(raw_val)
            except ValueError:
                continue
            op = _normalize_op(raw_op)
            budget[op] = count

    budget_op_counts = budget

    op_seq: list[str] | None = None
    if args.op_seq:
        op_seq = [_normalize_op(tok) for tok in _parse_list(args.op_seq)]

    dst_seq: list[int] | None = None
    if args.dst_seq:
        dst_seq = []
        for tok in _parse_list(args.dst_seq):
            if tok.lower() in {"val", "0"}:
                dst_seq.append(0)
            elif tok.lower() in {"tmp", "1"}:
                dst_seq.append(1)
            else:
                raise SystemExit(f"unknown dst token {tok!r} (use val/tmp)")

    def _parse_src_seq(raw: str) -> list[int] | None:
        if not raw:
            return None
        out: list[int] = []
        for tok in _parse_list(raw):
            t = tok.lower()
            if t == "val":
                out.append(0)
            elif t == "tmp":
                out.append(1)
            elif t.startswith("k") and t[1:].isdigit():
                out.append(2 + int(t[1:]))
            else:
                raise SystemExit(f"unknown src token {tok!r} (use val/tmp/kN)")
        return out

    src_seq_a = _parse_src_seq(args.src_seq_a)
    src_seq_b = _parse_src_seq(args.src_seq_b)
    src_seq_c = _parse_src_seq(args.src_seq_c)

    const_assigns: dict[int, int] | None = None
    if args.const_assign:
        const_assigns = {}
        for token in _parse_list(args.const_assign):
            if "=" not in token:
                continue
            key, raw = token.split("=", 1)
            if not key.startswith("k") or not key[1:].isdigit():
                raise SystemExit(f"const-assign key must be kN, got {key!r}")
            try:
                val = int(raw, 0)
            except ValueError:
                raise SystemExit(f"const-assign value invalid: {raw!r}")
            const_assigns[int(key[1:])] = val

    sym_const_count = 0
    for seq in (src_seq_a, src_seq_b, src_seq_c):
        if not seq:
            continue
        for idx in seq:
            if idx >= 2:
                sym_const_count = max(sym_const_count, (idx - 2) + 1)
    const_syms_override = None
    if sym_const_count > 0:
        const_syms_override = [z3.BitVec(f"k{i}", args.width) for i in range(sym_const_count)]
        consts = [0 for _ in range(sym_const_count)]
        shift_vals = set()

    def _build_const_pools(*, seed_for_pool: int):
        if not (op_seq and dst_seq and src_seq_a and src_seq_b and src_seq_c):
            raise SystemExit("const-search/const-hill requires op-seq, dst-seq, src-seq-a/b/c")

        k_roles: dict[int, set[str]] = {}
        for i, op in enumerate(op_seq):
            for which, src_seq in (("a", src_seq_a), ("b", src_seq_b), ("c", src_seq_c)):
                idx = src_seq[i]
                if idx < 2:
                    continue
                k_idx = idx - 2
                if op == "muladd":
                    role = "mul_mult" if which == "b" else "mul_add"
                elif op in {"<<", ">>"} and which == "b":
                    role = "shift"
                elif op == "+" and which == "b":
                    role = "add"
                elif op == "^" and which == "b":
                    role = "xor"
                else:
                    role = "other"
                k_roles.setdefault(k_idx, set()).add(role)

        MULTS = {1 + (1 << 12), 1 + (1 << 5), 1 + (1 << 3)}
        HASH_CONSTS = {
            0x7ED55D16,
            0xC761C23C,
            0x165667B1,
            0xD3A2646C,
            0xFD7046C5,
            0xB55A4F09,
        }
        MULTS |= {0, 1}
        HASH_CONSTS |= {0, 1}
        MULTS |= {(-m) & MASK32 for m in list(MULTS)}
        HASH_CONSTS |= {(-c) & MASK32 for c in list(HASH_CONSTS)}
        if args.pool_random > 0:
            rng_pool = random.Random(seed_for_pool)
            for _ in range(args.pool_random):
                HASH_CONSTS.add(rng_pool.getrandbits(32))

        pools: dict[int, list[int]] = {}
        for k_idx, roles in k_roles.items():
            if "shift" in roles:
                pools[k_idx] = []
                continue
            if "mul_mult" in roles:
                pools[k_idx] = sorted(MULTS)
            elif roles & {"mul_add", "add", "xor"}:
                pools[k_idx] = sorted(HASH_CONSTS)
            else:
                pools[k_idx] = sorted(HASH_CONSTS)

        fixed = const_assigns or {}
        for k_idx, pool in pools.items():
            if not pool and k_idx not in fixed:
                raise SystemExit(f"k{k_idx} is used as shift amount but not fixed via --const-assign")

        return pools, fixed

    if args.mitm:
        if args.mitm_width < 2 or args.mitm_width > 12:
            raise SystemExit("mitm-width must be in [2, 12]")
        budget_mitm = budget_op_counts if budget_op_counts else None
        allow_muladd = not args.no_muladd
        allow_mul = not args.no_mul
        prog = mitm_search(
            width=args.mitm_width,
            l1=args.mitm_l1,
            l2=args.mitm_l2,
            consts=consts,
            shift_vals=shift_vals,
            allow_tmp_before_shift=args.mitm_allow_tmp_before_shift,
            allow_val_b=args.mitm_allow_val_b,
            allow_tmp_a=args.mitm_allow_tmp_a,
            shift_dst_tmp=not args.mitm_shift_to_val,
            shift_src_val=True,
            allow_muladd=allow_muladd,
            allow_mul=allow_mul,
            budget=budget_mitm,
            max_unique=args.mitm_max_unique,
        )
        if prog is None:
            print("mitm: no candidate found")
            return
        print("mitm: candidate found on reduced width, verifying...")
        if _verify_prog_z3(prog):
            print("mitm: verified exact equivalence")
            print("hash_prog:")
            for inst in prog:
                print(inst)
        else:
            print("mitm: failed exact verification")
        return

    if args.skeleton_11:
        # Enumerate 11-op variants by removing one non-muladd op.
        base_op_seq = ["muladd", ">>", "^", "^", "muladd", "<<", "+", "^", "muladd", ">>", "^", "^"]
        base_dst_seq = [0, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0]
        base_src_a = [0] * 12
        base_src_b = [2, 4, 5, 1, 6, 8, 9, 1, 10, 12, 13, 1]
        base_src_c = [3, 0, 0, 0, 7, 0, 0, 0, 11, 0, 0, 0]
        fixed = const_assigns or {}
        fixed.update({2: 19, 6: 9, 10: 16})  # shift amounts k2/k6/k10

        best = None
        best_score = 10**9

        for remove_at in range(len(base_op_seq)):
            if base_op_seq[remove_at] == "muladd":
                continue
            op_seq = base_op_seq[:]
            dst_seq = base_dst_seq[:]
            src_a = base_src_a[:]
            src_b = base_src_b[:]
            src_c = base_src_c[:]
            op_seq.pop(remove_at)
            dst_seq.pop(remove_at)
            src_a.pop(remove_at)
            src_b.pop(remove_at)
            src_c.pop(remove_at)

            score, consts = _const_hill_for_skeleton(
                op_seq=op_seq,
                dst_seq=dst_seq,
                src_seq_a=src_a,
                src_seq_b=src_b,
                src_seq_c=src_c,
                const_assigns=fixed,
                pool_random=args.pool_random,
                hill_restarts=args.hill_restarts,
                hill_steps=args.hill_steps,
                hill_samples=args.hill_samples,
                hill_seed=args.hill_seed + remove_at,
            )
            if score < best_score:
                best_score = score
                best = (op_seq, dst_seq, src_a, src_b, src_c, consts)

        if best is None or best_score > 0 or best[5] is None:
            print(f"skeleton_11: no candidate found (best mismatches={best_score})")
            return

        op_seq, dst_seq, src_a, src_b, src_c, consts = best
        prog = _build_prog_from_seqs(
            op_seq=op_seq,
            dst_seq=dst_seq,
            src_seq_a=src_a,
            src_seq_b=src_b,
            src_seq_c=src_c,
            const_values=consts,
        )
        print("skeleton_11: candidate passed samples, verifying...")
        if _verify_prog_z3(prog):
            print("skeleton_11: verified exact equivalence")
            print("hash_prog:")
            for inst in prog:
                print(inst)
        else:
            print("skeleton_11: failed exact verification")
        return

    if args.skeleton_13:
        # Enumerate 13-op variants: insert extra XOR const after various steps.
        # Skeleton layout uses symbolic consts k0..k12, with shifts fixed.
        base_op_seq = ["muladd", ">>", "^", "^", "muladd", "<<", "+", "^", "muladd", ">>", "^", "^"]
        base_dst_seq = [0, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0]
        base_src_a = [0] * 12
        base_src_b = [2, 4, 5, 1, 6, 8, 9, 1, 10, 12, 13, 1]
        base_src_c = [3, 0, 0, 0, 7, 0, 0, 0, 11, 0, 0, 0]
        fixed = const_assigns or {}
        fixed.update({2: 19, 6: 9, 10: 16})  # shift amounts k2/k6/k10

        best = None
        best_score = 10**9
        best_prog = None

        for insert_at in range(len(base_op_seq) + 1):
            # Insert extra XOR const (k14) on val.
            op_seq = base_op_seq[:]
            dst_seq = base_dst_seq[:]
            src_a = base_src_a[:]
            src_b = base_src_b[:]
            src_c = base_src_c[:]
            op_seq.insert(insert_at, "^")
            dst_seq.insert(insert_at, 0)
            src_a.insert(insert_at, 0)
            src_b.insert(insert_at, 14)
            src_c.insert(insert_at, 0)

            score, consts = _const_hill_for_skeleton(
                op_seq=op_seq,
                dst_seq=dst_seq,
                src_seq_a=src_a,
                src_seq_b=src_b,
                src_seq_c=src_c,
                const_assigns=fixed,
                pool_random=args.pool_random,
                hill_restarts=args.hill_restarts,
                hill_steps=args.hill_steps,
                hill_samples=args.hill_samples,
                hill_seed=args.hill_seed + insert_at,
            )
            if score < best_score:
                best_score = score
                best = (op_seq, dst_seq, src_a, src_b, src_c, consts)

        if best is None or best_score > 0 or best[5] is None:
            print(f"skeleton_13: no candidate found (best mismatches={best_score})")
            return

        op_seq, dst_seq, src_a, src_b, src_c, consts = best
        prog = _build_prog_from_seqs(
            op_seq=op_seq,
            dst_seq=dst_seq,
            src_seq_a=src_a,
            src_seq_b=src_b,
            src_seq_c=src_c,
            const_values=consts,
        )
        print("skeleton_13: candidate passed samples, verifying...")
        if _verify_prog_z3(prog):
            print("skeleton_13: verified exact equivalence")
            print("hash_prog:")
            for inst in prog:
                print(inst)
        else:
            print("skeleton_13: failed exact verification")
        return

    if args.const_hill:
        pools, fixed = _build_const_pools(seed_for_pool=args.hill_seed)
        samples = _rand_u32_samples(seed=args.hill_seed, n=args.hill_samples)
        targets = [_eval_myhash_u32(a) for a in samples]

        rng = random.Random(args.hill_seed)
        mutable_keys = [k for k in pools.keys() if k not in fixed]
        if not mutable_keys:
            raise SystemExit("const-hill has no mutable constants (all fixed)")

        def score_for(const_values: dict[int, int]) -> int:
            prog = _build_prog_from_seqs(
                op_seq=op_seq,
                dst_seq=dst_seq,
                src_seq_a=src_seq_a,
                src_seq_b=src_seq_b,
                src_seq_c=src_seq_c,
                const_values=const_values,
            )
            mismatches = 0
            for a, want in zip(samples, targets):
                if _eval_prog_u32(a, prog) != want:
                    mismatches += 1
                    if mismatches > 0:
                        break
            return mismatches

        best_overall = None
        best_score = 10**9

        for r in range(args.hill_restarts):
            const_values = dict(fixed)
            for k in mutable_keys:
                const_values[k] = rng.choice(pools[k])
            score = score_for(const_values)
            if score < best_score:
                best_score = score
                best_overall = dict(const_values)

            for _ in range(args.hill_steps):
                k = rng.choice(mutable_keys)
                old = const_values[k]
                cand = rng.choice(pools[k])
                if cand == old:
                    continue
                const_values[k] = cand
                new_score = score_for(const_values)
                if new_score <= score:
                    score = new_score
                    if score < best_score:
                        best_score = score
                        best_overall = dict(const_values)
                else:
                    const_values[k] = old
                if score == 0:
                    prog = _build_prog_from_seqs(
                        op_seq=op_seq,
                        dst_seq=dst_seq,
                        src_seq_a=src_seq_a,
                        src_seq_b=src_seq_b,
                        src_seq_c=src_seq_c,
                        const_values=const_values,
                    )
                    print("const_hill: candidate passed sample set")
                    if _verify_prog_z3(prog):
                        print("const_hill: verified exact equivalence")
                        print("hash_prog:")
                        for inst in prog:
                            print(inst)
                        return
                    print("const_hill: failed exact verification")
                    return

        # Try a single-parameter repair sweep if we're close.
        if best_overall is not None and best_score <= 3:
            for k in mutable_keys:
                orig = best_overall[k]
                for cand in pools[k]:
                    best_overall[k] = cand
                    if score_for(best_overall) == 0:
                        prog = _build_prog_from_seqs(
                            op_seq=op_seq,
                            dst_seq=dst_seq,
                            src_seq_a=src_seq_a,
                            src_seq_b=src_seq_b,
                            src_seq_c=src_seq_c,
                            const_values=best_overall,
                        )
                        print("const_hill: repair candidate passed sample set")
                        if _verify_prog_z3(prog):
                            print("const_hill: verified exact equivalence")
                            print("hash_prog:")
                            for inst in prog:
                                print(inst)
                            return
                        print("const_hill: repair candidate failed exact verification")
                        break
                best_overall[k] = orig
        print(f"const_hill: no candidate found (best mismatches={best_score})")
        if best_overall is not None:
            pairs = ", ".join([f"k{k}=0x{v:08x}" for k, v in sorted(best_overall.items())])
            print("const_hill: best consts: " + pairs)
        return

    if args.const_search:
        if not (op_seq and dst_seq and src_seq_a and src_seq_b and src_seq_c):
            raise SystemExit("const-search requires op-seq, dst-seq, src-seq-a/b/c")

        # Determine which k indices appear and assign pools by role.
        pools, fixed = _build_const_pools(seed_for_pool=args.const_seed)

        # Progressive sample gates.
        gate_sizes = [16, 64, 256]
        samples = _rand_u32_samples(seed=args.const_seed, n=max(gate_sizes))
        targets = [_eval_myhash_u32(a) for a in samples]

        rng = random.Random(args.const_seed)
        for attempt in range(1, args.const_attempts + 1):
            const_values = dict(fixed)
            for k_idx, pool in pools.items():
                if k_idx in const_values:
                    continue
                const_values[k_idx] = rng.choice(pool)

            prog = _build_prog_from_seqs(
                op_seq=op_seq,
                dst_seq=dst_seq,
                src_seq_a=src_seq_a,
                src_seq_b=src_seq_b,
                src_seq_c=src_seq_c,
                const_values=const_values,
            )

            ok = True
            for gate in gate_sizes:
                for j in range(gate):
                    if _eval_prog_u32(samples[j], prog) != targets[j]:
                        ok = False
                        break
                if not ok:
                    break
            if not ok:
                continue

            print(f"const_search: candidate passed gates at attempt {attempt}")
            if _verify_prog_z3(prog):
                print("const_search: verified exact equivalence")
                print("hash_prog:")
                for inst in prog:
                    print(inst)
                return
            print("const_search: failed exact verification")
            return

        print("const_search: no candidate found")
        return

    if args.template_search:
        op4 = _normalize_op(args.template_op4)
        if op4 not in {"+", "^"}:
            raise SystemExit("template-op4 must be '+' or '^'")
        # Use only real hash constants and shift/muladd constants for the template.
        consts = _consts_for_stages(range(len(HASH_STAGES)))
        samples = _rand_u32_samples(seed=args.template_seed, n=128)
        prog = _search_template_random(
            attempts=args.template_attempts,
            seed=args.template_seed,
            consts=consts,
            op4=op4,
            samples=samples,
        )
        if prog is None:
            print("template_search: no candidate found in random search")
            return
        print("template_search: candidate found on samples")
        ok = _verify_prog_z3(prog)
        if ok:
            print("template_search: verified exact equivalence")
        else:
            print("template_search: failed exact verification")
        print("hash_prog:")
        for inst in prog:
            print(inst)
        return

    if args.shape == "stage":
        if not (0 <= args.stage_idx < len(HASH_STAGES)):
            raise SystemExit(f"stage-idx must be in [0, {len(HASH_STAGES)-1}]")
        target_fn = lambda a: _target_hash_block(a, start=args.stage_idx, count=1, width=args.width)
    elif args.shape == "block":
        if args.stage_start < 0 or args.stage_count <= 0:
            raise SystemExit("stage-start must be >= 0 and stage-count > 0")
        if args.stage_start + args.stage_count > len(HASH_STAGES):
            raise SystemExit("stage-start + stage-count exceeds HASH_STAGES")
        target_fn = lambda a: _target_hash_block(a, start=args.stage_start, count=args.stage_count, width=args.width)
    else:
        target_fn = lambda a: _target_myhash(a, width=args.width)

    ok, detail = cegis_superopt(
        n_ops=args.n_ops,
        consts=consts,
        shift_vals=shift_vals,
        binops=binops,
        op_muladd=op_muladd,
        source_window=(args.source_window if args.source_window > 0 else None),
        target_fn=target_fn,
        two_reg=args.two_reg,
        budget=budget_op_counts,
        shift_src_val=args.shift_src_val,
        shift_dst_tmp=args.shift_dst_tmp,
        muladd_dst_val=args.muladd_dst_val,
        width=args.width,
        op_seq=op_seq,
        dst_seq=dst_seq,
        src_seq_a=src_seq_a,
        src_seq_b=src_seq_b,
        src_seq_c=src_seq_c,
        const_assigns=const_assigns,
        const_syms_override=const_syms_override,
        init_samples=args.init_samples,
        max_iters=args.max_iters,
        seed=args.seed,
        synth_timeout_ms=args.synth_timeout_ms,
        verify_timeout_ms=args.verify_timeout_ms,
    )
    verdict = "FOUND" if ok else "UNKNOWN_OR_UNSAT"
    print(f"myhash {args.n_ops}-op: {verdict} ({detail})")


if __name__ == "__main__":
    main()
