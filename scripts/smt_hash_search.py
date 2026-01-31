#!/usr/bin/env python3
"""
SMT-based synthesis for hash compression on small bit-widths.

Searches for a program of length <=L that matches the hash for all inputs
(of the chosen bit width). Intended as evidence about feasibility, not proof
for 32-bit.
"""
from __future__ import annotations

import argparse
from dataclasses import dataclass
from typing import List

import z3

HASH_STAGES = [
    ("+", 0x7ED55D16, "+", "<<", 12),
    ("^", 0xC761C23C, "^", ">>", 19),
    ("+", 0x165667B1, "+", "<<", 5),
    ("+", 0xD3A2646C, "^", "<<", 9),
    ("+", 0xFD7046C5, "+", "<<", 3),
    ("^", 0xB55A4F09, "^", ">>", 16),
]

BIN_OPS = ["+", "-", "^", "&", "|", "*"]
UNARY_OPS = ["shl", "shr", "addc", "xorc", "madd"]


@dataclass(frozen=True)
class SearchConfig:
    bits: int
    length: int
    allow_extra_ops: bool


def _hash(x: int, bits: int) -> int:
    mask = (1 << bits) - 1
    for op1, val1, op2, op3, val3 in HASH_STAGES:
        val1 &= mask
        tmp = ((x << val3) if op3 == "<<" else (x >> val3)) & mask
        if op1 == "+":
            x = (x + val1) & mask
        else:
            x = (x ^ val1) & mask
        if op2 == "+":
            x = (x + tmp) & mask
        else:
            x = (x ^ tmp) & mask
    return x & mask


def build_consts(bits: int):
    mask = (1 << bits) - 1
    consts = {0, 1}
    shifts = {3, 5, 9, 12, 16, 19}
    muladds = []
    for op1, val1, op2, _, val3 in HASH_STAGES:
        consts.add(val1 & mask)
        if op1 == "+" and op2 == "+":
            mult = (1 + (1 << val3)) & mask
            add = val1 & mask
            muladds.append((mult, add))
    return sorted(consts), sorted(shifts), muladds


def _known_program_fullhash(ops, consts, shifts, muladds, bits: int):
    mask = (1 << bits) - 1
    const_idx = {c: i for i, c in enumerate(consts)}
    shift_idx = {s: i for i, s in enumerate(shifts)}
    madd_idx = {pair: i for i, pair in enumerate(muladds)}

    program = []
    val_idx = 0  # input x
    for op1, val1, op2, op3, val3 in HASH_STAGES:
        if op1 == "+" and op2 == "+":
            mult = (1 + (1 << val3)) & mask
            add = val1 & mask
            d = madd_idx[(mult, add)]
            program.append(("madd", val_idx, 0, 0, d))
            val_idx = len(program)  # index of last value (input count=1)
        else:
            if op3 == "<<":
                program.append(("shl", val_idx, 0, shift_idx[val3], 0))
            else:
                program.append(("shr", val_idx, 0, shift_idx[val3], 0))
            tmp_idx = len(program)
            if op1 == "^":
                program.append(("xorc", val_idx, 0, const_idx[val1 & mask], 0))
            else:
                program.append(("addc", val_idx, 0, const_idx[val1 & mask], 0))
            val_idx = len(program)
            if op2 == "^":
                program.append(("^", val_idx, tmp_idx, 0, 0))
            else:
                program.append(("+", val_idx, tmp_idx, 0, 0))
            val_idx = len(program)
    return program


def synth_fullhash(cfg: SearchConfig, timeout_ms: int = 10000, fixed_program=None):
    bits = cfg.bits
    mask = (1 << bits) - 1
    consts, shifts, muladds = build_consts(bits)

    ops = list(BIN_OPS)
    if not cfg.allow_extra_ops:
        ops = ["+", "^", "*"]

    op_codes = {name: i for i, name in enumerate(ops + UNARY_OPS)}

    solver = z3.Solver()
    solver.set("timeout", timeout_ms)

    # Program structure
    op = [z3.Int(f"op_{i}") for i in range(cfg.length)]
    a = [z3.Int(f"a_{i}") for i in range(cfg.length)]
    b = [z3.Int(f"b_{i}") for i in range(cfg.length)]
    c = [z3.Int(f"c_{i}") for i in range(cfg.length)]  # const index for unary
    d = [z3.Int(f"d_{i}") for i in range(cfg.length)]  # second const index for madd

    total_inputs = 1  # just x
    const_count = len(consts)
    shift_count = len(shifts)
    madd_count = len(muladds)

    for i in range(cfg.length):
        solver.add(op[i] >= 0, op[i] < len(ops) + len(UNARY_OPS))
        solver.add(a[i] >= 0, a[i] < total_inputs + i)
        solver.add(b[i] >= 0, b[i] < total_inputs + i)
        solver.add(c[i] >= 0, c[i] < max(const_count, shift_count, 1))
        solver.add(d[i] >= 0, d[i] < max(madd_count, 1))

    if fixed_program is not None:
        for i, instr in enumerate(fixed_program):
            name, ai, bi, ci, di = instr
            solver.add(op[i] == op_codes[name])
            solver.add(a[i] == ai)
            solver.add(b[i] == bi)
            solver.add(c[i] == ci)
            solver.add(d[i] == di)

    # For all x in domain (small bits): enforce equality.
    for x_val in range(1 << bits):
        x = z3.BitVecVal(x_val, bits)
        vals: List[z3.BitVecRef] = [x]
        def select_val(idx, pool):
            expr = pool[0]
            for j in range(1, len(pool)):
                expr = z3.If(idx == j, pool[j], expr)
            return expr

        for i in range(cfg.length):
            ai = select_val(a[i], vals)
            bi = select_val(b[i], vals)

            def select_const(idx, items):
                expr = z3.BitVecVal(items[0], bits)
                for j in range(1, len(items)):
                    expr = z3.If(idx == j, z3.BitVecVal(items[j], bits), expr)
                return expr

            def bv_const(idx):
                return select_const(idx, consts)

            def bv_shift(idx):
                return select_const(idx, shifts)

            def bv_madd(idx):
                # select mult/add pair
                mults = [m for m, _ in muladds]
                adds = [a for _, a in muladds]
                return select_const(idx, mults), select_const(idx, adds)

            # Build op expression with ite over opcode
            expr = z3.BitVecVal(0, bits)
            for name, code in op_codes.items():
                if name in BIN_OPS:
                    if name == "+":
                        e = ai + bi
                    elif name == "-":
                        e = ai - bi
                    elif name == "^":
                        e = ai ^ bi
                    elif name == "&":
                        e = ai & bi
                    elif name == "|":
                        e = ai | bi
                    else:
                        e = ai * bi
                else:
                    if name == "shl":
                        e = z3.LShR(ai, 0)  # placeholder
                        e = ai << bv_shift(c[i])
                    elif name == "shr":
                        e = z3.LShR(ai, bv_shift(c[i]))
                    elif name == "addc":
                        e = ai + bv_const(c[i])
                    elif name == "xorc":
                        e = ai ^ bv_const(c[i])
                    else:
                        mult, add = bv_madd(d[i])
                        e = ai * mult + add
                expr = z3.If(op[i] == code, e, expr)

            vals.append(expr & z3.BitVecVal(mask, bits))

        solver.add(vals[-1] == z3.BitVecVal(_hash(x_val, bits), bits))

    res = solver.check()
    return res


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--bits", type=int, default=8)
    parser.add_argument("--length", type=int, default=11)
    parser.add_argument("--allow-extra-ops", action="store_true")
    parser.add_argument("--timeout-ms", type=int, default=10000)
    parser.add_argument("--fix-known", action="store_true", help="Constrain to known 12-op hash program.")
    args = parser.parse_args()

    cfg = SearchConfig(bits=args.bits, length=args.length, allow_extra_ops=args.allow_extra_ops)
    fixed = None
    if args.fix_known:
        consts, shifts, muladds = build_consts(cfg.bits)
        ops = list(BIN_OPS)
        if not cfg.allow_extra_ops:
            ops = ["+", "^", "*"]
        fixed = _known_program_fullhash(ops, consts, shifts, muladds, cfg.bits)
    res = synth_fullhash(cfg, timeout_ms=args.timeout_ms, fixed_program=fixed)
    print(f"smt fullhash bits={cfg.bits} length={cfg.length} extra_ops={cfg.allow_extra_ops} res={res}")


if __name__ == "__main__":
    main()
