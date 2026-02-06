#!/usr/bin/env python3
"""
Heuristic superoptimizer for hash fusion / stage reduction.

Not exhaustive; uses small-bit semantics and bounded enumeration with pruning.
"""
from __future__ import annotations

import argparse
import random
import time
from collections import defaultdict
from dataclasses import dataclass
import z3

HASH_STAGES = [
    ("+", 0x7ED55D16, "+", "<<", 12),
    ("^", 0xC761C23C, "^", ">>", 19),
    ("+", 0x165667B1, "+", "<<", 5),
    ("+", 0xD3A2646C, "^", "<<", 9),
    ("+", 0xFD7046C5, "+", "<<", 3),
    ("^", 0xB55A4F09, "^", ">>", 16),
]

ENGINE_KEYS = ("alu", "valu", "flow", "load", "store")

# Cost table: each grammar op maps to ISA engine costs.
# Defaults assume hash ops lower to single VALU ops.
OP_COSTS = {
    "+": {"valu": 1},
    "^": {"valu": 1},
    "shl": {"valu": 1},
    "shr": {"valu": 1},
    "madd": {"valu": 1},
    "-": {"valu": 1},
    "&": {"valu": 1},
    "|": {"valu": 1},
    "*": {"valu": 1},
}


@dataclass(frozen=True)
class Expr:
    size: int
    vals: tuple[int, ...]


@dataclass(frozen=True)
class ExprAst:
    size: int
    vals: tuple[int, ...]
    ast: tuple
    cost: tuple[int, ...] = (0, 0, 0, 0, 0)


def _stage_cost(stage) -> int:
    op1, _, op2, _, _ = stage
    return 1 if (op1 == "+" and op2 == "+") else 3


def _linear_muladd(stage, mask: int) -> tuple[int, int]:
    _, val1, _, _, val3 = stage
    mult = (1 + (1 << val3)) & mask
    add = val1 & mask
    return mult, add


def _apply_stage(stage, x: int, mask: int) -> int:
    op1, val1, op2, op3, val3 = stage
    val1 = val1 & mask
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


def _hash(x: int, mask: int) -> int:
    for stage in HASH_STAGES:
        x = _apply_stage(stage, x, mask)
    return x & mask


def _hash2(x: int, a: int, b: int, mask: int) -> int:
    return _hash(_hash(x ^ a, mask) ^ b, mask)


def _build_ops_sets(mask: int) -> tuple[list[int], list[int], list[tuple[int, int]]]:
    consts = {0, 1}
    shifts = {3, 5, 9, 12, 16, 19}
    muladds = []
    for op1, val1, op2, _, val3 in HASH_STAGES:
        consts.add(val1 & mask)
        if op1 == "+" and op2 == "+":
            muladds.append(_linear_muladd((op1, val1, op2, "<<", val3), mask))
    return sorted(consts), sorted(shifts), muladds


def _enumerate(
    tests: list[tuple[int, ...]] | list[int],
    max_size: int,
    mask: int,
    target: tuple[int, ...],
    max_per_size: int,
    time_limit: float,
    extra_ops: bool = False,
) -> tuple[bool, int | None]:
    start = time.time()
    consts, shifts, muladds = _build_ops_sets(mask)

    exprs_by_size: dict[int, list[Expr]] = defaultdict(list)
    seen: dict[tuple[int, ...], int] = {}

    def add_expr(expr: Expr) -> None:
        key = expr.vals
        if key in seen:
            if expr.size < seen[key]:
                seen[key] = expr.size
            return
        seen[key] = expr.size
        exprs_by_size[expr.size].append(expr)

    if tests and isinstance(tests[0], tuple):
        # Multiple input variables packed in each tuple.
        arity = len(tests[0])
        for i in range(arity):
            add_expr(Expr(0, tuple(t[i] for t in tests)))
    else:
        add_expr(Expr(0, tuple(tests)))  # x
    for c in consts:
        add_expr(Expr(0, tuple([c] * len(tests))))

    for size in range(1, max_size + 1):
        if time.time() - start > time_limit:
            return False, None

        # unary ops
        for e in list(exprs_by_size[size - 1]):
            for s in shifts:
                add_expr(Expr(size, tuple(((v << s) & mask) for v in e.vals)))
                add_expr(Expr(size, tuple(((v >> s) & mask) for v in e.vals)))
            for c in consts:
                add_expr(Expr(size, tuple(((v + c) & mask) for v in e.vals)))
                add_expr(Expr(size, tuple(((v ^ c) & mask) for v in e.vals)))
            for mult, add in muladds:
                add_expr(Expr(size, tuple(((v * mult + add) & mask) for v in e.vals)))

        # binary ops
        for a_size in range(0, size):
            b_size = size - 1 - a_size
            for ea in exprs_by_size[a_size]:
                for eb in exprs_by_size[b_size]:
                    if id(ea) > id(eb):
                        continue
                    add_expr(Expr(size, tuple(((va + vb) & mask) for va, vb in zip(ea.vals, eb.vals))))
                    add_expr(Expr(size, tuple(((va ^ vb) & mask) for va, vb in zip(ea.vals, eb.vals))))
                    if extra_ops:
                        add_expr(Expr(size, tuple(((va - vb) & mask) for va, vb in zip(ea.vals, eb.vals))))
                        add_expr(Expr(size, tuple(((va & vb) & mask) for va, vb in zip(ea.vals, eb.vals))))
                        add_expr(Expr(size, tuple(((va | vb) & mask) for va, vb in zip(ea.vals, eb.vals))))
                        add_expr(Expr(size, tuple(((va * vb) & mask) for va, vb in zip(ea.vals, eb.vals))))

        if len(exprs_by_size[size]) > max_per_size:
            exprs_by_size[size] = exprs_by_size[size][:max_per_size]

        if target in seen:
            return True, size

    return False, None


def _eval_ast(ast: tuple, x: int | tuple[int, ...], mask: int) -> int:
    op = ast[0]
    if op == "x":
        if isinstance(x, tuple):
            idx = ast[1] if len(ast) > 1 else 0
            return x[idx] & mask
        return x & mask
    if op == "const":
        return ast[1] & mask
    if op == "shl":
        return (( _eval_ast(ast[1], x, mask) << ast[2]) & mask)
    if op == "shr":
        return (( _eval_ast(ast[1], x, mask) >> ast[2]) & mask)
    if op == "+":
        return (_eval_ast(ast[1], x, mask) + _eval_ast(ast[2], x, mask)) & mask
    if op == "^":
        return (_eval_ast(ast[1], x, mask) ^ _eval_ast(ast[2], x, mask)) & mask
    if op == "-":
        return (_eval_ast(ast[1], x, mask) - _eval_ast(ast[2], x, mask)) & mask
    if op == "&":
        return (_eval_ast(ast[1], x, mask) & _eval_ast(ast[2], x, mask)) & mask
    if op == "|":
        return (_eval_ast(ast[1], x, mask) | _eval_ast(ast[2], x, mask)) & mask
    if op == "*":
        return (_eval_ast(ast[1], x, mask) * _eval_ast(ast[2], x, mask)) & mask
    if op == "madd":
        v = _eval_ast(ast[1], x, mask)
        return (v * ast[2] + ast[3]) & mask
    raise ValueError(f"unknown ast op {op}")


def _ast_to_z3(ast: tuple, x: z3.BitVecRef | list[z3.BitVecRef], bits: int) -> z3.BitVecRef:
    op = ast[0]
    if op == "x":
        if isinstance(x, list):
            idx = ast[1] if len(ast) > 1 else 0
            return x[idx]
        return x
    if op == "const":
        return z3.BitVecVal(ast[1], bits)
    if op == "shl":
        return z3.LShR(_ast_to_z3(ast[1], x, bits) << ast[2], 0)
    if op == "shr":
        return z3.LShR(_ast_to_z3(ast[1], x, bits), ast[2])
    if op == "+":
        return _ast_to_z3(ast[1], x, bits) + _ast_to_z3(ast[2], x, bits)
    if op == "^":
        return _ast_to_z3(ast[1], x, bits) ^ _ast_to_z3(ast[2], x, bits)
    if op == "-":
        return _ast_to_z3(ast[1], x, bits) - _ast_to_z3(ast[2], x, bits)
    if op == "&":
        return _ast_to_z3(ast[1], x, bits) & _ast_to_z3(ast[2], x, bits)
    if op == "|":
        return _ast_to_z3(ast[1], x, bits) | _ast_to_z3(ast[2], x, bits)
    if op == "*":
        return _ast_to_z3(ast[1], x, bits) * _ast_to_z3(ast[2], x, bits)
    if op == "madd":
        return _ast_to_z3(ast[1], x, bits) * z3.BitVecVal(ast[2], bits) + z3.BitVecVal(ast[3], bits)
    raise ValueError(f"unknown ast op {op}")


def _hash_z3(x: z3.BitVecRef, bits: int) -> z3.BitVecRef:
    for op1, val1, op2, op3, val3 in HASH_STAGES:
        tmp = x << val3 if op3 == "<<" else z3.LShR(x, val3)
        if op1 == "+":
            x = x + z3.BitVecVal(val1, bits)
        else:
            x = x ^ z3.BitVecVal(val1, bits)
        if op2 == "+":
            x = x + tmp
        else:
            x = x ^ tmp
    return x


def _hash_stage(x: int, stage_idx: int, mask: int) -> int:
    return _apply_stage(HASH_STAGES[stage_idx], x, mask)


def _hash_stage_z3(x: z3.BitVecRef, stage_idx: int, bits: int) -> z3.BitVecRef:
    op1, val1, op2, op3, val3 = HASH_STAGES[stage_idx]
    tmp = x << val3 if op3 == "<<" else z3.LShR(x, val3)
    if op1 == "+":
        x = x + z3.BitVecVal(val1, bits)
    else:
        x = x ^ z3.BitVecVal(val1, bits)
    if op2 == "+":
        x = x + tmp
    else:
        x = x ^ tmp
    return x


def _hash2_z3(x: z3.BitVecRef, a: z3.BitVecRef, b: z3.BitVecRef, bits: int) -> z3.BitVecRef:
    return _hash_z3(_hash_z3(x ^ a, bits) ^ b, bits)


def _ast_counts(ast: tuple) -> dict[str, int]:
    seen: set[int] = set()
    counts: dict[str, int] = {}

    def walk(node: tuple) -> None:
        key = id(node)
        if key in seen:
            return
        seen.add(key)
        op = node[0]
        if op in {"x", "const"}:
            return
        counts[op] = counts.get(op, 0) + 1
        if op in {"shl", "shr"}:
            walk(node[1])
        elif op in {"+", "^", "-", "&", "|", "*"}:
            walk(node[1])
            walk(node[2])
        elif op == "madd":
            walk(node[1])

    walk(ast)
    return counts


def _cost_tuple(costs: dict[str, int]) -> tuple[int, ...]:
    return tuple(costs.get(k, 0) for k in ENGINE_KEYS)


def _cost_add(a: tuple[int, ...], b: tuple[int, ...]) -> tuple[int, ...]:
    return tuple(x + y for x, y in zip(a, b))


def _cost_leq(a: tuple[int, ...], b: tuple[int, ...]) -> bool:
    return all(x <= y for x, y in zip(a, b))


def _op_cost(op: str) -> tuple[int, ...]:
    costs = OP_COSTS.get(op, {})
    return _cost_tuple(costs)


def _cost_to_dict(cost_tuple: tuple[int, ...]) -> dict[str, int]:
    return {k: v for k, v in zip(ENGINE_KEYS, cost_tuple) if v}


def _ast_cost(ast: tuple) -> tuple[int, ...]:
    seen: set[int] = set()
    total = (0, 0, 0, 0, 0)

    def walk(node: tuple) -> None:
        nonlocal total
        key = id(node)
        if key in seen:
            return
        seen.add(key)
        op = node[0]
        if op in {"x", "const"}:
            return
        total = _cost_add(total, _op_cost(op))
        if op in {"shl", "shr"}:
            walk(node[1])
        elif op in {"+", "^", "-", "&", "|", "*"}:
            walk(node[1])
            walk(node[2])
        elif op == "madd":
            walk(node[1])

    walk(ast)
    return total


def _engine_counts(ast: tuple) -> dict[str, int]:
    # Map AST ops to ISA engine counts. Hash ops are VALU-lane ops by default.
    return _cost_to_dict(_ast_cost(ast))


def _baseline_ast() -> tuple:
    # Build AST for full hash stages in order.
    linear: list[tuple[int, int]] = []
    bitwise: list[tuple[str, int, str, str, int]] = []
    for op1, val1, op2, op3, val3 in HASH_STAGES:
        if op1 == "+" and op2 == "+":
            mult = (1 + (1 << val3)) % (2**32)
            linear.append((mult, val1))
        else:
            bitwise.append((op1, val1, op2, op3, val3))
    x_ast: tuple = ("x",)
    lin_i = 0
    bit_i = 0
    for op1, _, op2, op3, _ in HASH_STAGES:
        if op1 == "+" and op2 == "+":
            mult, add = linear[lin_i]
            lin_i += 1
            x_ast = ("madd", x_ast, mult, add)
        else:
            stage = bitwise[bit_i]
            bit_i += 1
            op1b, constb, op2b, shift_op, shift = stage
            shift_ast = ("shl", x_ast, shift) if shift_op == "<<" else ("shr", x_ast, shift)
            op1_ast = (op1b, x_ast, ("const", constb))
            x_ast = (op2b, op1_ast, shift_ast)
    return x_ast


def _ast_replace_x(ast: tuple, new_x: tuple) -> tuple:
    memo: dict[int, tuple] = {}

    def walk(node: tuple) -> tuple:
        key = id(node)
        if key in memo:
            return memo[key]
        op = node[0]
        if op == "x":
            memo[key] = new_x
            return new_x
        if op == "const":
            memo[key] = node
            return node
        if op in {"shl", "shr"}:
            out = (op, walk(node[1]), node[2])
            memo[key] = out
            return out
        if op in {"+", "^", "-", "&", "|", "*"}:
            out = (op, walk(node[1]), walk(node[2]))
            memo[key] = out
            return out
        if op == "madd":
            out = ("madd", walk(node[1]), node[2], node[3])
            memo[key] = out
            return out
        memo[key] = node
        return node

    return walk(ast)


def _baseline_hash2_ast() -> tuple:
    # hash(hash(x ^ a) ^ b) with baseline hash AST.
    x = ("x", 0)
    a = ("x", 1)
    b = ("x", 2)
    inner = ("^", x, a)
    inner_hash = _ast_replace_x(_baseline_ast(), inner)
    outer_in = ("^", inner_hash, b)
    return _ast_replace_x(_baseline_ast(), outer_in)


def _baseline_hash2_ops() -> list[tuple]:
    def add_hash_ops(dst: list[tuple]) -> None:
        for op1, val1, op2, op3, val3 in HASH_STAGES:
            if op1 == "+" and op2 == "+":
                mult = (1 + (1 << val3)) % (1 << 32)
                dst.append(("madd", mult, val1))
            elif op1 == "^" and op2 == "^":
                dst.append(("xorsr", val3) if op3 == ">>" else ("xorsl", val3))
                dst.append(("xorc", val1))
            elif op1 == "+" and op2 == "^":
                if op3 == "<<":
                    dst.append(("addxor_l", val1, val3))
                else:
                    dst.append(("addxor_r", val1, val3))
            else:
                dst.append(("xorc", val1))

    ops: list[tuple] = [("xorv", 0)]
    add_hash_ops(ops)
    ops.append(("xorv", 1))
    add_hash_ops(ops)
    return ops


def baseline_report() -> None:
    ast = _baseline_ast()
    counts = _ast_counts(ast)
    total_ops = sum(counts.values())
    engine_counts = _engine_counts(ast)
    print(f"baseline_fullhash_ops: {total_ops} op_counts={counts} engine_counts={engine_counts}")
    ast2 = _baseline_hash2_ast()
    counts2 = _ast_counts(ast2)
    total_ops2 = sum(counts2.values())
    engine_counts2 = _engine_counts(ast2)
    print(f"baseline_hash2_ops: {total_ops2} op_counts={counts2} engine_counts={engine_counts2}")
    prog2, consts2 = _baseline_hash2_program()
    print(f"baseline_hash2_program_len: {len(prog2)} consts={len(consts2)}")


def _enumerate_ast(
    tests: list[int] | list[tuple[int, ...]],
    max_size: int,
    mask: int,
    target: tuple[int, ...],
    max_per_size: int,
    time_limit: float,
    extra_ops: bool = False,
) -> tuple[bool, int | None, tuple | None]:
    start = time.time()
    consts, shifts, muladds = _build_ops_sets(mask)

    exprs_by_size: dict[int, list[ExprAst]] = defaultdict(list)
    seen: dict[tuple[int, ...], int] = {}

    def add_expr(expr: ExprAst) -> None:
        key = expr.vals
        if key in seen:
            if expr.size < seen[key]:
                seen[key] = expr.size
            return
        seen[key] = expr.size
        exprs_by_size[expr.size].append(expr)

    if tests and isinstance(tests[0], tuple):
        arity = len(tests[0])
        for i in range(arity):
            add_expr(ExprAst(0, tuple(t[i] for t in tests), ("x", i), cost=(0, 0, 0, 0, 0)))
    else:
        add_expr(ExprAst(0, tuple(tests), ("x",), cost=(0, 0, 0, 0, 0)))
    for c in consts:
        add_expr(ExprAst(0, tuple([c] * len(tests)), ("const", c), cost=(0, 0, 0, 0, 0)))

    for size in range(1, max_size + 1):
        if time.time() - start > time_limit:
            return False, None, None

        for e in list(exprs_by_size[size - 1]):
            for s in shifts:
                add_expr(ExprAst(size, tuple(((v << s) & mask) for v in e.vals), ("shl", e.ast, s), cost=_cost_add(e.cost, _op_cost("shl"))))
                add_expr(ExprAst(size, tuple(((v >> s) & mask) for v in e.vals), ("shr", e.ast, s), cost=_cost_add(e.cost, _op_cost("shr"))))
            for c in consts:
                add_expr(ExprAst(size, tuple(((v + c) & mask) for v in e.vals), ("+", e.ast, ("const", c)), cost=_cost_add(e.cost, _op_cost("+"))))
                add_expr(ExprAst(size, tuple(((v ^ c) & mask) for v in e.vals), ("^", e.ast, ("const", c)), cost=_cost_add(e.cost, _op_cost("^"))))
            for mult, add in muladds:
                add_expr(ExprAst(size, tuple(((v * mult + add) & mask) for v in e.vals), ("madd", e.ast, mult, add), cost=_cost_add(e.cost, _op_cost("madd"))))

        for a_size in range(0, size):
            b_size = size - 1 - a_size
            for ea in exprs_by_size[a_size]:
                for eb in exprs_by_size[b_size]:
                    if id(ea) > id(eb):
                        continue
                    add_expr(ExprAst(size, tuple(((va + vb) & mask) for va, vb in zip(ea.vals, eb.vals)), ("+", ea.ast, eb.ast), cost=_cost_add(_cost_add(ea.cost, eb.cost), _op_cost("+"))))
                    add_expr(ExprAst(size, tuple(((va ^ vb) & mask) for va, vb in zip(ea.vals, eb.vals)), ("^", ea.ast, eb.ast), cost=_cost_add(_cost_add(ea.cost, eb.cost), _op_cost("^"))))
                    if extra_ops:
                        add_expr(ExprAst(size, tuple(((va - vb) & mask) for va, vb in zip(ea.vals, eb.vals)), ("-", ea.ast, eb.ast), cost=_cost_add(_cost_add(ea.cost, eb.cost), _op_cost("-"))))
                        add_expr(ExprAst(size, tuple(((va & vb) & mask) for va, vb in zip(ea.vals, eb.vals)), ("&", ea.ast, eb.ast), cost=_cost_add(_cost_add(ea.cost, eb.cost), _op_cost("&"))))
                        add_expr(ExprAst(size, tuple(((va | vb) & mask) for va, vb in zip(ea.vals, eb.vals)), ("|", ea.ast, eb.ast), cost=_cost_add(_cost_add(ea.cost, eb.cost), _op_cost("|"))))
                        add_expr(ExprAst(size, tuple(((va * vb) & mask) for va, vb in zip(ea.vals, eb.vals)), ("*", ea.ast, eb.ast), cost=_cost_add(_cost_add(ea.cost, eb.cost), _op_cost("*"))))

        if len(exprs_by_size[size]) > max_per_size:
            exprs_by_size[size] = exprs_by_size[size][:max_per_size]

        if target in seen:
            for expr in exprs_by_size[size]:
                if expr.vals == target:
                    return True, size, expr.ast
            # fallback: search all sizes
            for size2 in range(size):
                for expr in exprs_by_size[size2]:
                    if expr.vals == target:
                        return True, size2, expr.ast
            return True, size, None

    return False, None, None


def _enumerate_ast_cost(
    tests: list[int] | list[tuple[int, ...]],
    cost_max: int,
    eval_bits: int,
    out_mask_bits: int | None,
    target: tuple[int, ...],
    max_per_cost: int,
    time_limit: float,
    extra_ops: bool = False,
    cost_budget: tuple[int, ...] | None = None,
) -> tuple[bool, int | None, tuple | None]:
    start = time.time()
    eval_mask = (1 << eval_bits) - 1
    out_mask = (1 << out_mask_bits) - 1 if out_mask_bits else eval_mask

    consts, shifts, muladds = _build_ops_sets(eval_mask)

    exprs_by_cost: dict[int, list[ExprAst]] = defaultdict(list)
    seen: dict[tuple[int, ...], int] = {}

    if cost_budget is None:
        # default: only cap valu cost
        cost_budget = (10**9, cost_max, 10**9, 10**9, 10**9)

    def add_expr(expr: ExprAst) -> None:
        key = expr.vals
        cost_key = expr.size
        if key in seen:
            if cost_key < seen[key]:
                seen[key] = cost_key
            return
        seen[key] = cost_key
        exprs_by_cost[cost_key].append(expr)

    def _mask_vals(vals: tuple[int, ...]) -> tuple[int, ...]:
        return tuple(v & out_mask for v in vals)

    # Base expressions
    if tests and isinstance(tests[0], tuple):
        arity = len(tests[0])
        for i in range(arity):
            add_expr(ExprAst(0, _mask_vals(tuple(t[i] for t in tests)), ("x", i), cost=(0, 0, 0, 0, 0)))
    else:
        add_expr(ExprAst(0, _mask_vals(tuple(tests)), ("x",), cost=(0, 0, 0, 0, 0)))
    for c in consts:
        add_expr(ExprAst(0, _mask_vals(tuple([c] * len(tests))), ("const", c), cost=(0, 0, 0, 0, 0)))

    # Enumerate by cost (valu)
    for cost in range(1, cost_max + 1):
        if time.time() - start > time_limit:
            return False, None, None

        # unary ops
        for e_cost in range(0, cost):
            for e in exprs_by_cost.get(e_cost, []):
                if time.time() - start > time_limit:
                    return False, None, None
                # shl/shr
                for s in shifts:
                    if time.time() - start > time_limit:
                        return False, None, None
                    oc = _op_cost("shl")
                    cost_tuple = _cost_add(e.cost, oc)
                    if not _cost_leq(cost_tuple, cost_budget):
                        continue
                    cost_key = cost_tuple[ENGINE_KEYS.index("valu")]
                    if cost_key != cost:
                        continue
                    vals = _mask_vals(tuple(((v << s) & eval_mask) for v in e.vals))
                    add_expr(ExprAst(cost_key, vals, ("shl", e.ast, s), cost=cost_tuple))
                    oc = _op_cost("shr")
                    cost_tuple = _cost_add(e.cost, oc)
                    if not _cost_leq(cost_tuple, cost_budget):
                        continue
                    cost_key = cost_tuple[ENGINE_KEYS.index("valu")]
                    if cost_key != cost:
                        continue
                    vals = _mask_vals(tuple(((v >> s) & eval_mask) for v in e.vals))
                    add_expr(ExprAst(cost_key, vals, ("shr", e.ast, s), cost=cost_tuple))
                # add/xor const
                for c in consts:
                    if time.time() - start > time_limit:
                        return False, None, None
                    oc = _op_cost("+")
                    cost_tuple = _cost_add(e.cost, oc)
                    if _cost_leq(cost_tuple, cost_budget):
                        cost_key = cost_tuple[ENGINE_KEYS.index("valu")]
                        if cost_key == cost:
                            vals = _mask_vals(tuple(((v + c) & eval_mask) for v in e.vals))
                            add_expr(ExprAst(cost_key, vals, ("+", e.ast, ("const", c)), cost=cost_tuple))
                    oc = _op_cost("^")
                    cost_tuple = _cost_add(e.cost, oc)
                    if _cost_leq(cost_tuple, cost_budget):
                        cost_key = cost_tuple[ENGINE_KEYS.index("valu")]
                        if cost_key == cost:
                            vals = _mask_vals(tuple(((v ^ c) & eval_mask) for v in e.vals))
                            add_expr(ExprAst(cost_key, vals, ("^", e.ast, ("const", c)), cost=cost_tuple))
                # madd
                oc = _op_cost("madd")
                for mult, add in muladds:
                    if time.time() - start > time_limit:
                        return False, None, None
                    cost_tuple = _cost_add(e.cost, oc)
                    if not _cost_leq(cost_tuple, cost_budget):
                        continue
                    cost_key = cost_tuple[ENGINE_KEYS.index("valu")]
                    if cost_key != cost:
                        continue
                    vals = _mask_vals(tuple(((v * mult + add) & eval_mask) for v in e.vals))
                    add_expr(ExprAst(cost_key, vals, ("madd", e.ast, mult, add), cost=cost_tuple))

        # binary ops
        for a_cost in range(0, cost):
            for ea in exprs_by_cost.get(a_cost, []):
                for b_cost in range(0, cost):
                    for eb in exprs_by_cost.get(b_cost, []):
                        if time.time() - start > time_limit:
                            return False, None, None
                        if id(ea) > id(eb):
                            continue
                        for op in ["+", "^"] + (["-", "&", "|", "*"] if extra_ops else []):
                            oc = _op_cost(op)
                            cost_tuple = _cost_add(_cost_add(ea.cost, eb.cost), oc)
                            if not _cost_leq(cost_tuple, cost_budget):
                                continue
                            cost_key = cost_tuple[ENGINE_KEYS.index("valu")]
                            if cost_key != cost:
                                continue
                            if op == "+":
                                vals = _mask_vals(tuple(((va + vb) & eval_mask) for va, vb in zip(ea.vals, eb.vals)))
                            elif op == "^":
                                vals = _mask_vals(tuple(((va ^ vb) & eval_mask) for va, vb in zip(ea.vals, eb.vals)))
                            elif op == "-":
                                vals = _mask_vals(tuple(((va - vb) & eval_mask) for va, vb in zip(ea.vals, eb.vals)))
                            elif op == "&":
                                vals = _mask_vals(tuple(((va & vb) & eval_mask) for va, vb in zip(ea.vals, eb.vals)))
                            elif op == "|":
                                vals = _mask_vals(tuple(((va | vb) & eval_mask) for va, vb in zip(ea.vals, eb.vals)))
                            else:
                                vals = _mask_vals(tuple(((va * vb) & eval_mask) for va, vb in zip(ea.vals, eb.vals)))
                            add_expr(ExprAst(cost_key, vals, (op, ea.ast, eb.ast), cost=cost_tuple))

        if len(exprs_by_cost.get(cost, [])) > max_per_cost:
            exprs_by_cost[cost] = exprs_by_cost[cost][:max_per_cost]

        if target in seen:
            for expr in exprs_by_cost.get(cost, []):
                if expr.vals == target:
                    return True, cost, expr.ast
            # fallback search
            for cost2 in range(cost + 1):
                for expr in exprs_by_cost.get(cost2, []):
                    if expr.vals == target:
                        return True, cost2, expr.ast
            return True, cost, None

    return False, None, None


def _resolve_bits(args) -> tuple[int, int]:
    eval_bits = args.eval_bits if args.eval_bits is not None else args.bits
    out_mask_bits = args.test_mask_bits if args.test_mask_bits is not None else eval_bits
    if out_mask_bits > eval_bits:
        raise SystemExit(f"test-mask-bits ({out_mask_bits}) cannot exceed eval-bits ({eval_bits})")
    return eval_bits, out_mask_bits


def _z3_equiv(lhs: z3.BitVecRef, rhs: z3.BitVecRef, timeout_ms: int) -> tuple[bool | None, z3.ModelRef | None]:
    s = z3.SolverFor("QF_BV")
    if timeout_ms is not None and timeout_ms > 0:
        s.set("timeout", timeout_ms)
    s.add(lhs != rhs)
    res = s.check()
    if res == z3.unsat:
        return True, None
    if res == z3.sat:
        return False, s.model()
    return None, None


def run_cegis(args) -> None:
    mask = (1 << args.bits) - 1
    random.seed(args.seed)
    tests = [random.getrandbits(args.bits) for _ in range(args.tests)]
    target = tuple(_hash(x, mask) for x in tests)

    start = time.time()
    rounds = 0
    while True:
        rounds += 1
        ok, size, ast = _enumerate_ast(
            tests=tests,
            max_size=args.max_size,
            mask=mask,
            target=target,
            max_per_size=args.max_per_size,
            time_limit=args.time_limit,
            extra_ops=args.extra_ops,
        )
        if not ok or ast is None:
            print(f"cegis: no expr <= {args.max_size} after {rounds} rounds")
            return
        # Prove with z3
        x = z3.BitVec("x", args.bits)
        cand = _ast_to_z3(ast, x, args.bits)
        target_z3 = _hash_z3(x, args.bits)
        s = z3.Solver()
        s.add(cand != target_z3)
        if s.check() == z3.unsat:
            print(f"cegis: proven size={size} rounds={rounds} ast={ast}")
            return
        model = s.model()
        cx = model[x].as_long()
        if cx not in tests:
            tests.append(cx)
            target = tuple(_hash(xv, mask) for xv in tests)
        if time.time() - start > args.time_limit:
            print(f"cegis: timeout after {rounds} rounds; best size={size}")
            return


def run_window_search(args) -> None:
    mask = (1 << args.bits) - 1
    random.seed(args.seed)
    tests = [random.getrandbits(args.bits) for _ in range(args.tests)]

    for start in range(len(HASH_STAGES) - args.window + 1):
        end = start + args.window
        stages = HASH_STAGES[start:end]
        if args.window == 2:
            target = tuple(
                _apply_stage(stages[-1], _apply_stage(stages[-2], x, mask), mask)
                for x in tests
            )
        else:
            target = tuple(
                _apply_stage(stages[-1], _apply_stage(stages[-2], _apply_stage(stages[-3], x, mask), mask), mask)
                for x in tests
            )
        orig = sum(_stage_cost(s) for s in stages)
        if args.emit_ast:
            ok, size, ast = _enumerate_ast(
                tests=tests,
                max_size=orig - 1,
                mask=mask,
                target=target,
                max_per_size=args.max_per_size,
                time_limit=args.time_limit,
            )
            print(
                f"window {start}-{end-1} orig_ops={orig} synth<={orig-1}? {ok} found_size={size}"
            )
            if ok and ast is not None:
                print(f"  ast: {ast}")
        else:
            ok, size = _enumerate(
                tests=tests,
                max_size=orig - 1,
                mask=mask,
                target=target,
                max_per_size=args.max_per_size,
                time_limit=args.time_limit,
                extra_ops=args.extra_ops,
            )
            print(
                f"window {start}-{end-1} orig_ops={orig} synth<={orig-1}? {ok} found_size={size}"
            )


def run_fullhash(args) -> None:
    mask = (1 << args.bits) - 1
    random.seed(args.seed)
    tests = [random.getrandbits(args.bits) for _ in range(args.tests)]
    target = tuple(_hash(x, mask) for x in tests)
    if args.emit_ast:
        ok, size, ast = _enumerate_ast(
            tests=tests,
            max_size=args.max_size,
            mask=mask,
            target=target,
            max_per_size=args.max_per_size,
            time_limit=args.time_limit,
            extra_ops=args.extra_ops,
        )
        print(f"fullhash synth<={args.max_size}? {ok} found_size={size}")
        if ok and ast is not None:
            print(f"ast: {ast}")
    else:
        ok, size = _enumerate(
            tests=tests,
            max_size=args.max_size,
            mask=mask,
            target=target,
            max_per_size=args.max_per_size,
            time_limit=args.time_limit,
            extra_ops=args.extra_ops,
        )
        print(f"fullhash synth<={args.max_size}? {ok} found_size={size}")


def run_compose2(args) -> None:
    mask = (1 << args.bits) - 1
    random.seed(args.seed)
    tests = [
        (random.getrandbits(args.bits), random.getrandbits(args.bits), random.getrandbits(args.bits))
        for _ in range(args.tests)
    ]
    target = tuple(_hash2(x, a, b, mask) for x, a, b in tests)

    # Heuristic x-only check (does not include a/b expressions).
    xs = [t[0] for t in tests]
    target_x = tuple(_hash2(x, tests[i][1], tests[i][2], mask) for i, x in enumerate(xs))
    ok, size = _enumerate(
        tests=xs,
        max_size=args.max_size,
        mask=mask,
        target=target_x,
        max_per_size=args.max_per_size,
        time_limit=args.time_limit,
        extra_ops=args.extra_ops,
    )
    print(f"compose2 (x-only heuristic) synth<={args.max_size}? {ok} found_size={size}")


def run_compose2_full(args) -> None:
    mask = (1 << args.bits) - 1
    random.seed(args.seed)
    tests = [
        (random.getrandbits(args.bits), random.getrandbits(args.bits), random.getrandbits(args.bits))
        for _ in range(args.tests)
    ]
    target = tuple(_hash2(x, a, b, mask) for x, a, b in tests)
    ok, size, ast = _enumerate_ast(
        tests=tests,
        max_size=args.max_size,
        mask=mask,
        target=target,
        max_per_size=args.max_per_size,
        time_limit=args.time_limit,
        extra_ops=args.extra_ops,
    )
    print(f"compose2_full synth<={args.max_size}? {ok} found_size={size}")
    if ok and ast is not None:
        counts = _ast_counts(ast)
        engine_counts = _engine_counts(ast)
        print(f"ast: {ast}")
        print(f"op_counts: {counts} prog_ops={size} engine_counts={engine_counts}")


def run_compose2_cegis(args) -> None:
    if args.cost_max is not None:
        return run_compose2_cegis_cost(args)
    mask = (1 << args.bits) - 1
    random.seed(args.seed)
    tests = [
        (random.getrandbits(args.bits), random.getrandbits(args.bits), random.getrandbits(args.bits))
        for _ in range(args.tests)
    ]
    target = tuple(_hash2(x, a, b, mask) for x, a, b in tests)

    size_min = args.size_min if args.size_min is not None else args.max_size
    size_max = args.size_max if args.size_max is not None else args.max_size

    for size_limit in range(size_min, size_max + 1, args.size_step):
        start = time.time()
        rounds = 0
        while True:
            rounds += 1
            ok, size, ast = _enumerate_ast(
                tests=tests,
                max_size=size_limit,
                mask=mask,
                target=target,
                max_per_size=args.max_per_size,
                time_limit=args.time_limit,
                extra_ops=args.extra_ops,
            )
            if not ok or ast is None:
                print(f"compose2_cegis: no expr <= {size_limit} after {rounds} rounds")
                break
            # Prove with z3
            xs = [z3.BitVec("x", args.bits), z3.BitVec("a", args.bits), z3.BitVec("b", args.bits)]
            cand = _ast_to_z3(ast, xs, args.bits)
            target_z3 = _hash2_z3(xs[0], xs[1], xs[2], args.bits)
            ok, model = _z3_equiv(cand, target_z3, args.z3_timeout_ms)
            if ok is True:
                counts = _ast_counts(ast)
                engine_counts = _engine_counts(ast)
                print(f"compose2_cegis: proven size={size} rounds={rounds} ast={ast}")
                print(f"op_counts: {counts} prog_ops={size} engine_counts={engine_counts}")
                return
            if ok is None:
                print(f"compose2_cegis: z3 timeout/unknown at size={size}")
                break
            cx = (model[xs[0]].as_long(), model[xs[1]].as_long(), model[xs[2]].as_long())
            if cx not in tests:
                tests.append(cx)
                target = tuple(_hash2(xv, av, bv, mask) for xv, av, bv in tests)
            if time.time() - start > args.time_limit:
                print(f"compose2_cegis: timeout after {rounds} rounds; best size={size}")
                break
    return


def run_compose2_cegis_cost(args) -> None:
    eval_bits, out_mask_bits = _resolve_bits(args)
    eval_mask = (1 << eval_bits) - 1
    out_mask = (1 << out_mask_bits) - 1 if out_mask_bits else eval_mask
    random.seed(args.seed)
    tests = [
        (random.getrandbits(eval_bits), random.getrandbits(eval_bits), random.getrandbits(eval_bits))
        for _ in range(args.tests)
    ]
    if args.enumerator == "program" and args.program_mode == "mitm" and args.mitm_tests is not None:
        if args.mitm_tests < 1:
            raise SystemExit("--mitm-tests must be >= 1")
        tests = tests[: min(args.mitm_tests, len(tests))]
    target = tuple((_hash2(x, a, b, eval_mask) & out_mask) for x, a, b in tests)

    if args.baseline_hash2_check:
        base_ast = _baseline_hash2_ast()
        base_cost = _ast_cost(base_ast)[ENGINE_KEYS.index("valu")]
        base_prog, base_consts = _baseline_hash2_program()
        base_ops = _baseline_hash2_ops()
        base_ops_cost = sum(
            {"madd": 1, "xorc": 1, "xorv": 1, "xorsr": 2, "xorsl": 2, "addxor_l": 3, "addxor_r": 3}[op[0]]
            for op in base_ops
        )
        xs = [t[0] for t in tests]
        as_ = [t[1] for t in tests]
        bs = [t[2] for t in tests]
        pool = [xs, as_, bs] + [[c] * len(xs) for c in base_consts]
        out = _eval_program(base_prog, pool, eval_mask, [])
        ok_eval = all(((y & out_mask) == t) for y, t in zip(out, target))
        print(f"baseline_hash2_check: cost={base_cost} prog_len={len(base_prog)} eval_ok={ok_eval} ops_cost={base_ops_cost} ops_len={len(base_ops)}")
        if args.enumerator == "program" and args.program_mode == "dp":
            ok, cost, program, _meta = _enumerate_program_cost(
                tests=tests,
                cost_max=base_cost,
                eval_bits=eval_bits,
                out_mask_bits=out_mask_bits,
                target=target,
                max_states=args.max_per_size,
                time_limit=args.time_limit,
                extra_ops=args.extra_ops,
                program_k=args.program_k,
                mode="dp",
            )
            print(f"baseline_hash2_check: dp_found={ok} cost={cost}")
        else:
            print("baseline_hash2_check: set --enumerator program --program-mode dp to test enumerator coverage")

    if args.cost_max is None:
        raise SystemExit("compose2_cegis_cost requires --cost-max")
    cost_min = args.cost_min if args.cost_min is not None else args.cost_max
    cost_max = args.cost_max
    if cost_min > cost_max:
        raise SystemExit(f"cost-min ({cost_min}) cannot exceed cost-max ({cost_max})")

    for cost_limit in range(cost_min, cost_max + 1, args.cost_step):
        start = time.time()
        rounds = 0
        while True:
            rounds += 1
            if args.enumerator == "program":
                if args.program_mode == "mitm":
                    if args.mitm_splits is not None:
                        splits = [int(s) for s in args.mitm_splits.split(",") if s.strip() != ""]
                    elif args.mitm_cost_split is not None:
                        splits = [args.mitm_cost_split]
                    else:
                        splits = [None]
                    per_split = max(1.0, args.time_limit / max(1, len(splits)))
                    ok = False
                    cost = None
                    program = None
                    meta = {}
                    for split in splits:
                        ok, cost, program, meta = _mitm_enumerate(
                            tests=tests,
                            cost_max=cost_limit,
                            eval_bits=eval_bits,
                            out_mask_bits=out_mask_bits,
                            target=target,
                            time_limit=per_split,
                            extra_ops=args.extra_ops,
                            restrict_ops=args.mitm_restrict,
                            cost_split=split,
                            fast=args.mitm_fast,
                            xorv_exact=args.mitm_xorv_exact,
                            xorv_each=args.mitm_xorv_each,
                        )
                        if ok:
                            break
                    ast = None
                else:
                    ok, cost, program, meta = _enumerate_program_cost(
                        tests=tests,
                        cost_max=cost_limit,
                        eval_bits=eval_bits,
                        out_mask_bits=out_mask_bits,
                        target=target,
                        max_states=args.max_per_size,
                        time_limit=args.time_limit,
                        extra_ops=args.extra_ops,
                        program_k=args.program_k,
                        mode=args.program_mode,
                    )
                    ast = None
            else:
                ok, cost, ast = _enumerate_ast_cost(
                    tests=tests,
                    cost_max=cost_limit,
                    eval_bits=eval_bits,
                    out_mask_bits=out_mask_bits,
                    target=target,
                    max_per_cost=args.max_per_size,
                    time_limit=args.time_limit,
                    extra_ops=args.extra_ops,
                )
                program = None
                meta = {}
            if not ok or (ast is None and program is None):
                if meta.get("timeout"):
                    print(f"compose2_cegis: mitm timeout at cost={cost_limit}")
                else:
                    print(f"compose2_cegis: no expr <= {cost_limit} after {rounds} rounds")
                break
            xs = [z3.BitVec("x", eval_bits), z3.BitVec("a", eval_bits), z3.BitVec("b", eval_bits)]
            if program is not None:
                if meta.get("mode") == "mitm":
                    cand = _ops_to_z3(program, xs, eval_bits)
                else:
                    base_exprs = xs + [z3.BitVecVal(c, eval_bits) for c in meta.get("consts", [])]
                    cand = _program_to_z3(program, base_exprs, eval_bits)
            else:
                cand = _ast_to_z3(ast, xs, eval_bits)
            target_z3 = _hash2_z3(xs[0], xs[1], xs[2], eval_bits)
            ok, model = _z3_equiv(cand, target_z3, args.z3_timeout_ms)
            if ok is True:
                if program is not None:
                    print(f"compose2_cegis: proven cost={cost} rounds={rounds} program_len={len(program)}")
                    print(f"program: {program}")
                else:
                    counts = _ast_counts(ast)
                    engine_counts = _engine_counts(ast)
                    print(f"compose2_cegis: proven cost={cost} rounds={rounds} ast={ast}")
                    print(f"op_counts: {counts} engine_counts={engine_counts}")
                return
            if ok is None:
                print(f"compose2_cegis: z3 timeout/unknown at cost={cost}")
                break
            cx = (model[xs[0]].as_long(), model[xs[1]].as_long(), model[xs[2]].as_long())
            if cx not in tests:
                tests.append(cx)
                target = tuple((_hash2(xv, av, bv, eval_mask) & out_mask) for xv, av, bv in tests)
            if time.time() - start > args.time_limit:
                print(f"compose2_cegis: timeout after {rounds} rounds; best cost={cost}")
                break
    return


def run_fullhash_cegis_cost(args) -> None:
    eval_bits, out_mask_bits = _resolve_bits(args)
    eval_mask = (1 << eval_bits) - 1
    out_mask = (1 << out_mask_bits) - 1 if out_mask_bits else eval_mask
    random.seed(args.seed)
    if args.exhaustive and eval_bits <= 8:
        tests = [i for i in range(1 << eval_bits)]
    else:
        tests = [random.getrandbits(eval_bits) for _ in range(args.tests)]
    target = tuple((_hash(x, eval_mask) & out_mask) for x in tests)

    if args.cost_max is None:
        raise SystemExit("fullhash_cegis_cost requires --cost-max")

    start = time.time()
    rounds = 0
    while True:
        rounds += 1
        ok, cost, ast = _enumerate_ast_cost(
            tests=tests,
            cost_max=args.cost_max,
            eval_bits=eval_bits,
            out_mask_bits=out_mask_bits,
            target=target,
            max_per_cost=args.max_per_size,
            time_limit=args.time_limit,
            extra_ops=args.extra_ops,
        )
        if not ok or ast is None:
            print(f"fullhash_cegis: no expr <= {args.cost_max} after {rounds} rounds")
            return
        x = z3.BitVec("x", eval_bits)
        cand = _ast_to_z3(ast, x, eval_bits)
        target_z3 = _hash_z3(x, eval_bits)
        ok, model = _z3_equiv(cand, target_z3, args.z3_timeout_ms)
        if ok is True:
            counts = _ast_counts(ast)
            engine_counts = _engine_counts(ast)
            print(f"fullhash_cegis: proven cost={cost} rounds={rounds} ast={ast}")
            print(f"op_counts: {counts} engine_counts={engine_counts}")
            return
        if ok is None:
            print(f"fullhash_cegis: z3 timeout/unknown at cost={cost}")
            return
        cx = model[x].as_long()
        if cx not in tests:
            tests.append(cx)
            target = tuple((_hash(xv, eval_mask) & out_mask) for xv in tests)
        if time.time() - start > args.time_limit:
            print(f"fullhash_cegis: timeout after {rounds} rounds; best cost={cost}")
            return


def run_stage_cegis_cost(args) -> None:
    eval_bits, out_mask_bits = _resolve_bits(args)
    eval_mask = (1 << eval_bits) - 1
    out_mask = (1 << out_mask_bits) - 1 if out_mask_bits else eval_mask
    stage_idx = args.stage
    if stage_idx < 0 or stage_idx >= len(HASH_STAGES):
        raise SystemExit(f"stage must be in [0,{len(HASH_STAGES)-1}]")
    random.seed(args.seed)
    if args.exhaustive and eval_bits <= 8:
        tests = [i for i in range(1 << eval_bits)]
    else:
        tests = [random.getrandbits(eval_bits) for _ in range(args.tests)]
    target = tuple((_hash_stage(x, stage_idx, eval_mask) & out_mask) for x in tests)

    if args.cost_max is None:
        raise SystemExit("stage_cegis_cost requires --cost-max")

    start = time.time()
    rounds = 0
    while True:
        rounds += 1
        ok, cost, ast = _enumerate_ast_cost(
            tests=tests,
            cost_max=args.cost_max,
            eval_bits=eval_bits,
            out_mask_bits=out_mask_bits,
            target=target,
            max_per_cost=args.max_per_size,
            time_limit=args.time_limit,
            extra_ops=args.extra_ops,
        )
        if not ok or ast is None:
            print(f"stage_cegis: no expr <= {args.cost_max} after {rounds} rounds")
            return
        x = z3.BitVec("x", eval_bits)
        cand = _ast_to_z3(ast, x, eval_bits)
        target_z3 = _hash_stage_z3(x, stage_idx, eval_bits)
        ok, model = _z3_equiv(cand, target_z3, args.z3_timeout_ms)
        if ok is True:
            counts = _ast_counts(ast)
            engine_counts = _engine_counts(ast)
            print(f"stage_cegis: proven cost={cost} rounds={rounds} stage={stage_idx} ast={ast}")
            print(f"op_counts: {counts} engine_counts={engine_counts}")
            return
        if ok is None:
            print(f"stage_cegis: z3 timeout/unknown at cost={cost}")
            return
        cx = model[x].as_long()
        if cx not in tests:
            tests.append(cx)
            target = tuple((_hash_stage(xv, stage_idx, eval_mask) & out_mask) for xv in tests)
        if time.time() - start > args.time_limit:
            print(f"stage_cegis: timeout after {rounds} rounds; best cost={cost}")
            return


def run_prove_baseline(args) -> None:
    eval_bits, out_mask_bits = _resolve_bits(args)
    eval_mask = (1 << eval_bits) - 1
    out_mask = (1 << out_mask_bits) - 1 if out_mask_bits else eval_mask
    random.seed(args.seed)
    tests = [random.getrandbits(eval_bits) for _ in range(args.tests)]
    target = tuple((_hash(x, eval_mask) & out_mask) for x in tests)

    cost_limit = args.baseline_cost
    # Directly prove the known baseline AST first (fast calibration).
    ast = _baseline_ast()
    base_cost = _ast_cost(ast)[ENGINE_KEYS.index("valu")]
    print(f"prove_baseline: baseline_cost={base_cost} target_cost={cost_limit}")
    # Prove linear-stage equivalence: x + c + (x << s) == x*(1+2^s)+c
    x = z3.BitVec("x", eval_bits)
    linear_ok = True
    for op1, val1, op2, op3, val3 in HASH_STAGES:
        if op1 == "+" and op2 == "+":
            c = z3.BitVecVal(val1, eval_bits)
            shift = val3
            direct = (x + c) + (x << shift)
            mult = (1 + (1 << shift)) % (1 << eval_bits)
            linear = x * z3.BitVecVal(mult, eval_bits) + c
            ok, _ = _z3_equiv(direct, linear, args.z3_timeout_ms)
            if ok is not True:
                linear_ok = False
                break
    if not linear_ok:
        print("prove_baseline: linear-stage equivalence FAILED/UNKNOWN")
        return

    if args.baseline_full_proof:
        cand = _ast_to_z3(ast, x, eval_bits)
        target_z3 = _hash_z3(x, eval_bits)
        ok, _ = _z3_equiv(cand, target_z3, args.z3_timeout_ms)
        if ok is True:
            counts = _ast_counts(ast)
            engine_counts = _engine_counts(ast)
            print("prove_baseline: baseline_ast proven (full hash)")
            print(f"op_counts: {counts} engine_counts={engine_counts}")
        elif ok is None:
            print("prove_baseline: baseline_ast UNKNOWN (z3 timeout)")
            return
        else:
            print("prove_baseline: baseline_ast FAILED (unexpected)")
            return
    else:
        counts = _ast_counts(ast)
        engine_counts = _engine_counts(ast)
        print("prove_baseline: baseline_ast proven (linear stages)")
        print(f"op_counts: {counts} engine_counts={engine_counts}")

    if args.baseline_only:
        return

    start = time.time()
    rounds = 0
    while True:
        rounds += 1
        ok, cost, ast = _enumerate_ast_cost(
            tests=tests,
            cost_max=cost_limit,
            eval_bits=eval_bits,
            out_mask_bits=out_mask_bits,
            target=target,
            max_per_cost=args.max_per_size,
            time_limit=args.time_limit,
            extra_ops=args.extra_ops,
        )
        if not ok or ast is None:
            print(f"prove_baseline: no expr <= {cost_limit} after {rounds} rounds")
            return
        x = z3.BitVec("x", eval_bits)
        cand = _ast_to_z3(ast, x, eval_bits)
        target_z3 = _hash_z3(x, eval_bits)
        ok, model = _z3_equiv(cand, target_z3, args.z3_timeout_ms)
        if ok is True:
            counts = _ast_counts(ast)
            engine_counts = _engine_counts(ast)
            print(f"prove_baseline: proven cost={cost} rounds={rounds} ast={ast}")
            print(f"op_counts: {counts} engine_counts={engine_counts}")
            return
        if ok is None:
            print(f"prove_baseline: z3 timeout/unknown at cost={cost}")
            return
        cx = model[x].as_long()
        if cx not in tests:
            tests.append(cx)
            target = tuple((_hash(xv, eval_mask) & out_mask) for xv in tests)
        if time.time() - start > args.time_limit:
            print(f"prove_baseline: timeout after {rounds} rounds; best cost={cost}")
            return

def run_fullhash_cegis(args) -> None:
    if args.cost_max is not None:
        return run_fullhash_cegis_cost(args)
    mask = (1 << args.bits) - 1
    random.seed(args.seed)
    if args.exhaustive and args.bits <= 8:
        tests = [i for i in range(1 << args.bits)]
    else:
        tests = [random.getrandbits(args.bits) for _ in range(args.tests)]
    target = tuple(_hash(x, mask) for x in tests)

    if args.exhaustive and args.bits <= 8:
        ok, size, ast = _enumerate_ast(
            tests=tests,
            max_size=args.max_size,
            mask=mask,
            target=target,
            max_per_size=args.max_per_size,
            time_limit=args.time_limit,
            extra_ops=args.extra_ops,
        )
        if not ok or ast is None:
            print(f"fullhash_exhaustive: no expr <= {args.max_size}")
            return
        counts = _ast_counts(ast)
        engine_counts = _engine_counts(ast)
        print(f"fullhash_exhaustive: size={size} ast={ast}")
        print(f"op_counts: {counts} prog_ops={size} engine_counts={engine_counts}")
        return

    start = time.time()
    rounds = 0
    while True:
        rounds += 1
        ok, size, ast = _enumerate_ast(
            tests=tests,
            max_size=args.max_size,
            mask=mask,
            target=target,
            max_per_size=args.max_per_size,
            time_limit=args.time_limit,
            extra_ops=args.extra_ops,
        )
        if not ok or ast is None:
            print(f"fullhash_cegis: no expr <= {args.max_size} after {rounds} rounds")
            return
        x = z3.BitVec("x", args.bits)
        cand = _ast_to_z3(ast, x, args.bits)
        target_z3 = _hash_z3(x, args.bits)
        ok, model = _z3_equiv(cand, target_z3, args.z3_timeout_ms)
        if ok is True:
            counts = _ast_counts(ast)
            engine_counts = _engine_counts(ast)
            print(f"fullhash_cegis: proven size={size} rounds={rounds} ast={ast}")
            print(f"op_counts: {counts} prog_ops={size} engine_counts={engine_counts}")
            return
        if ok is None:
            print(f"fullhash_cegis: z3 timeout/unknown at size={size}")
            return
        cx = model[x].as_long()
        if cx not in tests:
            tests.append(cx)
            target = tuple(_hash(xv, mask) for xv in tests)
        if time.time() - start > args.time_limit:
            print(f"fullhash_cegis: timeout after {rounds} rounds; best size={size}")
            return


def run_stage_cegis(args) -> None:
    if args.cost_max is not None:
        return run_stage_cegis_cost(args)
    mask = (1 << args.bits) - 1
    stage_idx = args.stage
    if stage_idx < 0 or stage_idx >= len(HASH_STAGES):
        raise SystemExit(f"stage must be in [0,{len(HASH_STAGES)-1}]")
    random.seed(args.seed)
    if args.exhaustive and args.bits <= 8:
        tests = [i for i in range(1 << args.bits)]
    else:
        tests = [random.getrandbits(args.bits) for _ in range(args.tests)]
    target = tuple(_hash_stage(x, stage_idx, mask) for x in tests)

    if args.exhaustive and args.bits <= 8:
        ok, size, ast = _enumerate_ast(
            tests=tests,
            max_size=args.max_size,
            mask=mask,
            target=target,
            max_per_size=args.max_per_size,
            time_limit=args.time_limit,
        )
        if not ok or ast is None:
            print(f"stage_exhaustive: no expr <= {args.max_size}")
            return
        counts = _ast_counts(ast)
        engine_counts = _engine_counts(ast)
        print(f"stage_exhaustive: size={size} stage={stage_idx} ast={ast}")
        print(f"op_counts: {counts} prog_ops={size} engine_counts={engine_counts}")
        return

    start = time.time()
    rounds = 0
    while True:
        rounds += 1
        ok, size, ast = _enumerate_ast(
            tests=tests,
            max_size=args.max_size,
            mask=mask,
            target=target,
            max_per_size=args.max_per_size,
            time_limit=args.time_limit,
        )
        if not ok or ast is None:
            print(f"stage_cegis: no expr <= {args.max_size} after {rounds} rounds")
            return
        x = z3.BitVec("x", args.bits)
        cand = _ast_to_z3(ast, x, args.bits)
        target_z3 = _hash_stage_z3(x, stage_idx, args.bits)
        ok, model = _z3_equiv(cand, target_z3, args.z3_timeout_ms)
        if ok is True:
            counts = _ast_counts(ast)
            engine_counts = _engine_counts(ast)
            print(f"stage_cegis: proven size={size} rounds={rounds} stage={stage_idx} ast={ast}")
            print(f"op_counts: {counts} prog_ops={size} engine_counts={engine_counts}")
            return
        if ok is None:
            print(f"stage_cegis: z3 timeout/unknown at size={size}")
            return
        cx = model[x].as_long()
        if cx not in tests:
            tests.append(cx)
            target = tuple(_hash_stage(xv, stage_idx, mask) for xv in tests)
        if time.time() - start > args.time_limit:
            print(f"stage_cegis: timeout after {rounds} rounds; best size={size}")
            return


def run_hash_xor(args) -> None:
    mask = (1 << args.bits) - 1
    random.seed(args.seed)
    tests = [(random.getrandbits(args.bits), random.getrandbits(args.bits)) for _ in range(args.tests)]
    target = tuple(_hash(x ^ a, mask) for x, a in tests)
    ok, size = _enumerate(
        tests=tests,
        max_size=args.max_size,
        mask=mask,
        target=target,
        max_per_size=args.max_per_size,
        time_limit=args.time_limit,
        extra_ops=args.extra_ops,
    )
    print(f"hash_xor synth<={args.max_size}? {ok} found_size={size}")


# --- Genetic search (heuristic, multi-input) ---

BIN_OPS = ["+", "-", "^", "&", "|", "*"]
SHIFT_OPS = ["<<", ">>"]
TERNARY_OPS = ["madd"]


def _eval_program(
    program: list[tuple],
    pool: list[list[int]],
    mask: int,
    shift_indices: list[int] | None,
) -> list[int]:
    values = list(pool)
    for instr in program:
        op = instr[0]
        if op in BIN_OPS:
            _, a, b = instr
            va = values[a]
            vb = values[b]
            if op == "+":
                out = [(x + y) & mask for x, y in zip(va, vb)]
            elif op == "-":
                out = [(x - y) & mask for x, y in zip(va, vb)]
            elif op == "^":
                out = [(x ^ y) & mask for x, y in zip(va, vb)]
            elif op == "&":
                out = [(x & y) & mask for x, y in zip(va, vb)]
            elif op == "|":
                out = [(x | y) & mask for x, y in zip(va, vb)]
            else:
                out = [(x * y) & mask for x, y in zip(va, vb)]
        elif op in SHIFT_OPS:
            _, a, b = instr
            va = values[a]
            if shift_indices:
                shift = values[b][0] & 31
            else:
                shift = b & 31
            if op == "<<":
                out = [(x << shift) & mask for x in va]
            else:
                out = [(x >> shift) & mask for x in va]
        else:
            _, a, b, c = instr
            va = values[a]
            if b < len(values) and c < len(values):
                vb = values[b]
                vc = values[c]
                out = [((x * y + z) & mask) for x, y, z in zip(va, vb, vc)]
            else:
                mult = b
                add = c
                out = [((x * mult + add) & mask) for x in va]
        values.append(out)
    return values[-1]


def _program_to_z3(
    program: list[tuple],
    base_exprs: list[z3.BitVecRef],
    bits: int,
) -> z3.BitVecRef:
    values: list[z3.BitVecRef] = list(base_exprs)
    for instr in program:
        op = instr[0]
        if op in BIN_OPS:
            _, a, b = instr
            va = values[a]
            vb = values[b]
            if op == "+":
                out = va + vb
            elif op == "-":
                out = va - vb
            elif op == "^":
                out = va ^ vb
            elif op == "&":
                out = va & vb
            elif op == "|":
                out = va | vb
            else:
                out = va * vb
        elif op in SHIFT_OPS:
            _, a, shift = instr
            va = values[a]
            out = va << shift if op == "<<" else z3.LShR(va, shift)
        else:
            _, a, mult, add = instr
            va = values[a]
            out = va * z3.BitVecVal(mult, bits) + z3.BitVecVal(add, bits)
        values.append(out)
    return values[-1]


def _ops_to_z3(ops: list[tuple], xs: list[z3.BitVecRef], bits: int) -> z3.BitVecRef:
    x = xs[0]
    var_exprs = xs[1:]
    for op in ops:
        name = op[0]
        if name == "xorc":
            x = x ^ z3.BitVecVal(op[1], bits)
        elif name == "addc":
            x = x + z3.BitVecVal(op[1], bits)
        elif name == "xorv":
            x = x ^ var_exprs[op[1]]
        elif name == "madd":
            mult, add = op[1], op[2]
            x = x * z3.BitVecVal(mult, bits) + z3.BitVecVal(add, bits)
        elif name == "xorsr":
            shift = op[1]
            x = x ^ z3.LShR(x, shift)
        elif name == "xorsl":
            shift = op[1]
            x = x ^ (x << shift)
        elif name == "addxor_l":
            c, shift = op[1], op[2]
            tmp = x
            x = (x + z3.BitVecVal(c, bits)) ^ (tmp << shift)
        elif name == "addxor_r":
            c, shift = op[1], op[2]
            tmp = x
            x = (x + z3.BitVecVal(c, bits)) ^ z3.LShR(tmp, shift)
        else:
            raise ValueError(f"unknown op {name}")
    return x


def _collect_consts(ast: tuple, out: set[int]) -> None:
    op = ast[0]
    if op == "const":
        out.add(ast[1])
        return
    if op == "x":
        return
    if op in {"shl", "shr"}:
        _collect_consts(ast[1], out)
        return
    if op in {"+", "^", "-", "&", "|", "*"}:
        _collect_consts(ast[1], out)
        _collect_consts(ast[2], out)
        return
    if op == "madd":
        _collect_consts(ast[1], out)
        return


def _ast_to_program(ast: tuple, input_count: int) -> tuple[list[tuple], list[int]]:
    consts_set: set[int] = set()
    _collect_consts(ast, consts_set)
    consts = sorted(consts_set)
    const_index = {c: input_count + i for i, c in enumerate(consts)}
    program: list[tuple] = []
    memo: dict[int, int] = {}
    base_count = input_count + len(consts)

    def emit(node: tuple) -> int:
        key = id(node)
        if key in memo:
            return memo[key]
        op = node[0]
        if op == "x":
            idx = node[1] if len(node) > 1 else 0
            memo[key] = idx
            return idx
        if op == "const":
            idx = const_index[node[1]]
            memo[key] = idx
            return idx
        if op in {"shl", "shr"}:
            a = emit(node[1])
            idx = base_count + len(program)
            memo[key] = idx
            program.append((op.replace("shl", "<<").replace("shr", ">>"), a, node[2]))
            return idx
        if op in {"+", "^", "-", "&", "|", "*"}:
            a = emit(node[1])
            b = emit(node[2])
            idx = base_count + len(program)
            memo[key] = idx
            program.append((op, a, b))
            return idx
        if op == "madd":
            a = emit(node[1])
            idx = base_count + len(program)
            memo[key] = idx
            program.append(("madd", a, node[2], node[3]))
            return idx
        raise ValueError(f"unknown ast op {op}")

    emit(ast)
    return program, consts


def _baseline_hash2_program() -> tuple[list[tuple], list[int]]:
    ast = _baseline_hash2_ast()
    return _ast_to_program(ast, input_count=3)


def _reconstruct_program(
    parents: list[tuple | None],
    base_count: int,
    target_idx: int,
) -> list[tuple]:
    # Build a minimal program (instruction list) for target_idx.
    program: list[tuple] = []
    mapping: dict[int, int] = {i: i for i in range(base_count)}

    def emit(idx: int) -> None:
        if idx < base_count or idx in mapping:
            return
        parent = parents[idx]
        if parent is None:
            return
        op = parent[0]
        if op in {"<<", ">>"}:
            _, a, s = parent
            emit(a)
            new_idx = base_count + len(program)
            mapping[idx] = new_idx
            program.append((op, mapping[a], s))
        elif op == "madd":
            _, a, mult, add = parent
            emit(a)
            new_idx = base_count + len(program)
            mapping[idx] = new_idx
            program.append(("madd", mapping[a], mult, add))
        else:
            _, a, b = parent
            emit(a)
            emit(b)
            new_idx = base_count + len(program)
            mapping[idx] = new_idx
            program.append((op, mapping[a], mapping[b]))

    emit(target_idx)
    return program


def _enumerate_program_cost(
    tests: list[int] | list[tuple[int, ...]],
    cost_max: int,
    eval_bits: int,
    out_mask_bits: int | None,
    target: tuple[int, ...],
    max_states: int,
    time_limit: float,
    extra_ops: bool = False,
    program_k: int = 32,
    mode: str = "beam",
) -> tuple[bool, int | None, list[tuple] | None, dict]:
    start = time.time()
    eval_mask = (1 << eval_bits) - 1
    out_mask = (1 << out_mask_bits) - 1 if out_mask_bits else eval_mask

    consts, shifts, muladds = _build_ops_sets(eval_mask)
    base_vals: list[tuple[int, ...]] = []
    if tests and isinstance(tests[0], tuple):
        arity = len(tests[0])
        for i in range(arity):
            base_vals.append(tuple(t[i] & out_mask for t in tests))
    else:
        base_vals.append(tuple(t & out_mask for t in tests))
    for c in consts:
        base_vals.append(tuple([c & out_mask] * len(tests)))

    target_score = len(target)
    score_cache: dict[tuple[int, ...], int] = {}

    def score(vec: tuple[int, ...]) -> int:
        if vec in score_cache:
            return score_cache[vec]
        s = sum(1 for v, t in zip(vec, target) if v == t)
        score_cache[vec] = s
        return s

    class State:
        __slots__ = ("vals", "valset", "hashes", "prog", "score")

        def __init__(self, vals, valset, hashes, prog, score_val) -> None:
            self.vals = vals
            self.valset = valset
            self.hashes = hashes
            self.prog = prog
            self.score = score_val

    base_set = set(base_vals)
    base_hashes = frozenset(hash(v) for v in base_vals)
    base_score = max((score(v) for v in base_vals), default=0)
    states = [State(base_vals, base_set, base_hashes, [], base_score)]
    seen_sigs = {base_hashes: 0}

    bin_ops = ["+", "^"] + (["-", "&", "|", "*"] if extra_ops else [])
    commutative = {"+", "^", "&", "|", "*"}

    if mode == "dp":
        # DP over value signatures: keep all distinct values up to cost_max.
        values = list(base_vals)
        parents: list[tuple | None] = [None for _ in values]
        costs = [0 for _ in values]
        seen_vals = {v: i for i, v in enumerate(values)}
        base_count = len(base_vals)

        def add_value(vec: tuple[int, ...], parent: tuple, cost: int) -> int | None:
            if vec in seen_vals:
                return None
            idx = len(values)
            values.append(vec)
            parents.append(parent)
            costs.append(cost)
            seen_vals[vec] = idx
            return idx

        for cost in range(1, cost_max + 1):
            if time.time() - start > time_limit:
                return False, None, None, {}
            # Candidate indices are all values with cost <= cost-1.
            cand_idx = [i for i, c in enumerate(costs) if c <= cost - 1]
            for i in cand_idx:
                v = values[i]
                for s in shifts:
                    if time.time() - start > time_limit:
                        return False, None, None, {}
                    new_vec = tuple(((x << s) & eval_mask) & out_mask for x in v)
                    idx = add_value(new_vec, ("<<", i, s), cost)
                    if new_vec == target and idx is not None:
                        return True, cost, _reconstruct_program(parents, base_count, idx), {"consts": consts}
                for s in shifts:
                    if time.time() - start > time_limit:
                        return False, None, None, {}
                    new_vec = tuple(((x >> s) & eval_mask) & out_mask for x in v)
                    idx = add_value(new_vec, (">>", i, s), cost)
                    if new_vec == target and idx is not None:
                        return True, cost, _reconstruct_program(parents, base_count, idx), {"consts": consts}
                for mult, add in muladds:
                    if time.time() - start > time_limit:
                        return False, None, None, {}
                    new_vec = tuple(((x * mult + add) & eval_mask) & out_mask for x in v)
                    idx = add_value(new_vec, ("madd", i, mult, add), cost)
                    if new_vec == target and idx is not None:
                        return True, cost, _reconstruct_program(parents, base_count, idx), {"consts": consts}
            for ai, i in enumerate(cand_idx):
                va = values[i]
                for j in cand_idx[ai:] if any(op in commutative for op in bin_ops) else cand_idx:
                    vb = values[j]
                    for op in bin_ops:
                        if op in commutative and j < i:
                            continue
                        if time.time() - start > time_limit:
                            return False, None, None, {}
                        if op == "+":
                            new_vec = tuple(((a + b) & eval_mask) & out_mask for a, b in zip(va, vb))
                        elif op == "^":
                            new_vec = tuple(((a ^ b) & eval_mask) & out_mask for a, b in zip(va, vb))
                        elif op == "-":
                            new_vec = tuple(((a - b) & eval_mask) & out_mask for a, b in zip(va, vb))
                        elif op == "&":
                            new_vec = tuple(((a & b) & eval_mask) & out_mask for a, b in zip(va, vb))
                        elif op == "|":
                            new_vec = tuple(((a | b) & eval_mask) & out_mask for a, b in zip(va, vb))
                        else:
                            new_vec = tuple(((a * b) & eval_mask) & out_mask for a, b in zip(va, vb))
                        idx = add_value(new_vec, (op, i, j), cost)
                        if new_vec == target and idx is not None:
                            return True, cost, _reconstruct_program(parents, base_count, idx), {"consts": consts}
            if max_states and len(values) > max_states:
                return False, None, None, {"warning": f"state cap {max_states} exceeded"}
        return False, None, None, {}

    for cost in range(1, cost_max + 1):
        if time.time() - start > time_limit:
            return False, None, None, {}
        next_states: list[State] = []
        for st in states:
            if target in st.valset:
                return True, cost - 1, st.prog, {"consts": consts}
            vals = st.vals
            # Choose candidate indices: always include base inputs/consts + top scoring values + recent values.
            base_count = len(base_vals)
            scored = sorted(range(len(vals)), key=lambda i: score(vals[i]), reverse=True)
            recent = list(range(max(0, len(vals) - program_k), len(vals)))
            cand_idx = list(dict.fromkeys(list(range(base_count)) + scored[:program_k] + recent))

            # Unary shifts and madd
            for i in cand_idx:
                v = vals[i]
                for s in shifts:
                    if time.time() - start > time_limit:
                        return False, None, None, {}
                    new_vec = tuple(((x << s) & eval_mask) & out_mask for x in v)
                    if new_vec in st.valset:
                        continue
                    new_vals = vals + [new_vec]
                    new_set = st.valset | {new_vec}
                    new_hashes = st.hashes | {hash(new_vec)}
                    if new_hashes in seen_sigs and seen_sigs[new_hashes] <= cost:
                        continue
                    seen_sigs[new_hashes] = cost
                    new_prog = st.prog + [("<<", i, s)]
                    next_states.append(State(new_vals, new_set, new_hashes, new_prog, max(st.score, score(new_vec))))
                    if new_vec == target:
                        return True, cost, new_prog, {"consts": consts}
                for s in shifts:
                    if time.time() - start > time_limit:
                        return False, None, None, {}
                    new_vec = tuple(((x >> s) & eval_mask) & out_mask for x in v)
                    if new_vec in st.valset:
                        continue
                    new_vals = vals + [new_vec]
                    new_set = st.valset | {new_vec}
                    new_hashes = st.hashes | {hash(new_vec)}
                    if new_hashes in seen_sigs and seen_sigs[new_hashes] <= cost:
                        continue
                    seen_sigs[new_hashes] = cost
                    new_prog = st.prog + [(">>", i, s)]
                    next_states.append(State(new_vals, new_set, new_hashes, new_prog, max(st.score, score(new_vec))))
                    if new_vec == target:
                        return True, cost, new_prog, {"consts": consts}
                for mult, add in muladds:
                    if time.time() - start > time_limit:
                        return False, None, None, {}
                    new_vec = tuple(((x * mult + add) & eval_mask) & out_mask for x in v)
                    if new_vec in st.valset:
                        continue
                    new_vals = vals + [new_vec]
                    new_set = st.valset | {new_vec}
                    new_hashes = st.hashes | {hash(new_vec)}
                    if new_hashes in seen_sigs and seen_sigs[new_hashes] <= cost:
                        continue
                    seen_sigs[new_hashes] = cost
                    new_prog = st.prog + [("madd", i, mult, add)]
                    next_states.append(State(new_vals, new_set, new_hashes, new_prog, max(st.score, score(new_vec))))
                    if new_vec == target:
                        return True, cost, new_prog, {"consts": consts}

            # Binary ops
            for ai, i in enumerate(cand_idx):
                va = vals[i]
                for j in cand_idx[ai:] if any(op in commutative for op in bin_ops) else cand_idx:
                    vb = vals[j]
                    for op in bin_ops:
                        if op in commutative and j < i:
                            continue
                        if time.time() - start > time_limit:
                            return False, None, None, {}
                        if op == "+":
                            new_vec = tuple(((a + b) & eval_mask) & out_mask for a, b in zip(va, vb))
                        elif op == "^":
                            new_vec = tuple(((a ^ b) & eval_mask) & out_mask for a, b in zip(va, vb))
                        elif op == "-":
                            new_vec = tuple(((a - b) & eval_mask) & out_mask for a, b in zip(va, vb))
                        elif op == "&":
                            new_vec = tuple(((a & b) & eval_mask) & out_mask for a, b in zip(va, vb))
                        elif op == "|":
                            new_vec = tuple(((a | b) & eval_mask) & out_mask for a, b in zip(va, vb))
                        else:
                            new_vec = tuple(((a * b) & eval_mask) & out_mask for a, b in zip(va, vb))
                        if new_vec in st.valset:
                            continue
                        new_vals = vals + [new_vec]
                        new_set = st.valset | {new_vec}
                        new_hashes = st.hashes | {hash(new_vec)}
                        if new_hashes in seen_sigs and seen_sigs[new_hashes] <= cost:
                            continue
                        seen_sigs[new_hashes] = cost
                        new_prog = st.prog + [(op, i, j)]
                        next_states.append(State(new_vals, new_set, new_hashes, new_prog, max(st.score, score(new_vec))))
                        if new_vec == target:
                            return True, cost, new_prog, {"consts": consts}

        if not next_states:
            return False, None, None, {}
        next_states.sort(key=lambda s: (s.score, len(s.vals)), reverse=True)
        states = next_states[:max_states]

    return False, None, None, {}


def _mitm_enumerate(
    tests: list[int] | list[tuple[int, ...]],
    cost_max: int,
    eval_bits: int,
    out_mask_bits: int | None,
    target: tuple[int, ...],
    time_limit: float,
    extra_ops: bool = False,
    restrict_ops: bool = False,
    cost_split: int | None = None,
    fast: bool = False,
    xorv_exact: int | None = None,
    xorv_each: bool = False,
) -> tuple[bool, int | None, list[tuple] | None, dict]:
    start = time.time()
    eval_mask = (1 << eval_bits) - 1
    out_mask = (1 << out_mask_bits) - 1 if out_mask_bits else eval_mask
    consts, shifts, muladds = _build_ops_sets(eval_mask)
    if not tests or not isinstance(tests[0], tuple):
        raise SystemExit("mitm requires multi-input tests (x,a,b,...)")
    arity = len(tests[0])
    x_vec = tuple(t[0] & out_mask for t in tests)
    var_vecs = [tuple(t[i] & out_mask for t in tests) for i in range(1, arity)]
    if xorv_each and xorv_exact is None:
        xorv_exact = len(var_vecs)
    if xorv_each and xorv_exact != len(var_vecs):
        raise SystemExit("mitm xorv_each requires xorv_exact == number of variable inputs")

    # Reversible op set
    ops: list[tuple] = []
    xor_shifts_r = [val3 for op1, _v1, op2, op3, val3 in HASH_STAGES if op2 == "^" and op3 == ">>"]
    xor_shifts_l = [val3 for op1, _v1, op2, op3, val3 in HASH_STAGES if op2 == "^" and op3 == "<<"]
    addxor_l = [(val1 & eval_mask, val3) for op1, val1, op2, op3, val3 in HASH_STAGES if op1 == "+" and op2 == "^" and op3 == "<<"]
    addxor_r = [(val1 & eval_mask, val3) for op1, val1, op2, op3, val3 in HASH_STAGES if op1 == "+" and op2 == "^" and op3 == ">>"]
    consts_use = consts
    if restrict_ops:
        consts_use = sorted({val1 & eval_mask for _op1, val1, _op2, _op3, _val3 in HASH_STAGES})
    for c in consts_use:
        ops.append(("xorc", c, 1))
    for mult, add in muladds:
        ops.append(("madd", mult, add, 1))
    for s in xor_shifts_r:
        ops.append(("xorsr", s, 2))
    if not restrict_ops:
        for s in xor_shifts_l:
            ops.append(("xorsl", s, 2))
    for c, s in addxor_l:
        ops.append(("addxor_l", c, s, 3))
    for c, s in addxor_r:
        ops.append(("addxor_r", c, s, 3))
    for i in range(len(var_vecs)):
        ops.append(("xorv", i, 1))

    use_counts = xorv_exact is not None
    if use_counts:
        count_dim = len(var_vecs) if xorv_each else 1
        req_counts = tuple([1] * count_dim) if xorv_each else (xorv_exact,)
        zero_counts = tuple([0] * count_dim)

    def unxorshift_r(val: int, shift: int) -> int:
        x = val & eval_mask
        i = shift
        while i < eval_bits:
            x ^= (x >> i)
            i *= 2
        return x & eval_mask

    def unxorshift_l(val: int, shift: int) -> int:
        x = val & eval_mask
        i = shift
        while i < eval_bits:
            x ^= (x << i) & eval_mask
            i *= 2
        return x & eval_mask

    inv_cache: dict[int, int] = {}

    def inv_mult(mult: int) -> int:
        if mult not in inv_cache:
            inv_cache[mult] = pow(mult, -1, 1 << eval_bits)
        return inv_cache[mult]

    def apply_op(op: tuple, vec: tuple[int, ...]) -> tuple[int, ...]:
        name = op[0]
        if name == "xorc":
            c = op[1]
            return tuple(((v ^ c) & eval_mask) & out_mask for v in vec)
        if name == "xorv":
            vv = var_vecs[op[1]]
            return tuple(((v ^ w) & eval_mask) & out_mask for v, w in zip(vec, vv))
        if name == "madd":
            mult, add = op[1], op[2]
            return tuple(((v * mult + add) & eval_mask) & out_mask for v in vec)
        if name == "xorsr":
            shift = op[1]
            return tuple(((v ^ (v >> shift)) & eval_mask) & out_mask for v in vec)
        if name == "xorsl":
            shift = op[1]
            return tuple(((v ^ ((v << shift) & eval_mask)) & eval_mask) & out_mask for v in vec)
        if name == "addxor_l":
            c, shift = op[1], op[2]
            out = []
            for v in vec:
                tmp = v
                out.append((((v + c) & eval_mask) ^ ((tmp << shift) & eval_mask)) & out_mask)
            return tuple(out)
        if name == "addxor_r":
            c, shift = op[1], op[2]
            out = []
            for v in vec:
                tmp = v
                out.append((((v + c) & eval_mask) ^ (tmp >> shift)) & out_mask)
            return tuple(out)
        raise ValueError(f"unknown op {name}")

    def invert_op(op: tuple, vec: tuple[int, ...]) -> tuple[int, ...]:
        name = op[0]
        if name == "xorc":
            c = op[1]
            return tuple(((v ^ c) & eval_mask) & out_mask for v in vec)
        if name == "xorv":
            vv = var_vecs[op[1]]
            return tuple(((v ^ w) & eval_mask) & out_mask for v, w in zip(vec, vv))
        if name == "madd":
            mult, add = op[1], op[2]
            inv = inv_mult(mult)
            return tuple((((v - add) * inv) & eval_mask) & out_mask for v in vec)
        if name == "xorsr":
            shift = op[1]
            return tuple(unxorshift_r(v, shift) & out_mask for v in vec)
        if name == "xorsl":
            shift = op[1]
            return tuple(unxorshift_l(v, shift) & out_mask for v in vec)
        if name == "addxor_l":
            c, shift = op[1], op[2]
            out = []
            for v in vec:
                y = v & eval_mask
                x = 0
                carry = 0
                for i in range(eval_bits):
                    c_i = (c >> i) & 1
                    y_i = (y >> i) & 1
                    x_k = (x >> (i - shift)) & 1 if i >= shift else 0
                    x_i = y_i ^ x_k ^ c_i ^ carry
                    x |= (x_i << i)
                    carry = (x_i & c_i) | (x_i & carry) | (c_i & carry)
                out.append(x & out_mask)
            return tuple(out)
        if name == "addxor_r":
            c, shift = op[1], op[2]
            out = []
            for v in vec:
                y = v & eval_mask
                x = 0
                carry = 0
                for i in range(eval_bits):
                    c_i = (c >> i) & 1
                    y_i = (y >> i) & 1
                    x_k = (x >> (i + shift)) & 1 if i + shift < eval_bits else 0
                    x_i = y_i ^ x_k ^ c_i ^ carry
                    x |= (x_i << i)
                    carry = (x_i & c_i) | (x_i & carry) | (c_i & carry)
                out.append(x & out_mask)
            return tuple(out)
        raise ValueError(f"unknown op {name}")

    def expand(
        frontier: dict[tuple, list[tuple]] | dict[tuple, int],
        cost_limit: int,
        direction: str,
    ) -> tuple[dict[tuple, list[tuple]] | dict[tuple, int], bool]:
        if fast:
            layers: dict[int, dict[tuple, int]] = {0: frontier}  # type: ignore[assignment]
            best_cost: dict[tuple, int] = {list(frontier.keys())[0]: 0}  # type: ignore[arg-type]
        else:
            layers = {0: frontier}  # type: ignore[assignment]
            best_cost: dict[tuple, int] = {list(frontier.keys())[0]: 0}  # type: ignore[arg-type]
        for cost in range(cost_limit + 1):
            if time.time() - start > time_limit:
                result: dict = {}
                for layer in layers.values():
                    result.update(layer)
                return result, True
            for key, seq in layers.get(cost, {}).items():  # type: ignore[union-attr]
                if use_counts:
                    vec, counts = key
                else:
                    vec, counts = key, None
                for op in ops:
                    if time.time() - start > time_limit:
                        result: dict = {}
                        for layer in layers.values():
                            result.update(layer)
                        return result, True
                    oc = op[-1]
                    new_cost = cost + oc
                    if new_cost > cost_limit:
                        continue
                    new_vec = invert_op(op, vec) if direction == "backward" else apply_op(op, vec)
                    if use_counts:
                        if counts is None:
                            counts = zero_counts
                        if op[0] == "xorv":
                            if xorv_each:
                                idx = op[1]
                                if counts[idx] >= 1:
                                    continue
                                next_counts = list(counts)
                                next_counts[idx] += 1
                                new_counts = tuple(next_counts)
                            else:
                                if counts[0] >= xorv_exact:
                                    continue
                                new_counts = (counts[0] + 1,)
                        else:
                            new_counts = counts
                        new_key = (new_vec, new_counts)
                    else:
                        new_key = new_vec
                    if new_key in best_cost and best_cost[new_key] <= new_cost:
                        continue
                    best_cost[new_key] = new_cost
                    if fast:
                        layers.setdefault(new_cost, {})[new_key] = new_cost  # type: ignore[index]
                    else:
                        layers.setdefault(new_cost, {})[new_key] = (seq + [op])  # type: ignore[index]
        result: dict = {}
        for layer in layers.values():
            result.update(layer)
        return result, False

    if cost_split is None:
        left = cost_max
        right = cost_max
    else:
        left = max(0, min(cost_max, cost_split))
        right = max(0, cost_max - left)
    f_key = (x_vec, zero_counts) if use_counts else x_vec
    forward, f_timeout = expand({f_key: []} if not fast else {f_key: 0}, left, "forward")
    if f_timeout:
        return False, None, None, {"mode": "mitm", "timeout": True}
    b_key = (target, zero_counts) if use_counts else target
    backward, b_timeout = expand({b_key: []} if not fast else {b_key: 0}, right, "backward")
    if b_timeout:
        return False, None, None, {"mode": "mitm", "timeout": True}

    best = None
    if fast:
        for vec, cost_f in forward.items():  # type: ignore[union-attr]
            if use_counts:
                vec_key = vec[0]
                counts_f = vec[1]
                want = tuple(rc - cf for rc, cf in zip(req_counts, counts_f))
                if any(v < 0 for v in want):
                    continue
                other_key = (vec_key, want)
                if other_key not in backward:
                    continue
                cost_b = backward[other_key]  # type: ignore[index]
            else:
                if vec not in backward:
                    continue
                cost_b = backward[vec]  # type: ignore[index]
            total_cost = cost_f + cost_b
            if total_cost > cost_max:
                continue
            if best is None or total_cost < best[0]:
                best = (total_cost, [])
        if best:
            return True, best[0], None, {"mode": "mitm", "consts": consts, "var_count": len(var_vecs), "fast": True}
    else:
        for vec, seq_f in forward.items():  # type: ignore[union-attr]
            if use_counts:
                vec_key = vec[0]
                counts_f = vec[1]
                want = tuple(rc - cf for rc, cf in zip(req_counts, counts_f))
                if any(v < 0 for v in want):
                    continue
                other_key = (vec_key, want)
                if other_key not in backward:
                    continue
                seq_b = backward[other_key]  # type: ignore[index]
            else:
                if vec not in backward:
                    continue
                seq_b = backward[vec]  # type: ignore[index]
            total_cost = sum(op[-1] for op in seq_f) + sum(op[-1] for op in seq_b)
            if total_cost > cost_max:
                continue
            if best is None or total_cost < best[0]:
                ops_fwd = seq_f + list(reversed(seq_b))
                best = (total_cost, ops_fwd)
        if best:
            return True, best[0], best[1], {"mode": "mitm", "consts": consts, "var_count": len(var_vecs)}
    return False, None, None, {"mode": "mitm", "consts": consts, "var_count": len(var_vecs)}


def _random_program(
    length: int,
    input_count: int,
    const_count: int,
    shift_indices: list[int],
    seed: int,
) -> list[tuple]:
    random.seed(seed)
    program: list[tuple] = []
    total = input_count + const_count
    for _ in range(length):
        op_choice = random.choice(BIN_OPS + SHIFT_OPS + TERNARY_OPS)
        if op_choice in BIN_OPS:
            a = random.randrange(total)
            b = random.randrange(total)
            program.append((op_choice, a, b))
        elif op_choice in SHIFT_OPS:
            a = random.randrange(total)
            b = random.choice(shift_indices)
            program.append((op_choice, a, b))
        else:
            a = random.randrange(total)
            b = random.randrange(total)
            c = random.randrange(total)
            program.append((op_choice, a, b, c))
        total += 1
    return program


def _mutate_program(
    program: list[tuple],
    input_count: int,
    const_count: int,
    shift_indices: list[int],
    rate: float,
) -> list[tuple]:
    out = [list(instr) for instr in program]
    total = input_count + const_count
    for i, instr in enumerate(out):
        total_idx = total + i
        if random.random() > rate:
            continue
        op = instr[0]
        # mutate op with small probability
        if random.random() < 0.2:
            op = random.choice(BIN_OPS + SHIFT_OPS + TERNARY_OPS)
            instr = [op]
        if op in BIN_OPS:
            a = random.randrange(total_idx)
            b = random.randrange(total_idx)
            instr = [op, a, b]
        elif op in SHIFT_OPS:
            a = random.randrange(total_idx)
            b = random.choice(shift_indices)
            instr = [op, a, b]
        else:
            a = random.randrange(total_idx)
            b = random.randrange(total_idx)
            c = random.randrange(total_idx)
            instr = [op, a, b, c]
        out[i] = instr
    return [tuple(instr) for instr in out]


def run_genetic(args) -> None:
    mask = (1 << args.bits) - 1
    random.seed(args.seed)
    tests = [
        (random.getrandbits(args.bits), random.getrandbits(args.bits), random.getrandbits(args.bits))
        for _ in range(args.tests)
    ]

    xs = [t[0] for t in tests]
    as_ = [t[1] for t in tests]
    bs = [t[2] for t in tests]

    if args.target == "fullhash":
        target = [_hash(x, mask) for x in xs]
        inputs = [xs]
    elif args.target == "hash_xor":
        target = [_hash(x ^ a, mask) for x, a in zip(xs, as_)]
        inputs = [xs, as_]
    else:
        target = [_hash2(x, a, b, mask) for x, a, b in zip(xs, as_, bs)]
        inputs = [xs, as_, bs]

    consts, shifts, _ = _build_ops_sets(mask)
    consts = list(consts)
    shift_consts = list(shifts)

    const_arrays = [[c] * len(xs) for c in consts]
    shift_arrays = [[s] * len(xs) for s in shift_consts]
    pool = inputs + const_arrays + shift_arrays

    input_count = len(inputs)
    const_count = len(const_arrays) + len(shift_arrays)
    shift_indices = list(range(input_count + len(const_arrays), input_count + const_count))

    pop = []
    for i in range(args.pop):
        prog = _random_program(args.length, input_count, const_count, shift_indices, args.seed + i)
        pop.append(prog)

    best_score = -1
    best_prog = None

    start = time.time()
    for gen in range(args.iters):
        scored = []
        for prog in pop:
            out = _eval_program(prog, pool, mask, shift_indices)
            score = sum(1 for y, t in zip(out, target) if y == t)
            scored.append((score, prog))
        scored.sort(key=lambda x: x[0], reverse=True)
        if scored[0][0] > best_score:
            best_score = scored[0][0]
            best_prog = scored[0][1]
        if best_score == len(target):
            break
        elite = [p for _, p in scored[: args.elite]]
        new_pop = list(elite)
        while len(new_pop) < args.pop:
            parent = random.choice(elite)
            child = _mutate_program(parent, input_count, const_count, shift_indices, args.mutate)
            new_pop.append(child)
        pop = new_pop
        if time.time() - start > args.time_limit:
            break

    print(
        f"genetic target={args.target} best={best_score}/{len(target)} length={args.length} gens={gen+1}"
    )


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--mode",
        choices=[
            "window2",
            "window3",
            "fullhash",
            "fullhash_cegis",
            "compose2",
            "compose2_full",
            "compose2_cegis",
            "hash_xor",
            "stage_cegis",
            "genetic",
            "cegis",
            "prove_baseline",
        ],
        required=True,
    )
    parser.add_argument("--bits", type=int, default=24)
    parser.add_argument("--tests", type=int, default=32)
    parser.add_argument("--max-size", type=int, default=11)
    parser.add_argument("--cost-max", type=int, default=None, help="Use cost-bounded enumeration (VALU cost cap).")
    parser.add_argument("--cost-min", type=int, default=None, help="Optional cost sweep start (cost-bounded modes).")
    parser.add_argument("--cost-step", type=int, default=1, help="Cost sweep step (cost-bounded modes).")
    parser.add_argument("--eval-bits", type=int, default=None, help="Internal eval width for cost-bounded modes.")
    parser.add_argument("--test-mask-bits", type=int, default=None, help="Mask output to this width for tests.")
    parser.add_argument("--max-per-size", type=int, default=8000)
    parser.add_argument("--time-limit", type=float, default=8.0)
    parser.add_argument("--seed", type=int, default=0)
    parser.add_argument("--window", type=int, default=2)
    parser.add_argument("--extra-ops", action="store_true", help="Include -, &, |, * in binary ops.")
    parser.add_argument("--emit-ast", action="store_true", help="Emit AST for small-bit solutions.")
    parser.add_argument("--target", choices=["fullhash", "hash_xor", "compose2"], default="fullhash")
    parser.add_argument("--length", type=int, default=12)
    parser.add_argument("--pop", type=int, default=64)
    parser.add_argument("--iters", type=int, default=200)
    parser.add_argument("--elite", type=int, default=8)
    parser.add_argument("--mutate", type=float, default=0.2)
    parser.add_argument("--stage", type=int, default=0, help="Stage index for stage_cegis")
    parser.add_argument("--exhaustive", action="store_true", help="Use full input domain for bits<=8 (stage/fullhash).")
    parser.add_argument("--report-baseline", action="store_true", help="Print baseline op counts and exit.")
    parser.add_argument("--baseline-cost", type=int, default=12, help="Cost target for prove_baseline.")
    parser.add_argument("--baseline-only", action="store_true", help="Only prove baseline AST, skip synthesis.")
    parser.add_argument("--baseline-full-proof", action="store_true", help="Attempt full-hash Z3 proof (may be slow).")
    parser.add_argument("--z3-timeout-ms", type=int, default=5000, help="Z3 timeout in milliseconds.")
    parser.add_argument("--enumerator", choices=["expr", "program"], default="expr", help="Expression or SSA program enumerator.")
    parser.add_argument("--program-k", type=int, default=32, help="Candidate operand pool size for program enumerator.")
    parser.add_argument("--program-mode", choices=["beam", "dp", "mitm"], default="beam", help="Program enumerator strategy.")
    parser.add_argument("--baseline-hash2-check", action="store_true", help="Check baseline hash2 program cost/feasibility.")
    parser.add_argument("--mitm-restrict", action="store_true", help="Restrict MITM ops to stage constants and right shifts only.")
    parser.add_argument("--mitm-cost-split", type=int, default=None, help="Optional MITM cost split (left side).")
    parser.add_argument("--mitm-splits", type=str, default=None, help="Comma-separated MITM cost splits to try (left side).")
    parser.add_argument("--mitm-fast", action="store_true", help="MITM: store only cost per signature (no program).")
    parser.add_argument("--mitm-xorv-exact", type=int, default=None, help="MITM: require exact number of xorv ops across the program.")
    parser.add_argument("--mitm-xorv-each", action="store_true", help="MITM: require each xorv input used exactly once (implies exact==arity-1).")
    parser.add_argument("--mitm-tests", type=int, default=None, help="Use fewer tests for MITM (CEGIS will still append counterexamples).")
    parser.add_argument("--size-min", type=int, default=None, help="Optional sweep start (compose2_cegis only)")
    parser.add_argument("--size-max", type=int, default=None, help="Optional sweep end (compose2_cegis only)")
    parser.add_argument("--size-step", type=int, default=2, help="Optional sweep step (compose2_cegis only)")
    args = parser.parse_args()

    if args.report_baseline:
        baseline_report()
        return

    if args.mode == "window2":
        args.window = 2
        run_window_search(args)
    elif args.mode == "window3":
        args.window = 3
        run_window_search(args)
    elif args.mode == "fullhash":
        run_fullhash(args)
    elif args.mode == "fullhash_cegis":
        run_fullhash_cegis(args)
    elif args.mode == "hash_xor":
        run_hash_xor(args)
    elif args.mode == "compose2_full":
        run_compose2_full(args)
    elif args.mode == "compose2_cegis":
        run_compose2_cegis(args)
    elif args.mode == "stage_cegis":
        run_stage_cegis(args)
    elif args.mode == "genetic":
        run_genetic(args)
    elif args.mode == "cegis":
        run_cegis(args)
    elif args.mode == "prove_baseline":
        run_prove_baseline(args)
    else:
        run_compose2(args)


if __name__ == "__main__":
    main()
