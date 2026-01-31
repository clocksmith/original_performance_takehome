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

HASH_STAGES = [
    ("+", 0x7ED55D16, "+", "<<", 12),
    ("^", 0xC761C23C, "^", ">>", 19),
    ("+", 0x165667B1, "+", "<<", 5),
    ("+", 0xD3A2646C, "^", "<<", 9),
    ("+", 0xFD7046C5, "+", "<<", 3),
    ("^", 0xB55A4F09, "^", ">>", 16),
]


@dataclass(frozen=True)
class Expr:
    size: int
    vals: tuple[int, ...]


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
    shift_indices: list[int],
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
            shift = values[b][0] & 31
            if op == "<<":
                out = [(x << shift) & mask for x in va]
            else:
                out = [(x >> shift) & mask for x in va]
        else:
            _, a, b, c = instr
            va = values[a]
            vb = values[b]
            vc = values[c]
            out = [((x * y + z) & mask) for x, y, z in zip(va, vb, vc)]
        values.append(out)
    return values[-1]


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
        choices=["window2", "window3", "fullhash", "compose2", "hash_xor", "genetic"],
        required=True,
    )
    parser.add_argument("--bits", type=int, default=24)
    parser.add_argument("--tests", type=int, default=32)
    parser.add_argument("--max-size", type=int, default=11)
    parser.add_argument("--max-per-size", type=int, default=8000)
    parser.add_argument("--time-limit", type=float, default=8.0)
    parser.add_argument("--seed", type=int, default=0)
    parser.add_argument("--window", type=int, default=2)
    parser.add_argument("--extra-ops", action="store_true", help="Include -, &, |, * in binary ops.")
    parser.add_argument("--target", choices=["fullhash", "hash_xor", "compose2"], default="fullhash")
    parser.add_argument("--length", type=int, default=12)
    parser.add_argument("--pop", type=int, default=64)
    parser.add_argument("--iters", type=int, default=200)
    parser.add_argument("--elite", type=int, default=8)
    parser.add_argument("--mutate", type=float, default=0.2)
    args = parser.parse_args()

    if args.mode == "window2":
        args.window = 2
        run_window_search(args)
    elif args.mode == "window3":
        args.window = 3
        run_window_search(args)
    elif args.mode == "fullhash":
        run_fullhash(args)
    elif args.mode == "hash_xor":
        run_hash_xor(args)
    elif args.mode == "genetic":
        run_genetic(args)
    else:
        run_compose2(args)


if __name__ == "__main__":
    main()
