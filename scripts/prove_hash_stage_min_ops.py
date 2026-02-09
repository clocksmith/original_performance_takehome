from __future__ import annotations

"""
Attempt to *disprove* the existence of a <=2-op implementation for individual
`myhash` stages under a generous ALU/VALU-like opset using Z3.

This is a sanity check for "can we fuse stages" arguments:
  - If a stage can be implemented in 2 ops, then (in principle) the hash could
    be reduced from 12 -> 11 ops/round (and the cycle floor changes).
  - If Z3 shows UNSAT for <=2 ops (for a given opset), then that stage requires
    >=3 ops in that opset.

Notes:
  - This is *not* a proof that the full 6-stage hash can't be globally fused
    into fewer total ops; it only rules out the most direct win (2-op stages).
  - Run with the repo venv so `z3-solver` is importable:
      ./.venv/bin/python scripts/prove_hash_stage_min_ops.py
"""

import argparse
import random
from dataclasses import dataclass
from typing import Callable, Iterable

import z3

MASK32 = (1 << 32) - 1


def _u32(x: int) -> int:
    return x & MASK32


def _bv32(x: int) -> z3.BitVecNumRef:
    return z3.BitVecVal(_u32(x), 32)


def _sel(values: list[z3.BitVecRef], idx: z3.IntNumRef | z3.ArithRef) -> z3.BitVecRef:
    """
    Select `values[idx]` for small idx using nested Ifs.

    Using Int selectors keeps the encoding simple.
    """
    assert values
    out: z3.BitVecRef = values[-1]
    for i in range(len(values) - 2, -1, -1):
        out = z3.If(idx == i, values[i], out)
    return out


def _apply_binop(op: str, a: z3.BitVecRef, b: z3.BitVecRef) -> z3.BitVecRef:
    if op == "+":
        return a + b
    if op == "-":
        return a - b
    if op == "^":
        return a ^ b
    if op == "&":
        return a & b
    if op == "|":
        return a | b
    if op == "*":
        return a * b
    if op == "<<":
        return a << b
    if op == ">>":
        return z3.LShR(a, b)
    raise ValueError(f"unknown op: {op!r}")


BINOPS = ["+", "-", "^", "&", "|", "*", "<<", ">>"]
OP_MULADD = "muladd"


@dataclass(frozen=True)
class Stage:
    name: str
    target: Callable[[z3.BitVecRef], z3.BitVecRef]


def _stage_by_name(name: str) -> Stage:
    # HASH_STAGES (1-indexed):
    # 1: a = (a + C1) + (a << 12)
    # 2: a = (a ^ C2) ^ (a >> 19)
    # 3: a = (a + C3) + (a << 5)
    # 4: a = (a + C4) ^ (a << 9)
    # 5: a = (a + C5) + (a << 3)
    # 6: a = (a ^ C6) ^ (a >> 16)
    if name == "stage2":
        C = 0xC761C23C
        k = 19
        return Stage(
            name=name,
            target=lambda a: (a ^ _bv32(C)) ^ z3.LShR(a, _bv32(k)),
        )
    if name == "stage4":
        C = 0xD3A2646C
        k = 9
        return Stage(
            name=name,
            target=lambda a: (a + _bv32(C)) ^ (a << _bv32(k)),
        )
    if name == "stage6":
        C = 0xB55A4F09
        k = 16
        return Stage(
            name=name,
            target=lambda a: (a ^ _bv32(C)) ^ z3.LShR(a, _bv32(k)),
        )
    raise SystemExit(f"unknown stage {name!r} (expected stage2|stage4|stage6)")


@dataclass
class ProgramModel:
    # op selectors (0..len(BINOPS) for binops, len(BINOPS) means muladd)
    op1: int
    op2: int
    # operand selectors
    a1: int
    b1: int
    c1: int
    a2: int
    b2: int
    c2: int
    # constant registers
    consts: list[int]


def _decode_model(m: z3.ModelRef, sym: dict[str, z3.ExprRef], n_consts: int) -> ProgramModel:
    def _get_int(key: str) -> int:
        v = m.eval(sym[key], model_completion=True)
        assert isinstance(v, z3.IntNumRef)
        return int(v.as_long())

    def _get_bv(key: str) -> int:
        v = m.eval(sym[key], model_completion=True)
        assert isinstance(v, z3.BitVecNumRef)
        return int(v.as_long())

    consts = [_get_bv(f"k{i}") for i in range(n_consts)]
    return ProgramModel(
        op1=_get_int("op1"),
        op2=_get_int("op2"),
        a1=_get_int("a1"),
        b1=_get_int("b1"),
        c1=_get_int("c1"),
        a2=_get_int("a2"),
        b2=_get_int("b2"),
        c2=_get_int("c2"),
        consts=consts,
    )


def _pretty(pm: ProgramModel) -> str:
    def op_name(code: int) -> str:
        if code == len(BINOPS):
            return "muladd"
        return BINOPS[code]

    def src1(i: int) -> str:
        if i == 0:
            return "a"
        return f"k{i-1}"

    def src2(i: int) -> str:
        if i == 0:
            return "a"
        if i == 1:
            return "t1"
        return f"k{i-2}"

    def fmt_const(x: int) -> str:
        return f"0x{x:08x}"

    consts = ", ".join(f"k{i}={fmt_const(v)}" for i, v in enumerate(pm.consts))
    return (
        f"consts: {consts}\n"
        f"t1 = {op_name(pm.op1)}({src1(pm.a1)}, {src1(pm.b1)}, {src1(pm.c1)})\n"
        f"out = {op_name(pm.op2)}({src2(pm.a2)}, {src2(pm.b2)}, {src2(pm.c2)})"
    )


def _build_2op_template(*, n_consts: int) -> tuple[dict[str, z3.ExprRef], z3.BitVecRef, z3.BitVecRef]:
    """
    Return (symbols, a, out(a)) for a generic 2-op program.
    """
    a = z3.BitVec("a", 32)
    const_syms = [z3.BitVec(f"k{i}", 32) for i in range(n_consts)]

    # Selectors: op code in [0..len(BINOPS)] where last is muladd.
    op1 = z3.Int("op1")
    op2 = z3.Int("op2")

    # Operand selectors:
    # - For op1: sources are [a, k0, k1, ...] => size = 1 + n_consts
    # - For op2: sources are [a, t1, k0, k1, ...] => size = 2 + n_consts
    a1 = z3.Int("a1")
    b1 = z3.Int("b1")
    c1 = z3.Int("c1")
    a2 = z3.Int("a2")
    b2 = z3.Int("b2")
    c2 = z3.Int("c2")

    srcs1 = [a, *const_syms]
    x1 = _sel(srcs1, a1)
    y1 = _sel(srcs1, b1)
    z1 = _sel(srcs1, c1)

    # Compute t1.
    t1_bin = _sel([_apply_binop(op, x1, y1) for op in BINOPS], op1)
    t1 = z3.If(op1 == len(BINOPS), (x1 * y1) + z1, t1_bin)

    srcs2 = [a, t1, *const_syms]
    x2 = _sel(srcs2, a2)
    y2 = _sel(srcs2, b2)
    z2 = _sel(srcs2, c2)

    out_bin = _sel([_apply_binop(op, x2, y2) for op in BINOPS], op2)
    out = z3.If(op2 == len(BINOPS), (x2 * y2) + z2, out_bin)

    sym: dict[str, z3.ExprRef] = {
        "op1": op1,
        "op2": op2,
        "a1": a1,
        "b1": b1,
        "c1": c1,
        "a2": a2,
        "b2": b2,
        "c2": c2,
    }
    for i, k in enumerate(const_syms):
        sym[f"k{i}"] = k
    return sym, a, out


def _domain_constraints(sym: dict[str, z3.ExprRef], *, n_consts: int) -> list[z3.BoolRef]:
    cons: list[z3.BoolRef] = []

    def in_range(v: z3.ArithRef, lo: int, hi_excl: int) -> z3.BoolRef:
        return z3.And(v >= lo, v < hi_excl)

    # op code in [0..len(BINOPS)] inclusive (muladd is len(BINOPS))
    cons.append(in_range(sym["op1"], 0, len(BINOPS) + 1))
    cons.append(in_range(sym["op2"], 0, len(BINOPS) + 1))

    # op1 operands in [0..n_consts] (0=a, 1..=k)
    for k in ("a1", "b1", "c1"):
        cons.append(in_range(sym[k], 0, 1 + n_consts))

    # op2 operands in [0..(1+n_consts)] for sources [a,t1,k...]
    for k in ("a2", "b2", "c2"):
        cons.append(in_range(sym[k], 0, 2 + n_consts))

    return cons


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


def _cegis_disprove_2op(
    st: Stage,
    *,
    n_consts: int,
    synth_timeout_ms: int,
    verify_timeout_ms: int,
    max_iters: int,
    seed: int,
    init_samples: int,
) -> tuple[bool, str]:
    """
    Return (disproved, detail).

    disproved=True means: UNSAT for the 2-op template (under this opset),
    i.e. no 2-op program exists.
    """
    sym, a, out = _build_2op_template(n_consts=n_consts)
    dom_cons = _domain_constraints(sym, n_consts=n_consts)

    samples = _initial_samples(seed=seed, n=init_samples)
    seen = set(samples)

    for it in range(1, max_iters + 1):
        # Synthesize a candidate that matches all current samples.
        s = z3.Solver()
        s.set(timeout=synth_timeout_ms)
        s.add(dom_cons)
        for aval in samples:
            s.add(
                z3.substitute(out, (a, _bv32(aval)))
                == z3.substitute(st.target(a), (a, _bv32(aval)))
            )
        res = s.check()
        if res == z3.unknown:
            return False, f"unknown (synthesis timed out) at iter {it} with {len(samples)} samples"
        if res == z3.unsat:
            return True, f"UNSAT (no 2-op program) after {it} iters, {len(samples)} samples"

        m = s.model()
        pm = _decode_model(m, sym, n_consts)

        # Verify by searching for a counterexample input.
        v = z3.Solver()
        v.set(timeout=verify_timeout_ms)

        subs = []
        for i in range(n_consts):
            subs.append((sym[f"k{i}"], _bv32(pm.consts[i])))
        for key in ("op1", "op2", "a1", "b1", "c1", "a2", "b2", "c2"):
            subs.append((sym[key], z3.IntVal(getattr(pm, key))))

        out_m = z3.substitute(out, *subs)
        tgt_m = st.target(a)
        v.add(out_m != tgt_m)
        res = v.check()
        if res == z3.unknown:
            return False, f"unknown (verify timed out)\n{_pretty(pm)}"
        if res == z3.unsat:
            return False, f"SAT: found a 2-op implementation!\n{_pretty(pm)}"

        cex = v.model().eval(a, model_completion=True)
        assert isinstance(cex, z3.BitVecNumRef)
        aval = int(cex.as_long())
        if aval not in seen:
            samples.append(aval)
            seen.add(aval)

    return False, f"gave up after {max_iters} iters (still SAT on samples)"


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--stage", type=str, default="stage2,stage4,stage6",
                    help="comma-separated: stage2,stage4,stage6")
    ap.add_argument("--n-consts", type=int, default=4,
                    help="number of arbitrary 32-bit constants available (k0..kN)")
    ap.add_argument("--init-samples", type=int, default=32,
                    help="initial random+edge samples for CEGIS synthesis")
    ap.add_argument("--max-iters", type=int, default=30,
                    help="max CEGIS iterations before giving up")
    ap.add_argument("--seed", type=int, default=0)
    ap.add_argument("--synth-timeout-ms", type=int, default=4000)
    ap.add_argument("--verify-timeout-ms", type=int, default=4000)
    args = ap.parse_args()

    stages = [s.strip() for s in args.stage.split(",") if s.strip()]
    if not stages:
        raise SystemExit("no stages requested")

    for name in stages:
        st = _stage_by_name(name)
        disproved, detail = _cegis_disprove_2op(
            st,
            n_consts=args.n_consts,
            synth_timeout_ms=args.synth_timeout_ms,
            verify_timeout_ms=args.verify_timeout_ms,
            max_iters=args.max_iters,
            seed=args.seed,
            init_samples=args.init_samples,
        )
        verdict = "NO_2OP" if disproved else "UNKNOWN_OR_FOUND"
        print(f"{name}: {verdict} ({detail})")


if __name__ == "__main__":
    main()

