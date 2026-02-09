from __future__ import annotations

"""
Tiny IR for the fixed `myhash` circuit.

Scope: This models only `problem.myhash` (6 HASH_STAGES), not the full kernel.

Hard semantic invariant:
  For every non-linear ("bitwise") stage, the shift operand is the *pre-op1*
  value `a_pre`, not the post-op1 value.
"""

from dataclasses import dataclass
import random
from typing import Literal, Sequence

from problem import HASH_STAGES, myhash

_MASK32 = (1 << 32) - 1


def _u32(x: int) -> int:
    return x & _MASK32


HashBinOp = Literal["+", "^"]
HashShiftOp = Literal["<<", ">>"]


@dataclass(frozen=True)
class LinearStageIR:
    """
    a <- a * mult + add  (mod 2^32)
    """

    stage_idx: int
    mult: int
    add: int


@dataclass(frozen=True)
class BitwiseStageIR:
    """
    a <- op2(op1(a_pre, const), shiftop(a_pre, shift))  (mod 2^32)

    Note: shift operand is explicitly a_pre (pre-op1 value).
    """

    stage_idx: int
    op1: HashBinOp
    const: int
    op2: HashBinOp
    shift_op: HashShiftOp
    shift: int


HashStageIR = LinearStageIR | BitwiseStageIR


def build_myhash_ir(stages: Sequence[tuple[str, int, str, str, int]] = HASH_STAGES) -> list[HashStageIR]:
    out: list[HashStageIR] = []
    for i, (op1, val1, op2, op3, val3) in enumerate(stages):
        if op1 == "+" and op2 == "+":
            mult = _u32(1 + (1 << val3))
            out.append(LinearStageIR(stage_idx=i, mult=mult, add=val1))
        else:
            out.append(
                BitwiseStageIR(
                    stage_idx=i,
                    op1=op1,  # type: ignore[arg-type]
                    const=val1,
                    op2=op2,  # type: ignore[arg-type]
                    shift_op=op3,  # type: ignore[arg-type]
                    shift=val3,
                )
            )
    return out


def eval_myhash_ir(a: int, prog: Sequence[HashStageIR]) -> int:
    a = _u32(a)
    for st in prog:
        if isinstance(st, LinearStageIR):
            a = _u32(a * st.mult + st.add)
            continue

        a_pre = a
        if st.shift_op == "<<":
            shifted = _u32(a_pre << st.shift)
        else:
            shifted = _u32(a_pre >> st.shift)

        if st.op1 == "+":
            op1_out = _u32(a_pre + st.const)
        else:
            op1_out = _u32(a_pre ^ st.const)

        if st.op2 == "+":
            a = _u32(op1_out + shifted)
        else:
            a = _u32(op1_out ^ shifted)

    return a


def check_myhash_equivalence(*, trials: int = 50_000, seed: int = 0) -> None:
    """
    Cheap smoke test: compare `problem.myhash` vs IR evaluator on random 32-bit inputs.
    """

    prog = build_myhash_ir()
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
    for a in edge:
        want = myhash(a)
        got = eval_myhash_ir(a, prog)
        assert got == want, (a, got, want)

    rng = random.Random(seed)
    for _ in range(trials):
        a = rng.getrandbits(32)
        want = myhash(a)
        got = eval_myhash_ir(a, prog)
        assert got == want, (a, got, want)


def main() -> None:
    check_myhash_equivalence()
    print("ok: myhash IR equivalence")


if __name__ == "__main__":
    main()

