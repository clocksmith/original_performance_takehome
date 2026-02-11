from __future__ import annotations

from typing import Any

from problem import HASH_STAGES

U32_MASK = (1 << 32) - 1


def _u32(x: int) -> int:
    return x & U32_MASK


def _linear_mult(shift: int) -> int:
    # (a + c) + (a << shift) = a*(1 + 2^shift) + c (mod 2^32)
    return _u32(1 + (1 << shift))


def build_hash_prog_preset(name: str) -> list[dict[str, Any]]:
    """
    Build curated hash programs for hash_variant="prog".

    Registers:
      - val: main state
      - tmp: scratch
      - tmp2: scratch
    """
    if name not in {"baseline", "swap_xor", "tmp_xor_const", "tmp_op1", "pingpong"}:
        raise ValueError(f"unknown hash_prog preset {name!r}")

    prog: list[dict[str, Any]] = []

    if name == "pingpong":
        state = "val"
        for op1, c1, op2, op3, sh in HASH_STAGES:
            nxt = "tmp2" if state == "val" else "val"
            if op1 == "+" and op2 == "+" and op3 == "<<":
                prog.append(
                    {
                        "op": "muladd",
                        "dst": nxt,
                        "a": state,
                        "b": _linear_mult(int(sh)),
                        "c": int(c1),
                        "stage": "linear",
                    }
                )
                state = nxt
                continue
            prog.append({"op": op3, "dst": "tmp", "a": state, "b": int(sh), "stage": "shift"})
            prog.append({"op": op1, "dst": nxt, "a": state, "b": int(c1), "stage": "op1"})
            prog.append({"op": op2, "dst": nxt, "a": nxt, "b": "tmp", "stage": "op2"})
            state = nxt
        return prog

    for op1, c1, op2, op3, sh in HASH_STAGES:
        if op1 == "+" and op2 == "+" and op3 == "<<":
            prog.append(
                {
                    "op": "muladd",
                    "dst": "val",
                    "a": "val",
                    "b": _linear_mult(int(sh)),
                    "c": int(c1),
                    "stage": "linear",
                }
            )
            continue

        if not (op1 == "^" and op2 == "^"):
            prog.append({"op": op3, "dst": "tmp", "a": "val", "b": int(sh), "stage": "shift"})
            prog.append({"op": op1, "dst": "val", "a": "val", "b": int(c1), "stage": "op1"})
            prog.append({"op": op2, "dst": "val", "a": "val", "b": "tmp", "stage": "op2"})
            continue

        if name == "baseline":
            prog.append({"op": op3, "dst": "tmp", "a": "val", "b": int(sh), "stage": "shift"})
            prog.append({"op": "^", "dst": "val", "a": "val", "b": int(c1), "stage": "op1"})
            prog.append({"op": "^", "dst": "val", "a": "val", "b": "tmp", "stage": "op2"})
            continue
        if name == "swap_xor":
            prog.append({"op": op3, "dst": "tmp", "a": "val", "b": int(sh), "stage": "shift"})
            prog.append({"op": "^", "dst": "val", "a": "val", "b": "tmp", "stage": "op1"})
            prog.append({"op": "^", "dst": "val", "a": "val", "b": int(c1), "stage": "op2"})
            continue
        if name == "tmp_xor_const":
            prog.append({"op": op3, "dst": "tmp", "a": "val", "b": int(sh), "stage": "shift"})
            prog.append({"op": "^", "dst": "tmp", "a": "tmp", "b": int(c1), "stage": "op1"})
            prog.append({"op": "^", "dst": "val", "a": "val", "b": "tmp", "stage": "op2"})
            continue
        if name == "tmp_op1":
            prog.append({"op": op3, "dst": "tmp", "a": "val", "b": int(sh), "stage": "shift"})
            prog.append({"op": "^", "dst": "tmp2", "a": "val", "b": int(c1), "stage": "op1"})
            prog.append({"op": "^", "dst": "val", "a": "tmp2", "b": "tmp", "stage": "op2"})
            continue
        raise AssertionError("unreachable")

    return prog
