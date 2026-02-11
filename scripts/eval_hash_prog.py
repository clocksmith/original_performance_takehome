#!/usr/bin/env python3
from __future__ import annotations

"""
Evaluate curated `hash_variant="prog"` candidates.

What this gives us:
1. A quick semantic check: candidate program == `problem.myhash` on random u32 inputs.
2. A cycle check: plug candidate into SPEC_UB_ENERGY_BUNDLE_1291 and measure bundled cycles.

This is the cheapest way to explore "hash lowering changes" without touching
the rest of the kernel knobs/search space.
"""

import argparse
import json
import random
from dataclasses import replace
import os
from pathlib import Path
import sys
from typing import Any

_REPO_ROOT = os.path.dirname(os.path.dirname(__file__))
if _REPO_ROOT not in sys.path:
    sys.path.insert(0, _REPO_ROOT)

from problem import HASH_STAGES, myhash


U32_MASK = (1 << 32) - 1


def u32(x: int) -> int:
    return x & U32_MASK


def _linear_mult(shift: int) -> int:
    # (a + c) + (a << shift) = a*(1 + 2^shift) + c  (mod 2^32)
    return u32(1 + (1 << shift))


def build_hash_prog(variant: str) -> list[dict[str, Any]]:
    """
    Build a candidate program for the fixed myhash circuit.

    Registers:
      - val: main state
      - tmp: scratch
      - tmp2: scratch (shares the 'sel' scratch in the kernel loop)
    """
    if variant not in {"baseline", "swap_xor", "tmp_xor_const", "tmp_op1", "pingpong"}:
        raise ValueError(f"unknown variant {variant!r}")

    prog: list[dict[str, Any]] = []

    # "pingpong": alternate the hash state register between val and tmp2
    # to reduce in-place clobbering. This is semantics-preserving but can
    # change dependency structure in the scheduler.
    if variant == "pingpong":
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

            # Bitwise/mixed stage:
            #   tmp = shift(state_pre)
            #   nxt = op1(state_pre, c1)
            #   nxt = op2(nxt, tmp)
            prog.append({"op": op3, "dst": "tmp", "a": state, "b": int(sh), "stage": "shift"})
            prog.append({"op": op1, "dst": nxt, "a": state, "b": int(c1), "stage": "op1"})
            prog.append({"op": op2, "dst": nxt, "a": nxt, "b": "tmp", "stage": "op2"})
            state = nxt
        return prog

    for op1, c1, op2, op3, sh in HASH_STAGES:
        if op1 == "+" and op2 == "+" and op3 == "<<":
            # Linear stage: muladd(val, mult, add)
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

        # Bitwise/mixed stage
        # Default lowering: tmp = shift(val_pre); val = op1(val_pre, c1); val = op2(val, tmp)
        if variant == "baseline":
            prog.append({"op": op3, "dst": "tmp", "a": "val", "b": int(sh), "stage": "shift"})
            prog.append({"op": op1, "dst": "val", "a": "val", "b": int(c1), "stage": "op1"})
            prog.append({"op": op2, "dst": "val", "a": "val", "b": "tmp", "stage": "op2"})
            continue

        # XOR-only stages have op1=op2="^"; other stages should stick to baseline.
        if not (op1 == "^" and op2 == "^"):
            prog.append({"op": op3, "dst": "tmp", "a": "val", "b": int(sh), "stage": "shift"})
            prog.append({"op": op1, "dst": "val", "a": "val", "b": int(c1), "stage": "op1"})
            prog.append({"op": op2, "dst": "val", "a": "val", "b": "tmp", "stage": "op2"})
            continue

        if variant == "swap_xor":
            # tmp = shift(val_pre); val = val ^ tmp; val = val ^ c1
            prog.append({"op": op3, "dst": "tmp", "a": "val", "b": int(sh), "stage": "shift"})
            prog.append({"op": "^", "dst": "val", "a": "val", "b": "tmp", "stage": "op1"})
            prog.append({"op": "^", "dst": "val", "a": "val", "b": int(c1), "stage": "op2"})
            continue

        if variant == "tmp_xor_const":
            # tmp = shift(val_pre); tmp = tmp ^ c1; val = val ^ tmp
            prog.append({"op": op3, "dst": "tmp", "a": "val", "b": int(sh), "stage": "shift"})
            prog.append({"op": "^", "dst": "tmp", "a": "tmp", "b": int(c1), "stage": "op1"})
            prog.append({"op": "^", "dst": "val", "a": "val", "b": "tmp", "stage": "op2"})
            continue

        if variant == "tmp_op1":
            # tmp = shift(val_pre); tmp2 = val_pre ^ c1; val = tmp2 ^ tmp
            prog.append({"op": op3, "dst": "tmp", "a": "val", "b": int(sh), "stage": "shift"})
            prog.append({"op": "^", "dst": "tmp2", "a": "val", "b": int(c1), "stage": "op1"})
            prog.append({"op": "^", "dst": "val", "a": "tmp2", "b": "tmp", "stage": "op2"})
            continue

        raise AssertionError("unreachable")

    return prog


def exec_hash_prog_u32(prog: list[dict[str, Any]], a0: int) -> int:
    regs = {"val": u32(a0), "tmp": 0, "tmp2": 0}

    def src(x):
        if isinstance(x, str):
            return regs[x]
        if isinstance(x, int):
            return u32(x)
        raise TypeError(f"bad src {x!r}")

    def set_dst(dst: str, v: int) -> None:
        if dst not in regs:
            raise KeyError(dst)
        regs[dst] = u32(v)

    for inst in prog:
        op = inst["op"]
        dst = inst["dst"]
        if op == "muladd":
            a = src(inst["a"])
            b = src(inst["b"])
            c = src(inst["c"])
            set_dst(dst, a * b + c)
            continue
        if op == "mov":
            a = src(inst["a"])
            set_dst(dst, a)
            continue

        a = src(inst["a"])
        b = src(inst["b"])
        if op == "+":
            set_dst(dst, a + b)
        elif op == "^":
            set_dst(dst, a ^ b)
        elif op == "<<":
            set_dst(dst, a << b)
        elif op == ">>":
            set_dst(dst, a >> b)
        else:
            raise ValueError(f"unsupported op {op!r}")

    return regs["val"]


def _load_prog_json(path: Path) -> list[dict[str, Any]]:
    payload = json.loads(path.read_text())
    if not isinstance(payload, list):
        raise ValueError("hash_prog json must be a list of instructions")
    return payload


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--variant", type=str, default="baseline")
    ap.add_argument("--prog-json", type=str, default="", help="optional JSON file containing a hash_prog instruction list")
    ap.add_argument("--trials", type=int, default=2000)
    ap.add_argument("--seed", type=int, default=0)
    ap.add_argument("--cycles", action="store_true", help="also compute bundled kernel cycles using SPEC_UB_ENERGY_BUNDLE_1291")
    args = ap.parse_args()

    if args.prog_json:
        prog = _load_prog_json(Path(args.prog_json))
        name = f"json:{args.prog_json}"
    else:
        prog = build_hash_prog(args.variant)
        name = f"variant:{args.variant}"

    rnd = random.Random(args.seed)
    for _ in range(max(0, args.trials)):
        a = rnd.getrandbits(32)
        got = exec_hash_prog_u32(prog, a)
        want = myhash(a)
        if got != want:
            raise SystemExit(
                f"mismatch for {name}: a=0x{a:08x} got=0x{got:08x} want=0x{want:08x}"
            )

    print(f"OK: {name} matches myhash on {args.trials} random u32 inputs")

    if not args.cycles:
        return

    from generator.ub_energy_bundle_1291 import SPEC_UB_ENERGY_BUNDLE_1291
    from generator.build_kernel_base import build_base_instrs

    spec = replace(
        SPEC_UB_ENERGY_BUNDLE_1291,
        hash_variant="prog",
        hash_prog=prog,
    )
    instrs = build_base_instrs(spec)
    cycles = sum(1 for instr in instrs if any(k != "debug" for k in instr))
    print(f"bundled cycles: {cycles}")


if __name__ == "__main__":
    main()
