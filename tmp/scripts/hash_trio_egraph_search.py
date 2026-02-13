from __future__ import annotations

"""
Minimal "e-graph style" search for hash stage trios.

We search equivalent lowerings for XOR-only hash stages (shift/op1/op2 trio),
verify equivalence to `problem.myhash`, then evaluate real kernel bundle cycles.
"""

import argparse
import itertools
import json
import os
import random
import sys
from dataclasses import asdict, replace
from pathlib import Path
from typing import Any

_REPO_ROOT = os.path.dirname(os.path.dirname(os.path.dirname(__file__)))
if _REPO_ROOT not in sys.path:
    sys.path.insert(0, _REPO_ROOT)

from generator.build_kernel_base import build_base_instrs
from generator.ub_energy_bundle_1291 import SPEC_UB_ENERGY_BUNDLE_1291
from problem import HASH_STAGES, myhash

U32 = (1 << 32) - 1


def u32(x: int) -> int:
    return x & U32


def linear_mult(shift: int) -> int:
    return u32(1 + (1 << shift))


def exec_hash_prog_u32(prog: list[dict[str, Any]], x0: int) -> int:
    regs = {"val": u32(x0), "tmp": 0, "tmp2": 0}

    def src(v: Any) -> int:
        if isinstance(v, str):
            return regs[v]
        if isinstance(v, int):
            return u32(v)
        raise TypeError(v)

    for inst in prog:
        op = inst["op"]
        dst = inst["dst"]
        if op == "muladd":
            regs[dst] = u32(src(inst["a"]) * src(inst["b"]) + src(inst["c"]))
        elif op == "mov":
            regs[dst] = u32(src(inst["a"]))
        elif op == "+":
            regs[dst] = u32(src(inst["a"]) + src(inst["b"]))
        elif op == "^":
            regs[dst] = u32(src(inst["a"]) ^ src(inst["b"]))
        elif op == "<<":
            regs[dst] = u32(src(inst["a"]) << src(inst["b"]))
        elif op == ">>":
            regs[dst] = u32(src(inst["a"]) >> src(inst["b"]))
        else:
            raise ValueError(op)
    return regs["val"]


def trio_lowering(style: str, op3: str, c1: int, sh: int, stage_idx: int) -> list[dict[str, Any]]:
    """
    Lower one XOR-only stage: (val ^ c1) ^ shift(val, sh)
    """
    if style == "baseline":
        return [
            {"op": op3, "dst": "tmp", "a": "val", "b": sh, "stage": "shift", "hash_stage": stage_idx},
            {"op": "^", "dst": "val", "a": "val", "b": c1, "stage": "op1", "hash_stage": stage_idx},
            {"op": "^", "dst": "val", "a": "val", "b": "tmp", "stage": "op2", "hash_stage": stage_idx},
        ]
    if style == "swap":
        return [
            {"op": op3, "dst": "tmp", "a": "val", "b": sh, "stage": "shift", "hash_stage": stage_idx},
            {"op": "^", "dst": "val", "a": "val", "b": "tmp", "stage": "op1", "hash_stage": stage_idx},
            {"op": "^", "dst": "val", "a": "val", "b": c1, "stage": "op2", "hash_stage": stage_idx},
        ]
    if style == "tmp_xor_const":
        return [
            {"op": op3, "dst": "tmp", "a": "val", "b": sh, "stage": "shift", "hash_stage": stage_idx},
            {"op": "^", "dst": "tmp", "a": "tmp", "b": c1, "stage": "op1", "hash_stage": stage_idx},
            {"op": "^", "dst": "val", "a": "val", "b": "tmp", "stage": "op2", "hash_stage": stage_idx},
        ]
    if style == "tmp_op1":
        return [
            {"op": op3, "dst": "tmp", "a": "val", "b": sh, "stage": "shift", "hash_stage": stage_idx},
            {"op": "^", "dst": "tmp2", "a": "val", "b": c1, "stage": "op1", "hash_stage": stage_idx},
            {"op": "^", "dst": "val", "a": "tmp2", "b": "tmp", "stage": "op2", "hash_stage": stage_idx},
        ]
    # New forms not directly exposed by stage knobs.
    if style == "copy_then_tmp_xor":
        return [
            {"op": "mov", "dst": "tmp2", "a": "val", "stage": "copy", "hash_stage": stage_idx},
            {"op": op3, "dst": "tmp", "a": "tmp2", "b": sh, "stage": "shift", "hash_stage": stage_idx},
            {"op": "^", "dst": "tmp2", "a": "tmp2", "b": c1, "stage": "op1", "hash_stage": stage_idx},
            {"op": "^", "dst": "val", "a": "tmp2", "b": "tmp", "stage": "op2", "hash_stage": stage_idx},
        ]
    if style == "shift_in_val":
        return [
            {"op": "mov", "dst": "tmp2", "a": "val", "stage": "copy", "hash_stage": stage_idx},
            {"op": op3, "dst": "val", "a": "val", "b": sh, "stage": "shift", "hash_stage": stage_idx},
            {"op": "^", "dst": "tmp2", "a": "tmp2", "b": c1, "stage": "op1", "hash_stage": stage_idx},
            {"op": "^", "dst": "val", "a": "tmp2", "b": "val", "stage": "op2", "hash_stage": stage_idx},
        ]
    raise ValueError(style)


def build_prog(style_map: dict[int, str]) -> list[dict[str, Any]]:
    prog: list[dict[str, Any]] = []
    for i, (op1, c1, op2, op3, sh) in enumerate(HASH_STAGES):
        if op1 == "+" and op2 == "+" and op3 == "<<":
            prog.append(
                {
                    "op": "muladd",
                    "dst": "val",
                    "a": "val",
                    "b": linear_mult(int(sh)),
                    "c": int(c1),
                    "stage": "linear",
                    "hash_stage": i,
                }
            )
            continue
        if op1 == "^" and op2 == "^":
            style = style_map.get(i, "baseline")
            prog.extend(trio_lowering(style, op3, int(c1), int(sh), i))
            continue
        # Mixed bitwise stage: keep semantic baseline form.
        prog.append({"op": op3, "dst": "tmp", "a": "val", "b": int(sh), "stage": "shift", "hash_stage": i})
        prog.append({"op": op1, "dst": "val", "a": "val", "b": int(c1), "stage": "op1", "hash_stage": i})
        prog.append({"op": op2, "dst": "val", "a": "val", "b": "tmp", "stage": "op2", "hash_stage": i})
    return prog


def verify_prog(prog: list[dict[str, Any]], *, trials: int, seed: int) -> bool:
    edge = [0, 1, 2, 3, (1 << 31) - 1, 1 << 31, (1 << 32) - 1]
    for a in edge:
        if exec_hash_prog_u32(prog, a) != myhash(a):
            return False
    rng = random.Random(seed)
    for _ in range(trials):
        a = rng.getrandbits(32)
        if exec_hash_prog_u32(prog, a) != myhash(a):
            return False
    return True


def bundle_cycles(spec) -> int:
    instrs = build_base_instrs(spec=spec)
    return sum(1 for b in instrs if any(k != "debug" and b.get(k) for k in b))


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--trials", type=int, default=10000)
    ap.add_argument("--seed", type=int, default=0)
    ap.add_argument("--out", type=str, default="tmp/json/hash_trio_egraph_search.json")
    args = ap.parse_args()

    base = SPEC_UB_ENERGY_BUNDLE_1291
    base_cycles = bundle_cycles(base)
    xor_stages = [i for i, (op1, _, op2, _, _) in enumerate(HASH_STAGES) if op1 == "^" and op2 == "^"]
    styles = ["baseline", "swap", "tmp_xor_const", "tmp_op1", "copy_then_tmp_xor", "shift_in_val"]

    print(f"base_cycles={base_cycles} xor_stages={xor_stages}", flush=True)
    best_cycles = base_cycles
    best = None
    tested = 0
    equivalent = 0
    rows: list[dict[str, Any]] = []

    for combo in itertools.product(styles, repeat=len(xor_stages)):
        style_map = {st: style for st, style in zip(xor_stages, combo)}
        prog = build_prog(style_map)
        tested += 1
        ok = verify_prog(prog, trials=args.trials, seed=args.seed + tested)
        if not ok:
            continue
        equivalent += 1
        spec = replace(base, hash_variant="prog", hash_prog=prog, hash_prog_variant="none")
        try:
            cyc = bundle_cycles(spec)
        except Exception as exc:
            rows.append({"style_map": style_map, "error": str(exc)})
            continue
        rows.append({"style_map": style_map, "cycles": cyc})
        if cyc < best_cycles:
            best_cycles = cyc
            best = {"style_map": style_map, "cycles": cyc, "prog": prog}
            print(f"NEW cycles={cyc} style_map={style_map}", flush=True)

    out = {
        "base_cycles": base_cycles,
        "tested": tested,
        "equivalent": equivalent,
        "best_cycles": best_cycles,
        "best": best,
        "results_top": sorted([r for r in rows if "cycles" in r], key=lambda x: x["cycles"])[:20],
    }
    out_path = Path(args.out)
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(json.dumps(out, indent=2), encoding="utf-8")
    print(f"done tested={tested} equivalent={equivalent} best={best_cycles} out={out_path}", flush=True)


if __name__ == "__main__":
    main()
