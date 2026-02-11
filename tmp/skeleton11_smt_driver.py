#!/usr/bin/env python3
from __future__ import annotations

import subprocess
import sys
from pathlib import Path

BASE_OP_SEQ = ["muladd", ">>", "^", "^", "muladd", "<<", "+", "^", "muladd", ">>", "^", "^"]
BASE_DST_SEQ = [0, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0]
BASE_SRC_A = [0] * 12
BASE_SRC_B = [2, 4, 5, 1, 6, 8, 9, 1, 10, 12, 13, 1]
BASE_SRC_C = [3, 0, 0, 0, 7, 0, 0, 0, 11, 0, 0, 0]

# Shift constants in the original 12-op skeleton (k2=19, k6=9, k10=16).
FIXED = {"k2": 19, "k6": 9, "k10": 16}


def idx_to_tok(i: int) -> str:
    if i == 0:
        return "val"
    if i == 1:
        return "tmp"
    return f"k{i-2}"


def run_variant(remove_at: int, *, relax: bool) -> tuple[int, str]:
    op_seq = BASE_OP_SEQ[:]
    dst_seq = BASE_DST_SEQ[:]
    src_a = BASE_SRC_A[:]
    src_b = BASE_SRC_B[:]
    src_c = BASE_SRC_C[:]

    op_seq.pop(remove_at)
    dst_seq.pop(remove_at)
    src_a.pop(remove_at)
    src_b.pop(remove_at)
    src_c.pop(remove_at)

    py = Path(__file__).resolve().parents[1] / ".venv" / "bin" / "python"
    args = [
        str(py),
        "scripts/superopt_myhash.py",
        "--shape",
        "full",
        "--n-ops",
        str(len(op_seq)),
        "--width",
        "32",
        "--two-reg",
        "--const-pool",
        "minimal",
        "--const-pool-target",
        "--init-samples",
        "32",
        "--max-iters",
        "80",
        "--synth-timeout-ms",
        "120000",
        "--verify-timeout-ms",
        "120000",
        "--op-seq",
        ",".join(op_seq),
        "--dst-seq",
        ",".join("val" if d == 0 else "tmp" for d in dst_seq),
        "--src-seq-a",
        ",".join(idx_to_tok(x) for x in src_a),
        "--src-seq-b",
        ",".join(idx_to_tok(x) for x in src_b),
        "--src-seq-c",
        ",".join(idx_to_tok(x) for x in src_c),
        "--const-assign",
        ",".join(f"{k}={v}" for k, v in FIXED.items()),
    ]

    if not relax:
        args += ["--shift-src-val", "--shift-dst-tmp", "--muladd-dst-val"]

    p = subprocess.run(args, capture_output=True, text=True)
    return p.returncode, p.stdout + p.stderr


def main() -> int:
    relax = "--relax" in sys.argv
    any_found = False
    for remove_at in range(len(BASE_OP_SEQ)):
        if BASE_OP_SEQ[remove_at] == "muladd":
            continue
        rc, out = run_variant(remove_at, relax=relax)
        tag = f"remove_at={remove_at} op={BASE_OP_SEQ[remove_at]} relax={relax}"
        # Print only summary line + FOUND bodies.
        lines = [ln for ln in out.splitlines() if ln.strip()]
        summary = lines[-1] if lines else "(no output)"
        print(tag, "->", summary)
        if "FOUND program" in out:
            any_found = True
            print(out)
            break
    return 0 if any_found else 1


if __name__ == "__main__":
    raise SystemExit(main())
