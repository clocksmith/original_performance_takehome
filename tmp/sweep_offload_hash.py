from __future__ import annotations

import os
import sys
from dataclasses import replace
from time import time

# Allow running from repo root.
_REPO_ROOT = os.path.dirname(os.path.dirname(__file__))
if _REPO_ROOT not in sys.path:
    sys.path.insert(0, _REPO_ROOT)

from generator.ub_energy_bundle_1291 import SPEC_UB_ENERGY_BUNDLE_1291
from generator.build_kernel_base import build_base_instrs


def eval_spec(spec):
    t0 = time()
    instrs = build_base_instrs(spec)
    return len(instrs), time() - t0


def main():
    base = SPEC_UB_ENERGY_BUNDLE_1291
    base_cycles, dt = eval_spec(base)
    print(f"base cycles={base_cycles} dt={dt:.3f}s")

    # Coarse grid. Budgets are counts of vector ops to offload in that category.
    budgets = [0, 16, 32, 64, 96, 128, 192, 256]

    best = (base_cycles, None)
    tries = 0

    for b_shift in budgets:
        for b_op2 in budgets:
            for b_op1 in [0, 16, 32, 64, 96, 128]:
                spec = replace(
                    base,
                    offload_mode="budgeted",
                    offload_hash_shift=True,
                    offload_hash_op2=True,
                    offload_hash_op1=(b_op1 > 0),
                    offload_budget_hash_shift=b_shift,
                    offload_budget_hash_op2=b_op2,
                    offload_budget_hash_op1=b_op1,
                    # keep existing parity/node_xor budgets
                )
                tries += 1
                cyc, dt = eval_spec(spec)
                if cyc < best[0]:
                    best = (cyc, (b_shift, b_op1, b_op2, dt))
                    print(f"NEW BEST cycles={cyc} shift={b_shift} op1={b_op1} op2={b_op2} dt={dt:.3f}s")

    print(f"tries={tries} best={best}")


if __name__ == '__main__':
    main()
