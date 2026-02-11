from __future__ import annotations

import os, sys
from dataclasses import replace
from time import time

_REPO_ROOT = os.path.dirname(os.path.dirname(__file__))
if _REPO_ROOT not in sys.path:
    sys.path.insert(0, _REPO_ROOT)

from generator.ub_energy_bundle_1291 import SPEC_UB_ENERGY_BUNDLE_1291
from generator.build_kernel_base import build_base_instrs


def main():
    base = SPEC_UB_ENERGY_BUNDLE_1291
    best = (10**9, None)
    t0 = time()
    for seed in range(0, 201):
        spec = replace(base, sched_seed=seed, sched_restarts=1, sched_jitter=0.15)
        cycles = len(build_base_instrs(spec))
        if cycles < best[0]:
            best = (cycles, seed)
            print('NEW', best)
    print('best', best, 'elapsed', time()-t0)


if __name__ == '__main__':
    main()
