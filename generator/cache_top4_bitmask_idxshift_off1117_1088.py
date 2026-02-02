from __future__ import annotations

from dataclasses import replace

import json
import os

from generator.spec_base import SPEC_BASE
from generator.build_kernel_base import build_base_instrs

SPEC_CACHE_TOP4_BITMASK_IDXSHIFT_OFF1117_1088 = replace(
    SPEC_BASE,
    use_bitmask_selection=True,
    selection_mode="bitmask",
    idx_shifted=True,
    offload_op1=1117,
    total_cycles=1088,
    depth4_rounds=0,
    depth4_cached_rounds=(),
    x4=0,
)

def build_instrs():
    root = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
    sched_path = os.path.join(
        root, "schedules", "cache_top4_bitmask_idxshift_off1117_1088.json"
    )
    if os.path.exists(sched_path):
        with open(sched_path, "r", encoding="utf-8") as f:
            data = json.load(f)

        def to_tuple(x):
            if isinstance(x, list):
                return tuple(to_tuple(v) for v in x)
            if isinstance(x, dict):
                return {k: to_tuple(v) for k, v in x.items()}
            return x

        return [to_tuple(instr) for instr in data]

    return build_base_instrs(spec=SPEC_CACHE_TOP4_BITMASK_IDXSHIFT_OFF1117_1088)
