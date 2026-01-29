from __future__ import annotations

from collections import defaultdict

from .offload import OffloadedOps


def count_ops(ops: OffloadedOps) -> dict[str, int]:
    counts = defaultdict(int)
    counts["valu"] = len(ops.valu_ops)
    counts["alu"] = len(ops.alu_ops)
    counts["flow"] = len(ops.flow_ops)
    counts["load"] = len(ops.load_ops)
    counts["store"] = len(ops.store_ops)
    return counts
