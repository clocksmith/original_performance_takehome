from collections import defaultdict
from dataclasses import dataclass

from problem import SLOT_LIMITS


@dataclass
class EngineStats:
    total_slots: int = 0
    max_per_cycle: int = 0
    op_counts: dict[str, int] | None = None


def analyze_instrs(instrs, caps=None):
    if caps is None:
        caps = {k: v for k, v in SLOT_LIMITS.items() if k != "debug"}

    stats = {e: EngineStats(op_counts=defaultdict(int)) for e in caps}
    per_cycle = []

    for cycle, instr in enumerate(instrs):
        used = {e: 0 for e in caps}
        for eng, slots in instr.items():
            if eng == "debug":
                continue
            used[eng] += len(slots)
            stats[eng].total_slots += len(slots)
            stats[eng].max_per_cycle = max(stats[eng].max_per_cycle, len(slots))
            for slot in slots:
                stats[eng].op_counts[slot[0]] += 1
        per_cycle.append(used)

    cycles = len(instrs)
    utilization = {
        e: (stats[e].total_slots / (caps[e] * cycles) if cycles else 0.0)
        for e in caps
    }

    return {
        "cycles": cycles,
        "caps": caps,
        "stats": stats,
        "utilization": utilization,
        "per_cycle": per_cycle,
    }


def format_summary(report):
    lines = []
    lines.append(f"cycles: {report['cycles']}")
    for eng, cap in report["caps"].items():
        st = report["stats"][eng]
        util = report["utilization"][eng]
        lines.append(
            f"{eng}: slots={st.total_slots} max/cycle={st.max_per_cycle} "
            f"util={util:.3f}"
        )
    return "\n".join(lines)


def print_summary(report):
    print(format_summary(report))
