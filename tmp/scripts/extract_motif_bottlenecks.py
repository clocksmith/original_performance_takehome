from __future__ import annotations

import argparse
import importlib
import json
import math
import os
import sys
from collections import Counter, defaultdict
from dataclasses import asdict
from pathlib import Path
from typing import Any

_REPO_ROOT = os.path.dirname(os.path.dirname(os.path.dirname(__file__)))
if _REPO_ROOT not in sys.path:
    sys.path.insert(0, _REPO_ROOT)

from generator.build_kernel_base import _apply_sched_dep_variant
from generator.offload import apply_offload_stream
from generator.op_list import build_ops
from generator.ops import Op
from generator.scratch_layout import ScratchAlloc, build_layout
from generator.schedule_dep import schedule_ops_dep
from problem import SLOT_LIMITS, VLEN


def _load_spec(ref: str):
    if ":" in ref:
        mod, attr = ref.split(":", 1)
        m = importlib.import_module(mod)
        return getattr(m, attr)
    m = importlib.import_module(ref)
    for attr in ("SPEC_UB_ENERGY_BUNDLE_1291", "SPEC_BASE", "SPEC"):
        if hasattr(m, attr):
            return getattr(m, attr)
    raise SystemExit(f"can't find spec in {ref!r}")


def _op_cost(op: Op) -> int:
    if op.engine == "alu" and op.slot and op.slot[0] == "alu_vec":
        return VLEN
    return 1


def _get_round(op: Op) -> int | None:
    meta = op.meta or {}
    r = meta.get("round")
    if isinstance(r, int):
        return r
    return None


def _motif(op: Op) -> str:
    meta = op.meta or {}
    stage = meta.get("stage")
    sel = meta.get("sel")
    if meta.get("setup"):
        return "setup"
    if stage in {"shift", "op1", "op2", "linear"}:
        return f"hash_{stage}"
    if sel:
        return f"selection_{sel}"
    if meta.get("reset"):
        return "idx_reset"
    if op.engine == "store":
        return "final_store"
    if op.engine == "valu":
        if op.slot[0] == "^":
            return "node_xor"
        if op.slot[0] == "&":
            return "parity"
        if op.slot[0] == "multiply_add":
            return "muladd_misc"
    if op.engine == "flow" and op.slot[0] == "vselect":
        return "selection_vselect"
    if op.engine == "alu" and op.slot[0] in {"==", "<"}:
        return "selection_cmp"
    if op.engine == "load" and op.slot[0] == "load_offset":
        return "uncached_node_load"
    if _get_round(op) is not None:
        return "round_misc"
    return "misc"


def _top_items(counter: Counter, k: int = 12) -> list[dict[str, Any]]:
    return [{"key": key, "count": int(val)} for key, val in counter.most_common(k)]


def _lb_from_counts(counts: dict[str, int]) -> dict[str, int]:
    out: dict[str, int] = {}
    for eng, cap in SLOT_LIMITS.items():
        out[eng] = int(math.ceil(counts.get(eng, 0) / cap)) if cap else 0
    out["lb"] = max(out.values() or [0])
    return out


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument(
        "--spec",
        type=str,
        default="generator.ub_energy_bundle_1291:SPEC_UB_ENERGY_BUNDLE_1291",
    )
    ap.add_argument("--out", type=str, default="tmp/json/motif_stats_1288.json")
    args = ap.parse_args()

    spec = _load_spec(args.spec)
    scratch = ScratchAlloc()
    layout = build_layout(spec, scratch)
    ordered_ops: list[Op] = []
    build_ops(spec, layout, ordered_ops=ordered_ops)
    final_ops = apply_offload_stream(spec, ordered_ops)

    policy = _apply_sched_dep_variant(
        str(getattr(spec, "sched_policy", "baseline")),
        str(getattr(spec, "sched_deps_variant", "full")),
    )
    scheduled = schedule_ops_dep(
        final_ops,
        return_ops=True,
        seed=int(getattr(spec, "sched_seed", 0)),
        jitter=float(getattr(spec, "sched_jitter", 0.0)),
        restarts=int(getattr(spec, "sched_restarts", 1)),
        compact=bool(getattr(spec, "sched_compact", False)),
        repair_passes=int(getattr(spec, "sched_repair_passes", 0)),
        repair_try_swap=bool(getattr(spec, "sched_repair_try_swap", False)),
        policy=policy,
        target_cycles=getattr(spec, "sched_target_cycles", None),
    )

    total_engine = Counter()
    total_kind = Counter()
    total_motif = Counter()
    motif_engine: dict[str, Counter] = defaultdict(Counter)
    round_engine: dict[int, Counter] = defaultdict(Counter)
    round_motif: dict[int, Counter] = defaultdict(Counter)
    temp_tags = Counter()
    offload_count = 0

    for op in final_ops:
        c = _op_cost(op)
        total_engine[op.engine] += c
        total_kind[f"{op.engine}:{op.slot[0]}"] += c
        m = _motif(op)
        total_motif[m] += c
        motif_engine[m][op.engine] += c
        r = _get_round(op)
        if r is not None:
            round_engine[r][op.engine] += c
            round_motif[r][m] += c
        meta = op.meta or {}
        temps = meta.get("temp")
        if isinstance(temps, str):
            temp_tags[temps] += 1
        elif isinstance(temps, (list, tuple)):
            for t in temps:
                if isinstance(t, str):
                    temp_tags[t] += 1
        if meta.get("offload"):
            offload_count += 1

    bundle_cycles = 0
    motif_cycle_presence = Counter()
    engine_cycle_presence = Counter()
    for bundle in scheduled:
        active = False
        motifs_here: set[str] = set()
        engines_here: set[str] = set()
        for eng, slots in bundle.items():
            if eng == "debug" or not slots:
                continue
            active = True
            engines_here.add(eng)
            for slot in slots:
                if isinstance(slot, Op):
                    motifs_here.add(_motif(slot))
        if not active:
            continue
        bundle_cycles += 1
        for m in motifs_here:
            motif_cycle_presence[m] += 1
        for e in engines_here:
            engine_cycle_presence[e] += 1

    motif_lb = {}
    for m, c in motif_engine.items():
        motif_lb[m] = _lb_from_counts(dict(c))

    round_lb = {}
    for r, c in round_engine.items():
        round_lb[r] = _lb_from_counts(dict(c))

    out = {
        "spec_ref": args.spec,
        "schedule_policy_effective": policy,
        "summary": {
            "ordered_ops": len(ordered_ops),
            "final_ops": len(final_ops),
            "scheduled_bundle_cycles": bundle_cycles,
            "offloaded_ops": offload_count,
        },
        "total_engine_counts": {k: int(v) for k, v in total_engine.items()},
        "total_kind_top": _top_items(total_kind, k=20),
        "total_motif_counts": {k: int(v) for k, v in total_motif.items()},
        "motif_lb": motif_lb,
        "motif_cycle_presence": {k: int(v) for k, v in motif_cycle_presence.items()},
        "engine_cycle_presence": {k: int(v) for k, v in engine_cycle_presence.items()},
        "round_lb": {str(k): v for k, v in round_lb.items()},
        "round_motif_top": {
            str(r): _top_items(counter, k=8) for r, counter in sorted(round_motif.items())
        },
        "temp_tag_top": _top_items(temp_tags, k=20),
        "spec": asdict(spec),
    }

    out_path = Path(args.out)
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(json.dumps(out, indent=2), encoding="utf-8")

    print(f"bundle_cycles={bundle_cycles}")
    print("top_motifs:")
    for k, v in Counter(total_motif).most_common(12):
        lb = motif_lb[k]["lb"]
        cyc = motif_cycle_presence.get(k, 0)
        print(f"  {k:20s} count={v:6d} lb={lb:4d} cycle_presence={cyc:4d}")
    print(f"wrote {out_path}")


if __name__ == "__main__":
    main()
