from __future__ import annotations

from dataclasses import replace

from .spec_base import SPEC_BASE, SpecBase
from .scratch_layout import ScratchAlloc, build_layout
from .op_list import build_ops
from .ops import Op
from problem import SLOT_LIMITS, VLEN

from .schedule_dep import schedule_ops_dep
from .offload import apply_offload_stream


_DEP_SUFFIXES = ("_waw0all", "_waw0", "_nowar", "_nowaw")


def _strip_dep_suffixes(policy: str) -> str:
    out = policy
    while True:
        changed = False
        for suffix in _DEP_SUFFIXES:
            if out.endswith(suffix):
                out = out[: -len(suffix)]
                changed = True
                break
        if not changed:
            break
    return out


def _apply_sched_dep_variant(policy: str, variant: str) -> str:
    base = _strip_dep_suffixes(policy)
    suffix_map = {
        "full": "",
        "nowar": "_nowar",
        "nowaw": "_nowaw",
        "nowaw_nowar": "_nowaw_nowar",
        "waw0": "_waw0",
        "waw0_nowar": "_waw0_nowar",
        "waw0all": "_waw0all",
        "waw0all_nowar": "_waw0all_nowar",
    }
    suffix = suffix_map.get(variant, "")
    return f"{base}{suffix}"


def _temp_tag_suffix(meta: dict, idx: int, mode: str, window: int) -> str:
    if mode == "round":
        return f"r{int(meta.get('round', -1))}"
    if mode == "vec":
        return f"r{int(meta.get('round', -1))}_v{int(meta.get('vec', -1))}"
    if mode == "op":
        return f"i{idx}"
    if mode == "window":
        w = max(1, int(window))
        return f"w{idx // w}"
    return ""


def _rewrite_temp_tags(spec: SpecBase, ops: list[Op]) -> list[Op]:
    mode = str(getattr(spec, "temp_rename_mode", "off") or "off")
    if mode == "off":
        return ops
    window = int(getattr(spec, "temp_rename_window", 8) or 8)
    out: list[Op] = []
    for i, op in enumerate(ops):
        meta = op.meta
        if not meta or "temp" not in meta:
            out.append(op)
            continue
        temp_meta = meta.get("temp")
        if isinstance(temp_meta, str):
            tags = [temp_meta]
            as_list = False
        else:
            tags = list(temp_meta) if temp_meta else []
            as_list = True
        if not tags:
            out.append(op)
            continue
        suffix = _temp_tag_suffix(meta, i, mode, window)
        if not suffix:
            out.append(op)
            continue
        new_tags = [f"{t}@{suffix}" for t in tags]
        new_meta = dict(meta)
        new_meta["temp"] = new_tags if as_list else new_tags[0]
        out.append(
            Op(
                engine=op.engine,
                slot=op.slot,
                offloadable=op.offloadable,
                meta=new_meta,
            )
        )
    return out


def _build_setup_prelude(spec: SpecBase, layout) -> list[dict[str, list[tuple]]]:
    setup_instrs: list[dict[str, list[tuple]]] = []
    assume_zero_indices = bool(getattr(spec, "assume_zero_indices", False))

    def _pack(engine: str, slots: list[tuple]) -> None:
        cap = SLOT_LIMITS[engine]
        for i in range(0, len(slots), cap):
            setup_instrs.append({engine: slots[i : i + cap]})

    # --- Setup phase (dependency-safe, packed per engine) ---
    # Load scalar constants.
    const_loads = []
    for val, addr in sorted(layout.const_s.items()):
        if val == 0 and getattr(spec, "proof_skip_const_zero", False):
            continue
        const_loads.append(("const", addr, val))
    _pack("load", const_loads)

    # Load base pointers from mem[4], mem[5], mem[6].
    ptr_loads = [
        ("load", layout.forest_values_p, layout.const_s[4]),
        ("load", layout.inp_values_p, layout.const_s[6]),
    ]
    if not assume_zero_indices:
        ptr_loads.insert(1, ("load", layout.inp_indices_p, layout.const_s[5]))
    _pack("load", ptr_loads)

    # Broadcast forest_values_p pointer for uncached address compute (shifted if needed).
    if getattr(spec, "idx_shifted", False):
        setup_instrs.append(
            {"alu": [("-", layout.node_tmp, layout.forest_values_p, layout.const_s[1])]}
        )
        setup_instrs.append({"valu": [("vbroadcast", layout.forest_values_v, layout.node_tmp)]})
    else:
        setup_instrs.append({"valu": [("vbroadcast", layout.forest_values_v, layout.forest_values_p)]})

    # Pointer setup (flow add_imm or ALU +, depending on spec).
    ptr_engine = getattr(spec, "ptr_setup_engine", "flow")
    if ptr_engine == "flow":
        flow_setup = [("add_imm", layout.val_ptr[0], layout.inp_values_p, 0)]
        for v in range(1, spec.vectors):
            flow_setup.append(("add_imm", layout.val_ptr[v], layout.val_ptr[v - 1], VLEN))
        if not assume_zero_indices:
            flow_setup.insert(0, ("add_imm", layout.idx_ptr[0], layout.inp_indices_p, 0))
            for v in range(1, spec.vectors):
                flow_setup.insert(2 * v, ("add_imm", layout.idx_ptr[v], layout.idx_ptr[v - 1], VLEN))
        _pack("flow", flow_setup)
    elif ptr_engine == "alu":
        # Two independent pointer chains (idx_ptr and val_ptr). We can safely
        # issue one step from each chain in the same cycle.
        zero = layout.const_s[0]
        vlen = layout.const_s[VLEN]

        slots0: list[tuple] = []
        if not assume_zero_indices:
            slots0.append(("+", layout.idx_ptr[0], layout.inp_indices_p, zero))
        slots0.append(("+", layout.val_ptr[0], layout.inp_values_p, zero))
        setup_instrs.append({"alu": slots0})

        for v in range(1, spec.vectors):
            slots: list[tuple] = []
            if not assume_zero_indices:
                slots.append(("+", layout.idx_ptr[v], layout.idx_ptr[v - 1], vlen))
            slots.append(("+", layout.val_ptr[v], layout.val_ptr[v - 1], vlen))
            setup_instrs.append({"alu": slots})
    else:
        raise ValueError(f"unknown ptr_setup_engine {ptr_engine!r}")

    # Cached node loads + broadcasts (sequential to preserve node_tmp dependency).
    if getattr(spec, "node_ptr_incremental", False):
        zero = layout.const_s[0]
        one = layout.const_s[1]
        node_ptr = layout.inp_indices_p
        setup_instrs.append({"alu": [("+", node_ptr, layout.forest_values_p, zero)]})
        for i, vaddr in enumerate(layout.node_v):
            setup_instrs.append({"load": [("load", layout.node_tmp, node_ptr)]})
            setup_instrs.append({"valu": [("vbroadcast", vaddr, layout.node_tmp)]})
            if i + 1 < len(layout.node_v):
                setup_instrs.append({"alu": [("+", node_ptr, node_ptr, one)]})
    else:
        for i, vaddr in enumerate(layout.node_v):
            setup_instrs.append(
                {"alu": [("+", layout.node_tmp, layout.forest_values_p, layout.const_s[i])]}
            )
            setup_instrs.append({"load": [("load", layout.node_tmp, layout.node_tmp)]})
            setup_instrs.append({"valu": [("vbroadcast", vaddr, layout.node_tmp)]})

    # Broadcast constants into vectors.
    const_v_broadcasts = [
        ("vbroadcast", vaddr, layout.const_s[val]) for val, vaddr in sorted(layout.const_v.items())
    ]
    _pack("valu", const_v_broadcasts)

    # Initial vloads (indices + values).
    vloads = []
    for v in range(spec.vectors):
        if not assume_zero_indices:
            vloads.append(("vload", layout.idx[v], layout.idx_ptr[v]))
        vloads.append(("vload", layout.val[v], layout.val_ptr[v]))
    _pack("load", vloads)
    # If the harness guarantees zero input indices, we can skip loading them and
    # instead initialize idx vectors here.
    if assume_zero_indices:
        init = layout.const_s[1] if getattr(spec, "idx_shifted", False) else layout.const_s[0]
        idx_inits = [("vbroadcast", layout.idx[v], init) for v in range(spec.vectors)]
        _pack("valu", idx_inits)
    elif getattr(spec, "idx_shifted", False) and not getattr(spec, "proof_assume_shifted_input", False):
        shift_ops = [("+", layout.idx[v], layout.idx[v], layout.const_v[1]) for v in range(spec.vectors)]
        _pack("valu", shift_ops)

    return setup_instrs


def build_base_instrs(spec: SpecBase | None = None):
    if spec is None:
        spec = SPEC_BASE
    scratch = ScratchAlloc()
    layout = build_layout(spec, scratch)

    setup_style = getattr(spec, "setup_style", "inline")
    setup_instrs: list[dict[str, list[tuple]]] = []

    if setup_style == "packed":
        setup_instrs = _build_setup_prelude(spec, layout)

    spec_for_ops = spec
    if setup_style in {"packed", "none"} and getattr(spec, "include_setup", True):
        spec_for_ops = replace(spec, include_setup=False)

    ordered_ops: list[Op] = []
    build_ops(spec_for_ops, layout, ordered_ops=ordered_ops)

    # Apply offload in-order to build the final op stream.
    final_ops = apply_offload_stream(spec, ordered_ops)
    final_ops = _rewrite_temp_tags(spec, final_ops)

    pad_cycles = getattr(spec, "valu_pad_cycles", 0)
    if pad_cycles:
        pad_count = pad_cycles * spec.valu_cap
        pad_dest = layout.tmp[0]
        for _ in range(pad_count):
            final_ops.insert(0, Op(engine="valu", slot=("^", pad_dest, pad_dest, pad_dest)))

    sched_seed = getattr(spec, "sched_seed", 0)
    sched_jitter = getattr(spec, "sched_jitter", 0.0)
    sched_restarts = getattr(spec, "sched_restarts", 1)
    sched_compact = bool(getattr(spec, "sched_compact", False))
    sched_policy = _apply_sched_dep_variant(
        str(getattr(spec, "sched_policy", "baseline")),
        str(getattr(spec, "sched_deps_variant", "full")),
    )
    sched_target_cycles = getattr(spec, "sched_target_cycles", None)
    sched_repair_passes = int(getattr(spec, "sched_repair_passes", 0) or 0)
    sched_repair_try_swap = bool(getattr(spec, "sched_repair_try_swap", False))
    instrs = schedule_ops_dep(
        final_ops,
        seed=sched_seed,
        jitter=sched_jitter,
        restarts=sched_restarts,
        compact=sched_compact,
        repair_passes=sched_repair_passes,
        repair_try_swap=sched_repair_try_swap,
        policy=sched_policy,
        target_cycles=sched_target_cycles,
    )
    if setup_style == "packed":
        return setup_instrs + instrs
    return instrs
