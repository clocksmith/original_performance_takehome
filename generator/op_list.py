from __future__ import annotations

from dataclasses import dataclass

from problem import HASH_STAGES, VLEN

from .ops import Op, OpLists

_ORDERED_OPS: list[Op] | None = None
_SEQ = 0
_USE_VALU_SELECT = False
_VALU_SELECT_ROUNDS: set[int] | None = None
_USE_TEMP_DEPS = True
_USE_TEMP_DEPS_EXTRAS = True
_USE_VALU_SELECT_LEAF = False
_VALU_OPS_REF: list[Op] | None = None
_LAYOUT_REF: Layout | None = None


def _record(op: Op) -> None:
    global _SEQ
    if _ORDERED_OPS is None:
        return
    _SEQ += 1
    if op.meta is None:
        op.meta = {}
    op.meta["_seq"] = _SEQ
    _ORDERED_OPS.append(op)


def _tag_temp(meta: dict | None, key: str) -> dict:
    if not _USE_TEMP_DEPS:
        return meta if meta is not None else {}
    if not _USE_TEMP_DEPS_EXTRAS and key.startswith("extra:"):
        return meta if meta is not None else {}
    new_meta = {} if meta is None else dict(meta)
    temps = new_meta.get("temp")
    if temps is None:
        temps = []
    elif isinstance(temps, str):
        temps = [temps]
    else:
        temps = list(temps)
    temps.append(key)
    new_meta["temp"] = temps
    return new_meta


@dataclass(frozen=True)
class LinearStage:
    mult: int
    add: int


@dataclass(frozen=True)
class BitwiseStage:
    op1: str
    const: int
    op2: str
    shift_op: str
    shift: int


def _split_hash_stages() -> tuple[list[LinearStage], list[BitwiseStage]]:
    linear: list[LinearStage] = []
    bitwise: list[BitwiseStage] = []
    for op1, val1, op2, op3, val3 in HASH_STAGES:
        if op1 == "+" and op2 == "+":
            mult = (1 + (1 << val3)) % (2**32)
            linear.append(LinearStage(mult=mult, add=val1))
        else:
            bitwise.append(BitwiseStage(op1=op1, const=val1, op2=op2, shift_op=op3, shift=val3))
    return linear, bitwise


def _vaddr(base: int) -> tuple[int, ...]:
    return tuple(base + i for i in range(VLEN))


def _add_valu(ops: list[Op], op: str, dest: int, a: int, b: int, meta=None, offloadable=False):
    new_op = Op(engine="valu", slot=(op, dest, a, b), offloadable=offloadable, meta=meta)
    _record(new_op)
    ops.append(new_op)


def _add_vmuladd(ops: list[Op], dest: int, a: int, b: int, c: int, meta=None):
    new_op = Op(engine="valu", slot=("multiply_add", dest, a, b, c), meta=meta)
    _record(new_op)
    ops.append(new_op)


def _add_vselect(ops: list[Op], dest: int, cond: int, a: int, b: int, meta=None):
    # When enabled, lower vector select into VALU ops:
    #   dest = b + cond * (a - b)
    # This is valid for our use-cases because `cond` is always 0/1 per lane
    # (bit-extraction masks or compare results). Note: the 2-op lowering needs
    # the original `b` value, so we only apply it when `dest != b` (or when we
    # have a precomputed (a-b) diff for 1-op lowering).
    if _USE_VALU_SELECT and _VALU_OPS_REF is not None:
        if _VALU_SELECT_ROUNDS is not None:
            r = None if meta is None else meta.get("round")
            if r is None or r not in _VALU_SELECT_ROUNDS:
                new_op = Op(engine="flow", slot=("vselect", dest, cond, a, b), meta=meta)
                _record(new_op)
                ops.append(new_op)
                return
        # 1-op lowering when we have a precomputed (a-b) diff vector.
        if _LAYOUT_REF is not None and (a, b) in _LAYOUT_REF.node_diff_v:
            diff_addr = _LAYOUT_REF.node_diff_v[(a, b)]
            _add_vmuladd(_VALU_OPS_REF, dest, cond, diff_addr, b, meta=meta)
            return
        # Fallback to 2-op selection. This is only safe when dest != b, since we
        # need the original `b` value for the multiply_add.
        if dest == b:
            new_op = Op(engine="flow", slot=("vselect", dest, cond, a, b), meta=meta)
            _record(new_op)
            ops.append(new_op)
            return
        _add_valu(_VALU_OPS_REF, "-", dest, a, b, meta=meta)
        _add_vmuladd(_VALU_OPS_REF, dest, cond, dest, b, meta=meta)
        return
    new_op = Op(engine="flow", slot=("vselect", dest, cond, a, b), meta=meta)
    _record(new_op)
    ops.append(new_op)


def _add_flow_add_imm(ops: list[Op], dest: int, a: int, imm: int, meta=None):
    new_op = Op(engine="flow", slot=("add_imm", dest, a, imm), meta=meta)
    _record(new_op)
    ops.append(new_op)


def _add_vbroadcast(ops: list[Op], dest: int, src: int, meta=None):
    new_op = Op(engine="valu", slot=("vbroadcast", dest, src), meta=meta)
    _record(new_op)
    ops.append(new_op)


def _add_load(ops: list[Op], dest: int, addr: int, meta=None):
    new_op = Op(engine="load", slot=("load", dest, addr), meta=meta)
    _record(new_op)
    ops.append(new_op)


def _add_const(ops: list[Op], dest: int, val: int, meta=None):
    new_op = Op(engine="load", slot=("const", dest, val), meta=meta)
    _record(new_op)
    ops.append(new_op)


def _add_alu_vec(ops: list[Op], op: str, dest: int, a: int, b_scalar: int, meta=None):
    for lane in range(VLEN):
        new_op = Op(engine="alu", slot=(op, dest + lane, a + lane, b_scalar), meta=meta)
        _record(new_op)
        ops.append(new_op)


def _add_alu(ops: list[Op], op: str, dest: int, a: int, b: int, meta=None):
    new_op = Op(engine="alu", slot=(op, dest, a, b), meta=meta)
    _record(new_op)
    ops.append(new_op)

def _idx_const(spec, const_s: dict[int, int], val: int) -> int:
    if getattr(spec, "idx_shifted", False):
        return const_s[val + 1]
    return const_s[val]


def _add_vselect_parity(spec, ops: list[Op], dest: int, cond: int, a: int, b: int, meta=None):
    if getattr(spec, "idx_shifted", False):
        a, b = b, a
    # Leaf-pair fast path: use a 1-op VALU muladd with a precomputed (a-b) diff
    # when enabled. This removes the FLOW vselect at leaf sites without
    # introducing the 2-op VALU lowering required for arbitrary merges.
    if _USE_VALU_SELECT_LEAF and _VALU_OPS_REF is not None and _LAYOUT_REF is not None:
        diff_addr = _LAYOUT_REF.node_diff_v.get((a, b))
        if diff_addr is not None:
            _add_vmuladd(_VALU_OPS_REF, dest, cond, diff_addr, b, meta=meta)
            return
    _add_vselect(ops, dest, cond, a, b, meta=meta)


def _selection_mode(spec, round_idx: int | None = None) -> str:
    per_round = getattr(spec, "selection_mode_by_round", None)
    if per_round is not None and round_idx is not None:
        mode = per_round.get(round_idx)
        if mode:
            return mode
    mode = getattr(spec, "selection_mode", None)
    if mode:
        return mode
    return "bitmask" if getattr(spec, "use_bitmask_selection", False) else "eq"


def _select_by_eq_alu(
    spec,
    alu_ops: list[Op],
    flow_ops: list[Op],
    tmp: int,
    sel: int,
    idx: int,
    nodes: list[tuple[int, int]],
    const_s: dict[int, int],
    const_v: dict[int, int],
    meta=None,
):
    if not nodes:
        raise ValueError("empty node list")
    base_addr = nodes[0][1]
    first = True
    for node_idx, node_addr in nodes[1:]:
        _add_alu_vec(alu_ops, "==", sel, idx, _idx_const(spec, const_s, node_idx), meta=meta)
        if first:
            _add_vselect(flow_ops, tmp, sel, node_addr, base_addr, meta=meta)
            first = False
        else:
            _add_vselect(flow_ops, tmp, sel, node_addr, tmp, meta=meta)
    return tmp

def _add_vload(ops: list[Op], dest: int, addr: int, meta=None):
    new_op = Op(engine="load", slot=("vload", dest, addr), meta=meta)
    _record(new_op)
    ops.append(new_op)


def _add_load_offset(ops: list[Op], dest: int, addr: int, offset: int, meta=None):
    new_op = Op(engine="load", slot=("load_offset", dest, addr, offset), meta=meta)
    _record(new_op)
    ops.append(new_op)


def _add_vstore(ops: list[Op], addr: int, src: int, meta=None):
    new_op = Op(engine="store", slot=("vstore", addr, src), meta=meta)
    _record(new_op)
    ops.append(new_op)



def build_ops(spec, layout, ordered_ops: list[Op] | None = None) -> OpLists:
    global _ORDERED_OPS, _SEQ, _USE_VALU_SELECT, _USE_VALU_SELECT_LEAF, _VALU_SELECT_ROUNDS, _USE_TEMP_DEPS, _USE_TEMP_DEPS_EXTRAS, _VALU_OPS_REF, _LAYOUT_REF
    _ORDERED_OPS = ordered_ops
    _SEQ = 0
    _USE_VALU_SELECT = bool(getattr(spec, "valu_select", False))
    _USE_VALU_SELECT_LEAF = bool(getattr(spec, "valu_select_leaf_pairs", False))
    rounds = getattr(spec, "valu_select_rounds", None)
    _VALU_SELECT_ROUNDS = None if rounds is None else set(rounds)
    _USE_TEMP_DEPS = bool(getattr(spec, "use_temp_deps", True))
    _USE_TEMP_DEPS_EXTRAS = bool(getattr(spec, "use_temp_deps_extras", True))
    _LAYOUT_REF = layout
    valu_ops: list[Op] = []
    _VALU_OPS_REF = valu_ops
    alu_ops: list[Op] = []
    flow_ops: list[Op] = []
    load_ops: list[Op] = []
    store_ops: list[Op] = []

    hash_variant = getattr(spec, "hash_variant", "direct")
    if hash_variant not in {"direct", "ir", "prog"}:
        raise ValueError(f"unknown hash_variant {hash_variant!r}")
    linear, bitwise = _split_hash_stages()
    hash_ir_prog = None
    _HashLinear = None
    _HashBitwise = None
    if hash_variant == "ir":
        from . import hash_ir as _hash_ir

        hash_ir_prog = _hash_ir.build_myhash_ir()
        _HashLinear = _hash_ir.LinearStageIR
        _HashBitwise = _hash_ir.BitwiseStageIR
    hash_prog = None
    if hash_variant == "prog":
        hash_prog = getattr(spec, "hash_prog", None)
        if not hash_prog:
            preset = str(getattr(spec, "hash_prog_variant", "none") or "none")
            if preset != "none":
                from .hash_prog_presets import build_hash_prog_preset

                hash_prog = build_hash_prog_preset(preset)
        if not hash_prog:
            raise ValueError("hash_variant='prog' requires spec.hash_prog")
    selection_modes_per_round = [_selection_mode(spec, r) for r in range(spec.rounds)]
    use_vector_major = any(
        mode in {"bitmask", "bitmask_valu", "mask", "mask_precompute"}
        for mode in selection_modes_per_round
    )
    # Optional override for op emission order. This changes the linear stream,
    # which changes the derived dependency graph, which can change achievable
    # packing in the scheduler.
    emit_order = getattr(spec, "emit_order", "auto")
    if emit_order not in {"auto", "vector_major", "round_major", "block"}:
        raise ValueError(f"unknown emit_order {emit_order!r}")
    if emit_order == "vector_major":
        use_vector_major = True
    elif emit_order == "round_major":
        use_vector_major = False
    cached_round_aliases = getattr(spec, "cached_round_aliases", None) or {}
    cached_round_depths = getattr(spec, "cached_round_depth", None) or {}
    cached_round_x = getattr(spec, "cached_round_x", None) or {}
    cached_rounds = (
        set(getattr(spec, "base_cached_rounds", ()))
        | set(cached_round_aliases.keys())
        | set(cached_round_depths.keys())
    )

    def _depth_from_round(r: int) -> int | None:
        if r in (0, 11):
            return 0
        if r in (1, 12):
            return 1
        if r in (2, 13):
            return 2
        if r in (3, 14):
            return 3
        return None

    def _depth_from_alias(val: int) -> int | None:
        if val in (0, 11, 1, 12, 2, 13, 3, 14):
            return _depth_from_round(val)
        if val in (0, 1, 2, 3):
            return val
        return None

    if getattr(spec, "include_setup", True):
        assume_zero_indices = bool(getattr(spec, "assume_zero_indices", False))
        # Scalar constants
        for val, addr in sorted(layout.const_s.items()):
            if val == 0 and getattr(spec, "proof_skip_const_zero", False):
                continue
            _add_const(load_ops, addr, val, meta={"setup": True, "const": val})

        # Load base pointers from mem[4], mem[5], mem[6]
        _add_load(load_ops, layout.forest_values_p, layout.const_s[4], meta={"setup": True, "ptr": "forest_values_p"})
        if not assume_zero_indices:
            _add_load(load_ops, layout.inp_indices_p, layout.const_s[5], meta={"setup": True, "ptr": "inp_indices_p"})
        _add_load(load_ops, layout.inp_values_p, layout.const_s[6], meta={"setup": True, "ptr": "inp_values_p"})

        # Pointer setup (flow or ALU)
        ptr_engine = getattr(spec, "ptr_setup_engine", "flow")
        if ptr_engine == "flow":
            _add_flow_add_imm(flow_ops, layout.val_ptr[0], layout.inp_values_p, 0, meta={"setup": True})
            for v in range(1, spec.vectors):
                _add_flow_add_imm(flow_ops, layout.val_ptr[v], layout.val_ptr[v - 1], VLEN, meta={"setup": True})
            if not assume_zero_indices:
                _add_flow_add_imm(flow_ops, layout.idx_ptr[0], layout.inp_indices_p, 0, meta={"setup": True})
                for v in range(1, spec.vectors):
                    _add_flow_add_imm(flow_ops, layout.idx_ptr[v], layout.idx_ptr[v - 1], VLEN, meta={"setup": True})
        elif ptr_engine == "alu":
            zero = layout.const_s[0]
            vlen = layout.const_s[VLEN]
            _add_alu(alu_ops, "+", layout.val_ptr[0], layout.inp_values_p, zero, meta={"setup": True})
            for v in range(1, spec.vectors):
                _add_alu(alu_ops, "+", layout.val_ptr[v], layout.val_ptr[v - 1], vlen, meta={"setup": True})
            if not assume_zero_indices:
                _add_alu(alu_ops, "+", layout.idx_ptr[0], layout.inp_indices_p, zero, meta={"setup": True})
                for v in range(1, spec.vectors):
                    _add_alu(alu_ops, "+", layout.idx_ptr[v], layout.idx_ptr[v - 1], vlen, meta={"setup": True})
        else:
            raise ValueError(f"unknown ptr_setup_engine {ptr_engine!r}")

        # Broadcast constants into vectors
        for val, vaddr in sorted(layout.const_v.items()):
            _add_vbroadcast(valu_ops, vaddr, layout.const_s[val], meta={"setup": True, "const": val})

        # Cached node loads + broadcasts
        if getattr(spec, "node_ptr_incremental", False):
            zero = layout.const_s[0]
            one = layout.const_s[1]
            node_ptr = layout.inp_indices_p
            _add_alu(alu_ops, "+", node_ptr, layout.forest_values_p, zero, meta={"setup": True, "node": "base"})
            for i, vaddr in enumerate(layout.node_v):
                _add_load(load_ops, layout.node_tmp, node_ptr, meta={"setup": True, "node": i})
                _add_vbroadcast(valu_ops, vaddr, layout.node_tmp, meta={"setup": True, "node": i})
                if i + 1 < len(layout.node_v):
                    _add_alu(
                        alu_ops,
                        "+",
                        node_ptr,
                        node_ptr,
                        one,
                        meta={"setup": True, "node": "inc"},
                    )
        else:
            for i, vaddr in enumerate(layout.node_v):
                _add_alu(alu_ops, "+", layout.node_tmp, layout.forest_values_p, layout.const_s[i], meta={"setup": True, "node": i})
                _add_load(load_ops, layout.node_tmp, layout.node_tmp, meta={"setup": True, "node": i})
                _add_vbroadcast(valu_ops, vaddr, layout.node_tmp, meta={"setup": True, "node": i})

        # Precompute node differences for fast VALU selection
        if _USE_VALU_SELECT or _USE_VALU_SELECT_LEAF:
            for (addr_a, addr_b), diff_addr in layout.node_diff_v.items():
                _add_valu(valu_ops, "-", diff_addr, addr_a, addr_b, meta={"setup": True, "diff": True})

        # Precompute fused node constants for Stage 5 fusion
        if getattr(spec, "fuse_stages", False):
            const_C5 = layout.const_v[HASH_STAGES[5][1]]
            for i, vaddr in enumerate(layout.node_v):
                _add_valu(valu_ops, "^", layout.node_fused_v[i], vaddr, const_C5, meta={"setup": True, "fuse": True})

        # Broadcast forest_values pointer for uncached address compute (shifted if needed).
        if getattr(spec, "idx_shifted", False):
            _add_alu(
                alu_ops,
                "-",
                layout.node_tmp,
                layout.forest_values_p,
                layout.const_s[1],
                meta={"setup": True, "ptr": "forest_values_p_shift"},
            )
            _add_vbroadcast(
                valu_ops,
                layout.forest_values_v,
                layout.node_tmp,
                meta={"setup": True, "ptr": "forest_values_p_shift"},
            )
        else:
            _add_vbroadcast(
                valu_ops,
                layout.forest_values_v,
                layout.forest_values_p,
                meta={"setup": True, "ptr": "forest_values_p"},
            )

        # Initial vloads (values always; indices optional).
        for v in range(spec.vectors):
            if not assume_zero_indices:
                _add_vload(load_ops, layout.idx[v], layout.idx_ptr[v], meta={"vec": v})
                if getattr(spec, "idx_shifted", False) and not getattr(spec, "proof_assume_shifted_input", False):
                    # Shift idx into 1-based representation.
                    _add_valu(
                        valu_ops,
                        "+",
                        layout.idx[v],
                        layout.idx[v],
                        layout.const_v[1],
                        meta={"setup": True, "vec": v, "idx_shift": True},
                    )
            else:
                # Harness initializes input indices to 0; avoid idx loads and initialize here.
                init = layout.const_s[1] if getattr(spec, "idx_shifted", False) else layout.const_s[0]
                _add_vbroadcast(
                    valu_ops,
                    layout.idx[v],
                    init,
                    meta={"setup": True, "vec": v, "idx_init": True},
                )
            _add_vload(load_ops, layout.val[v], layout.val_ptr[v], meta={"vec": v})

    # Rounds (blocked, round-major when using shared temp buffers)
    block = getattr(spec, "vector_block", 0)
    if emit_order != "block":
        block = 0
    if block:
        vec_round_pairs = []
        for block_start in range(0, spec.vectors, block):
            block_end = min(spec.vectors, block_start + block)
            for r in range(spec.rounds):
                for v in range(block_start, block_end):
                    vec_round_pairs.append((v, r))
    elif use_vector_major:
        vec_round_pairs = [(v, r) for v in range(spec.vectors) for r in range(spec.rounds)]
    else:
        vec_round_pairs = [(v, r) for r in range(spec.rounds) for v in range(spec.vectors)]

    for v, r in vec_round_pairs:
        selection_mode = selection_modes_per_round[r]
        mask_mode = selection_mode in {"mask", "mask_precompute"}
        tmp = layout.tmp[v]
        sel = layout.sel[v]
        extra = None
        extra2 = None
        extra3 = None
        extra4 = None
        extra_key = None
        extra2_key = None
        extra3_key = None
        extra4_key = None
        tmp_read_key = f"tmp_read:{r}:{v}"
        if layout.extra:
            # IMPORTANT: these scratch temps are real memory locations, so if different vectors
            # share the same `extra*` address the scheduler must serialize them.
            #
            # The old mapping used (v+1), (v+2), ... which creates a dependency ring:
            # vector v writes extra2 == extra of vector (v+1), coupling *all* vectors even
            # when we have many extra vectors available. That can destroy parallelism for
            # bitmask/mask selection and depth4 selection.
            #
            # We instead pick additional temps using large offsets so overlap forms small
            # components (or none) rather than a giant chain.
            k = len(layout.extra)
            base = v % k

            def _pick_offsets(n: int) -> list[int]:
                # Candidate offsets in priority order; we try to keep them far apart.
                cand = [k // 2, k // 3, k // 4, k // 5, 1, 2, 3, 5, 7, 11, 13, 17, 19]
                out: list[int] = []
                used = {0}
                # Can't pick more than k-1 non-zero distinct offsets.
                if k <= 1:
                    return out
                n = min(n, k - 1)
                for off in cand:
                    if len(out) >= n:
                        break
                    off = off % k if k else 0
                    if off == 0 or off in used:
                        continue
                    used.add(off)
                    out.append(off)
                # Worst-case fallback: walk forward until we have enough distinct offsets.
                off = 1
                while len(out) < n:
                    if off not in used:
                        used.add(off)
                        out.append(off)
                        if len(out) >= n:
                            break
                    off += 1
                return out

            extra = layout.extra[base]
            extra_key = f"extra:{base}"
            offs = _pick_offsets(3)  # up to extra4
            if k > 1:
                i2 = (base + offs[0]) % k
                extra2 = layout.extra[i2]
                extra2_key = f"extra:{i2}"
            if k > 2:
                i3 = (base + offs[1]) % k
                extra3 = layout.extra[i3]
                extra3_key = f"extra:{i3}"
            if k > 3:
                i4 = (base + offs[2]) % k
                extra4 = layout.extra[i4]
                extra4_key = f"extra:{i4}"
        idx = layout.idx[v]
        val = layout.val[v]
        offload_node_xor = getattr(spec, "offload_node_xor", False)
        shifts_on_valu = bool(getattr(spec, "shifts_on_valu", True))

        one_v = layout.const_v[1]
        one_s = layout.const_s[1]
        # Const vectors are allocated on-demand by the scratch layout. Avoid
        # unconditionally requiring shift2/shift3 consts for kernels that never
        # take mask/bit-extraction paths.
        shift1_v = layout.const_v.get(1)
        shift2_v = layout.const_v.get(2)
        shift3_v = layout.const_v.get(3)
        shift1_s = layout.const_s.get(1)
        shift2_s = layout.const_s.get(2)
        shift3_s = layout.const_s.get(3)

        def _bit0(dest: int, src: int, *, meta: dict) -> None:
            # dest = src & 1
            if shifts_on_valu:
                _add_valu(valu_ops, "&", dest, src, one_v, meta=meta)
            else:
                _add_alu_vec(alu_ops, "&", dest, src, one_s, meta=meta)

        def _shr_bit1(dest: int, src: int, shift_s_addr: int | None, shift_v_addr: int | None, *, meta: dict) -> None:
            # dest = (src >> shift) & 1
            if shifts_on_valu:
                if shift_v_addr is None:
                    raise RuntimeError("missing shift const_v in scratch layout for VALU bit-extraction")
                _add_valu(valu_ops, ">>", dest, src, shift_v_addr, meta=meta)
                _add_valu(valu_ops, "&", dest, dest, one_v, meta=meta)
            else:
                if shift_s_addr is None:
                    raise RuntimeError("missing shift const_s in scratch layout for ALU bit-extraction")
                _add_alu_vec(alu_ops, ">>", dest, src, shift_s_addr, meta=meta)
                _add_alu_vec(alu_ops, "&", dest, dest, one_s, meta=meta)

        def _node_xor(src: int, meta=None) -> None:
            _add_valu(
                valu_ops,
                "^",
                val,
                val,
                src,
                meta=meta,
                offloadable=offload_node_xor,
            )
        r_sel = cached_round_aliases.get(r, r)
        # Resolve per-round cache depth and partial caching (x).
        cache_depth = None
        if r in cached_round_depths:
            cache_depth = cached_round_depths[r]
        elif r in cached_round_aliases:
            cache_depth = _depth_from_alias(cached_round_aliases[r])
        elif r in cached_rounds:
            cache_depth = _depth_from_round(r)
        cache_x = cached_round_x.get(r, spec.vectors) if cache_depth is not None else 0

        r_sel = cache_depth if cache_depth in (0, 1, 2, 3) else None

        if cache_depth is not None and v < cache_x:
            if r_sel == 0:
                _node_xor(layout.node_v[0], meta={"round": r, "vec": v})
            elif r_sel == 1:
                if mask_mode and getattr(spec, "idx_shifted", False):
                    _bit0(tmp, idx, meta={"round": r, "vec": v, "sel": "mask"})
                    _add_vselect(
                        flow_ops,
                        sel,
                        tmp,
                        layout.node_v[2],
                        layout.node_v[1],
                        meta=_tag_temp({"round": r, "vec": v, "sel": "mask"}, tmp_read_key),
                    )
                    _node_xor(sel, meta={"round": r, "vec": v})
                elif selection_mode in {"bitmask", "bitmask_valu"} and extra is not None:
                    _add_alu_vec(alu_ops, "&", tmp, idx, layout.const_s[1], meta={"round": r, "vec": v})
                    _add_vselect_parity(
                        spec,
                        flow_ops,
                        sel,
                        tmp,
                        layout.node_v[1],
                        layout.node_v[2],
                        meta=_tag_temp({"round": r, "vec": v}, tmp_read_key),
                    )
                    _node_xor(sel, meta={"round": r, "vec": v})
                else:
                    nodes = [(1, layout.node_v[1]), (2, layout.node_v[2])]
                    _select_by_eq_alu(spec, alu_ops, flow_ops, tmp, sel, idx, nodes, layout.const_s, layout.const_v, meta={"round": r, "vec": v})
                    _node_xor(tmp, meta={"round": r, "vec": v})
            elif r_sel == 2:
                if mask_mode and getattr(spec, "idx_shifted", False) and extra is not None:
                    _bit0(tmp, idx, meta={"round": r, "vec": v, "sel": "mask"})
                    _add_vselect(
                        flow_ops,
                        sel,
                        tmp,
                        layout.node_v[4],
                        layout.node_v[3],
                        meta=_tag_temp({"round": r, "vec": v, "sel": "mask"}, tmp_read_key),
                    )
                    _add_vselect(
                        flow_ops,
                        extra,
                        tmp,
                        layout.node_v[6],
                        layout.node_v[5],
                        meta=_tag_temp(_tag_temp({"round": r, "vec": v, "sel": "mask"}, extra_key), tmp_read_key),
                    )
                    _shr_bit1(tmp, idx, shift1_s, shift1_v, meta={"round": r, "vec": v, "sel": "mask"})
                    _add_vselect(
                        flow_ops,
                        sel,
                        tmp,
                        extra,
                        sel,
                        meta=_tag_temp({"round": r, "vec": v, "sel": "mask"}, extra_key),
                    )
                    _node_xor(sel, meta={"round": r, "vec": v})
                elif selection_mode in {"bitmask", "bitmask_valu"} and extra is not None:
                    _add_alu_vec(alu_ops, "&", tmp, idx, layout.const_s[1], meta={"round": r, "vec": v})
                    _add_vselect_parity(
                        spec,
                        flow_ops,
                        sel,
                        tmp,
                        layout.node_v[3],
                        layout.node_v[4],
                        meta=_tag_temp({"round": r, "vec": v}, tmp_read_key),
                    )
                    _add_vselect_parity(
                        spec,
                        flow_ops,
                        extra,
                        tmp,
                        layout.node_v[5],
                        layout.node_v[6],
                        meta=_tag_temp(_tag_temp({"round": r, "vec": v}, extra_key), tmp_read_key),
                    )
                    _add_alu_vec(
                        alu_ops,
                        "<",
                        tmp,
                        idx,
                        _idx_const(spec, layout.const_s, 5),
                        meta={"round": r, "vec": v},
                    )
                    _add_vselect(
                        flow_ops,
                        sel,
                        tmp,
                        sel,
                        extra,
                        meta=_tag_temp({"round": r, "vec": v}, extra_key),
                    )
                    _node_xor(sel, meta={"round": r, "vec": v})
                else:
                    nodes = [(i, layout.node_v[i]) for i in range(3, 7)]
                    _select_by_eq_alu(spec, alu_ops, flow_ops, tmp, sel, idx, nodes, layout.const_s, layout.const_v, meta={"round": r, "vec": v})
                    _node_xor(tmp, meta={"round": r, "vec": v})
            elif r_sel == 3:
                if (
                    mask_mode
                    and getattr(spec, "idx_shifted", False)
                    and extra is not None
                    and extra2 is not None
                ):
                    # mask0 -> tmp, select pairs for nodes 7..10
                    _bit0(tmp, idx, meta={"round": r, "vec": v, "sel": "mask"})
                    _add_vselect(
                        flow_ops,
                        sel,
                        tmp,
                        layout.node_v[8],
                        layout.node_v[7],
                        meta=_tag_temp({"round": r, "vec": v, "sel": "mask"}, tmp_read_key),
                    )
                    _add_vselect(
                        flow_ops,
                        extra2,
                        tmp,
                        layout.node_v[10],
                        layout.node_v[9],
                        meta=_tag_temp(_tag_temp({"round": r, "vec": v, "sel": "mask"}, extra2_key), tmp_read_key),
                    )
                    # mask1 -> tmp, select between pairs (lower half)
                    _shr_bit1(tmp, idx, shift1_s, shift1_v, meta={"round": r, "vec": v, "sel": "mask"})
                    _add_vselect(
                        flow_ops,
                        sel,
                        tmp,
                        extra2,
                        sel,
                        meta=_tag_temp({"round": r, "vec": v, "sel": "mask"}, extra2_key),
                    )

                    # mask0 -> tmp, select pairs for nodes 11..14
                    _bit0(tmp, idx, meta={"round": r, "vec": v, "sel": "mask"})
                    _add_vselect(
                        flow_ops,
                        extra,
                        tmp,
                        layout.node_v[12],
                        layout.node_v[11],
                        meta=_tag_temp(_tag_temp({"round": r, "vec": v, "sel": "mask"}, extra_key), tmp_read_key),
                    )
                    _add_vselect(
                        flow_ops,
                        extra2,
                        tmp,
                        layout.node_v[14],
                        layout.node_v[13],
                        meta=_tag_temp(_tag_temp({"round": r, "vec": v, "sel": "mask"}, extra2_key), tmp_read_key),
                    )
                    # mask1 -> tmp, select between pairs (upper half)
                    _shr_bit1(tmp, idx, shift1_s, shift1_v, meta={"round": r, "vec": v, "sel": "mask"})
                    _add_vselect(
                        flow_ops,
                        extra,
                        tmp,
                        extra2,
                        extra,
                        meta=_tag_temp({"round": r, "vec": v, "sel": "mask"}, extra2_key or extra_key),
                    )

                    # mask2 -> tmp, select between lower and upper
                    _shr_bit1(tmp, idx, shift2_s, shift2_v, meta={"round": r, "vec": v, "sel": "mask"})
                    _add_vselect(
                        flow_ops,
                        sel,
                        tmp,
                        extra,
                        sel,
                        meta=_tag_temp({"round": r, "vec": v, "sel": "mask"}, extra_key),
                    )
                    _node_xor(sel, meta={"round": r, "vec": v})
                elif selection_mode in {"bitmask", "bitmask_valu"} and extra is not None:
                    # Lower half: nodes 7..10
                    _add_alu_vec(alu_ops, "&", tmp, idx, layout.const_s[1], meta={"round": r, "vec": v})
                    _add_vselect_parity(
                        spec,
                        flow_ops,
                        sel,
                        tmp,
                        layout.node_v[7],
                        layout.node_v[8],
                        meta=_tag_temp({"round": r, "vec": v}, tmp_read_key),
                    )
                    if extra2 is not None:
                        _add_vselect_parity(
                            spec,
                            flow_ops,
                            extra2,
                            tmp,
                            layout.node_v[9],
                            layout.node_v[10],
                            meta=_tag_temp(_tag_temp({"round": r, "vec": v}, extra2_key), tmp_read_key),
                        )
                        _add_alu_vec(
                            alu_ops,
                            "<",
                            tmp,
                            idx,
                            _idx_const(spec, layout.const_s, 9),
                            meta={"round": r, "vec": v},
                        )
                        _add_vselect(
                            flow_ops,
                            sel,
                            tmp,
                            sel,
                            extra2,
                            meta=_tag_temp({"round": r, "vec": v}, extra2_key),
                        )
                    else:
                        _add_vselect(
                            flow_ops,
                            extra,
                            tmp,
                            layout.node_v[9],
                            layout.node_v[10],
                            meta=_tag_temp(_tag_temp({"round": r, "vec": v}, extra_key), tmp_read_key),
                        )
                        _add_alu_vec(
                            alu_ops,
                            "<",
                            tmp,
                            idx,
                            _idx_const(spec, layout.const_s, 9),
                            meta={"round": r, "vec": v},
                        )
                        _add_vselect(
                            flow_ops,
                            sel,
                            tmp,
                            sel,
                            extra,
                            meta=_tag_temp({"round": r, "vec": v}, extra_key),
                        )

                    # Upper half: nodes 11..14 (use LSB selection)
                    _add_alu_vec(alu_ops, "&", tmp, idx, layout.const_s[1], meta={"round": r, "vec": v})
                    _add_vselect_parity(
                        spec,
                        flow_ops,
                        extra,
                        tmp,
                        layout.node_v[11],
                        layout.node_v[12],
                        meta=_tag_temp(_tag_temp({"round": r, "vec": v}, extra_key), tmp_read_key),
                    )
                    _add_vselect_parity(
                        spec,
                        flow_ops,
                        extra2 if extra2 is not None else sel,
                        tmp,
                        layout.node_v[13],
                        layout.node_v[14],
                        meta=_tag_temp(_tag_temp({"round": r, "vec": v}, extra2_key or extra_key), tmp_read_key),
                    )
                    _add_alu_vec(
                        alu_ops,
                        "<",
                        tmp,
                        idx,
                        _idx_const(spec, layout.const_s, 13),
                        meta={"round": r, "vec": v},
                    )
                    _add_vselect(
                        flow_ops,
                        extra,
                        tmp,
                        extra,
                        extra2 if extra2 is not None else sel,
                        meta=_tag_temp({"round": r, "vec": v}, extra_key),
                    )

                    # Final select between lower and upper
                    _add_alu_vec(
                        alu_ops,
                        "<",
                        tmp,
                        idx,
                        _idx_const(spec, layout.const_s, 11),
                        meta={"round": r, "vec": v},
                    )
                    _add_vselect(
                        flow_ops,
                        sel,
                        tmp,
                        sel,
                        extra,
                        meta=_tag_temp({"round": r, "vec": v}, extra_key),
                    )
                    _node_xor(sel, meta={"round": r, "vec": v})
                else:
                    nodes = [(i, layout.node_v[i]) for i in range(7, 15)]
                    _select_by_eq_alu(spec, alu_ops, flow_ops, tmp, sel, idx, nodes, layout.const_s, layout.const_v, meta={"round": r, "vec": v})
                    _node_xor(tmp, meta={"round": r, "vec": v})
            else:
                # Shouldn't happen for current spec, but keep uncached fallback.
                _add_valu(valu_ops, "+", sel, idx, layout.forest_values_v, meta={"round": r, "vec": v})
                for lane in range(VLEN):
                    _add_load_offset(load_ops, tmp, sel, lane, meta={"round": r, "vec": v, "lane": lane})
                _node_xor(tmp, meta={"round": r, "vec": v})
        elif r in spec.depth4_cached_rounds and v < spec.x4:
            if selection_mode == "bitmask_valu" and extra is not None and extra2 is not None and extra3 is not None:
                # Depth4 bitmask selection using VALU for bit extraction (reduces per-lane ALU pressure).
                # bit0 in tmp
                _bit0(tmp, idx, meta={"round": r, "vec": v, "sel": "bitmask_valu", "bit": 0})
                # bit1 in extra3
                _shr_bit1(extra3, idx, shift1_s, shift1_v, meta={"round": r, "vec": v, "sel": "bitmask_valu", "bit": 1})

                # Lower half (15..22) -> sel
                _add_vselect(flow_ops, sel, tmp, layout.node_v[16], layout.node_v[15], meta={"round": r, "vec": v, "sel": "bitmask_valu"})
                _add_vselect(flow_ops, extra, tmp, layout.node_v[18], layout.node_v[17], meta={"round": r, "vec": v, "sel": "bitmask_valu"})
                _add_vselect(flow_ops, sel, extra3, extra, sel, meta={"round": r, "vec": v, "sel": "bitmask_valu"})
                _add_vselect(flow_ops, extra, tmp, layout.node_v[20], layout.node_v[19], meta={"round": r, "vec": v, "sel": "bitmask_valu"})
                _add_vselect(flow_ops, extra2, tmp, layout.node_v[22], layout.node_v[21], meta={"round": r, "vec": v, "sel": "bitmask_valu"})
                _add_vselect(flow_ops, extra, extra3, extra2, extra, meta={"round": r, "vec": v, "sel": "bitmask_valu"})

                # bit2 in extra3
                _shr_bit1(extra3, idx, shift2_s, shift2_v, meta={"round": r, "vec": v, "sel": "bitmask_valu", "bit": 2})
                _add_vselect(flow_ops, sel, extra3, extra, sel, meta={"round": r, "vec": v, "sel": "bitmask_valu"})

                # Recompute bit1 into extra3
                _shr_bit1(extra3, idx, shift1_s, shift1_v, meta={"round": r, "vec": v, "sel": "bitmask_valu", "bit": 1})

                # Upper half (23..30) -> extra
                _add_vselect(flow_ops, extra, tmp, layout.node_v[24], layout.node_v[23], meta={"round": r, "vec": v, "sel": "bitmask_valu"})
                _add_vselect(flow_ops, extra2, tmp, layout.node_v[26], layout.node_v[25], meta={"round": r, "vec": v, "sel": "bitmask_valu"})
                _add_vselect(flow_ops, extra, extra3, extra2, extra, meta={"round": r, "vec": v, "sel": "bitmask_valu"})
                _add_vselect(flow_ops, extra2, tmp, layout.node_v[28], layout.node_v[27], meta={"round": r, "vec": v, "sel": "bitmask_valu"})
                _add_vselect(flow_ops, extra3, tmp, layout.node_v[30], layout.node_v[29], meta={"round": r, "vec": v, "sel": "bitmask_valu"})

                # bit1 in tmp (recompute) for upper pair select
                _shr_bit1(tmp, idx, shift1_s, shift1_v, meta={"round": r, "vec": v, "sel": "bitmask_valu", "bit": 1})
                _add_vselect(flow_ops, extra2, tmp, extra3, extra2, meta={"round": r, "vec": v, "sel": "bitmask_valu"})

                # bit2 in tmp for upper reduction
                _shr_bit1(tmp, idx, shift2_s, shift2_v, meta={"round": r, "vec": v, "sel": "bitmask_valu", "bit": 2})
                _add_vselect(flow_ops, extra, tmp, extra2, extra, meta={"round": r, "vec": v, "sel": "bitmask_valu"})

                # Final select between lower (sel) and upper (extra) using bit3
                _shr_bit1(tmp, idx, shift3_s, shift3_v, meta={"round": r, "vec": v, "sel": "bitmask_valu", "bit": 3})
                _add_vselect(flow_ops, sel, tmp, extra, sel, meta={"round": r, "vec": v, "sel": "bitmask_valu"})
                _node_xor(sel, meta={"round": r, "vec": v})
            elif selection_mode == "bitmask" and extra is not None and extra2 is not None and extra3 is not None:
                # Depth4 bitmask selection (nodes 15..30) with extra temp vectors.
                # Upper half (23..30) -> extra
                _add_alu_vec(alu_ops, "&", tmp, idx, layout.const_s[1], meta={"round": r, "vec": v, "sel": "bitmask"})
                _add_vselect_parity(
                    spec,
                    flow_ops,
                    extra,
                    tmp,
                    layout.node_v[23],
                    layout.node_v[24],
                    meta=_tag_temp({"round": r, "vec": v, "sel": "bitmask"}, tmp_read_key),
                )
                _add_vselect_parity(
                    spec,
                    flow_ops,
                    extra2,
                    tmp,
                    layout.node_v[25],
                    layout.node_v[26],
                    meta=_tag_temp(_tag_temp({"round": r, "vec": v, "sel": "bitmask"}, extra2_key), tmp_read_key),
                )
                _add_alu_vec(
                    alu_ops,
                    "<",
                    tmp,
                    idx,
                    _idx_const(spec, layout.const_s, 25),
                    meta={"round": r, "vec": v, "sel": "bitmask"},
                )
                _add_vselect(
                    flow_ops,
                    extra,
                    tmp,
                    extra,
                    extra2,
                    meta=_tag_temp({"round": r, "vec": v, "sel": "bitmask"}, extra2_key),
                )

                _add_alu_vec(alu_ops, "&", tmp, idx, layout.const_s[1], meta={"round": r, "vec": v, "sel": "bitmask"})
                _add_vselect_parity(
                    spec,
                    flow_ops,
                    extra2,
                    tmp,
                    layout.node_v[27],
                    layout.node_v[28],
                    meta=_tag_temp(_tag_temp({"round": r, "vec": v, "sel": "bitmask"}, extra2_key), tmp_read_key),
                )
                _add_vselect_parity(
                    spec,
                    flow_ops,
                    extra3,
                    tmp,
                    layout.node_v[29],
                    layout.node_v[30],
                    meta=_tag_temp(_tag_temp({"round": r, "vec": v, "sel": "bitmask"}, extra3_key), tmp_read_key),
                )
                _add_alu_vec(
                    alu_ops,
                    "<",
                    tmp,
                    idx,
                    _idx_const(spec, layout.const_s, 29),
                    meta={"round": r, "vec": v, "sel": "bitmask"},
                )
                _add_vselect(
                    flow_ops,
                    extra2,
                    tmp,
                    extra2,
                    extra3,
                    meta=_tag_temp({"round": r, "vec": v, "sel": "bitmask"}, extra3_key),
                )
                _add_alu_vec(
                    alu_ops,
                    "<",
                    tmp,
                    idx,
                    _idx_const(spec, layout.const_s, 27),
                    meta={"round": r, "vec": v, "sel": "bitmask"},
                )
                _add_vselect(
                    flow_ops,
                    extra,
                    tmp,
                    extra,
                    extra2,
                    meta=_tag_temp({"round": r, "vec": v, "sel": "bitmask"}, extra2_key),
                )

                # Lower half (15..22) -> sel
                _add_alu_vec(alu_ops, "&", tmp, idx, layout.const_s[1], meta={"round": r, "vec": v, "sel": "bitmask"})
                _add_vselect_parity(
                    spec,
                    flow_ops,
                    sel,
                    tmp,
                    layout.node_v[15],
                    layout.node_v[16],
                    meta=_tag_temp({"round": r, "vec": v, "sel": "bitmask"}, tmp_read_key),
                )
                _add_vselect_parity(
                    spec,
                    flow_ops,
                    extra2,
                    tmp,
                    layout.node_v[17],
                    layout.node_v[18],
                    meta=_tag_temp(_tag_temp({"round": r, "vec": v, "sel": "bitmask"}, extra2_key), tmp_read_key),
                )
                _add_alu_vec(
                    alu_ops,
                    "<",
                    tmp,
                    idx,
                    _idx_const(spec, layout.const_s, 17),
                    meta={"round": r, "vec": v, "sel": "bitmask"},
                )
                _add_vselect(
                    flow_ops,
                    sel,
                    tmp,
                    sel,
                    extra2,
                    meta=_tag_temp({"round": r, "vec": v, "sel": "bitmask"}, extra2_key),
                )

                _add_alu_vec(alu_ops, "&", tmp, idx, layout.const_s[1], meta={"round": r, "vec": v, "sel": "bitmask"})
                _add_vselect_parity(
                    spec,
                    flow_ops,
                    extra2,
                    tmp,
                    layout.node_v[19],
                    layout.node_v[20],
                    meta=_tag_temp(_tag_temp({"round": r, "vec": v, "sel": "bitmask"}, extra2_key), tmp_read_key),
                )
                _add_vselect_parity(
                    spec,
                    flow_ops,
                    extra3,
                    tmp,
                    layout.node_v[21],
                    layout.node_v[22],
                    meta=_tag_temp(_tag_temp({"round": r, "vec": v, "sel": "bitmask"}, extra3_key), tmp_read_key),
                )
                _add_alu_vec(
                    alu_ops,
                    "<",
                    tmp,
                    idx,
                    _idx_const(spec, layout.const_s, 21),
                    meta={"round": r, "vec": v, "sel": "bitmask"},
                )
                _add_vselect(
                    flow_ops,
                    extra2,
                    tmp,
                    extra2,
                    extra3,
                    meta=_tag_temp({"round": r, "vec": v, "sel": "bitmask"}, extra3_key),
                )
                _add_alu_vec(
                    alu_ops,
                    "<",
                    tmp,
                    idx,
                    _idx_const(spec, layout.const_s, 19),
                    meta={"round": r, "vec": v, "sel": "bitmask"},
                )
                _add_vselect(
                    flow_ops,
                    sel,
                    tmp,
                    sel,
                    extra2,
                    meta=_tag_temp({"round": r, "vec": v, "sel": "bitmask"}, extra2_key),
                )

                # Final select between lower (sel) and upper (extra)
                _add_alu_vec(
                    alu_ops,
                    "<",
                    tmp,
                    idx,
                    _idx_const(spec, layout.const_s, 23),
                    meta={"round": r, "vec": v, "sel": "bitmask"},
                )
                _add_vselect(
                    flow_ops,
                    sel,
                    tmp,
                    sel,
                    extra,
                    meta=_tag_temp({"round": r, "vec": v, "sel": "bitmask"}, extra_key),
                )
                _node_xor(sel, meta={"round": r, "vec": v})
            elif (
                mask_mode
                and getattr(spec, "idx_shifted", False)
                and extra is not None
                and extra2 is not None
                and extra3 is not None
            ):
                if selection_mode == "mask_precompute" and extra4 is not None:
                    # Like "mask", but precompute bit0/bit1 once and reuse them.
                    # This reduces redundant VALU work in depth4 selection.
                    # bit0 -> extra4, bit1 -> extra3
                    _bit0(extra4, idx, meta={"round": r, "vec": v, "sel": "mask_precompute", "bit": 0})
                    _shr_bit1(extra3, idx, shift1_s, shift1_v, meta={"round": r, "vec": v, "sel": "mask_precompute", "bit": 1})

                    # Lower half (15..22) -> extra2
                    _add_vselect(
                        flow_ops,
                        sel,
                        extra4,
                        layout.node_v[16],
                        layout.node_v[15],
                        meta=_tag_temp({"round": r, "vec": v, "sel": "mask_precompute"}, tmp_read_key),
                    )
                    _add_vselect(
                        flow_ops,
                        extra,
                        extra4,
                        layout.node_v[18],
                        layout.node_v[17],
                        meta=_tag_temp(_tag_temp({"round": r, "vec": v, "sel": "mask_precompute"}, extra_key), tmp_read_key),
                    )
                    _add_vselect(
                        flow_ops,
                        sel,
                        extra3,
                        extra,
                        sel,
                        meta=_tag_temp({"round": r, "vec": v, "sel": "mask_precompute"}, extra_key),
                    )
                    _add_vselect(
                        flow_ops,
                        extra,
                        extra4,
                        layout.node_v[20],
                        layout.node_v[19],
                        meta=_tag_temp(_tag_temp({"round": r, "vec": v, "sel": "mask_precompute"}, extra_key), tmp_read_key),
                    )
                    _add_vselect(
                        flow_ops,
                        extra2,
                        extra4,
                        layout.node_v[22],
                        layout.node_v[21],
                        meta=_tag_temp(_tag_temp({"round": r, "vec": v, "sel": "mask_precompute"}, extra2_key), tmp_read_key),
                    )
                    _add_vselect(
                        flow_ops,
                        extra,
                        extra3,
                        extra2,
                        extra,
                        meta=_tag_temp({"round": r, "vec": v, "sel": "mask_precompute"}, extra2_key),
                    )
                    _shr_bit1(tmp, idx, shift2_s, shift2_v, meta={"round": r, "vec": v, "sel": "mask_precompute", "bit": 2})
                    _add_vselect(
                        flow_ops,
                        extra2,
                        tmp,
                        extra,
                        sel,
                        meta=_tag_temp({"round": r, "vec": v, "sel": "mask_precompute"}, extra_key),
                    )

                    # Upper half (23..30) -> extra
                    _add_vselect(
                        flow_ops,
                        sel,
                        extra4,
                        layout.node_v[24],
                        layout.node_v[23],
                        meta=_tag_temp({"round": r, "vec": v, "sel": "mask_precompute"}, tmp_read_key),
                    )
                    _add_vselect(
                        flow_ops,
                        extra,
                        extra4,
                        layout.node_v[26],
                        layout.node_v[25],
                        meta=_tag_temp(_tag_temp({"round": r, "vec": v, "sel": "mask_precompute"}, extra_key), tmp_read_key),
                    )
                    _add_vselect(
                        flow_ops,
                        sel,
                        extra3,
                        extra,
                        sel,
                        meta=_tag_temp({"round": r, "vec": v, "sel": "mask_precompute"}, extra_key),
                    )
                    _add_vselect(
                        flow_ops,
                        extra,
                        extra4,
                        layout.node_v[28],
                        layout.node_v[27],
                        meta=_tag_temp(_tag_temp({"round": r, "vec": v, "sel": "mask_precompute"}, extra_key), tmp_read_key),
                    )
                    _add_vselect(
                        flow_ops,
                        tmp,
                        extra4,
                        layout.node_v[30],
                        layout.node_v[29],
                        meta=_tag_temp({"round": r, "vec": v, "sel": "mask_precompute"}, tmp_read_key),
                    )
                    _add_vselect(
                        flow_ops,
                        extra,
                        extra3,
                        tmp,
                        extra,
                        meta=_tag_temp({"round": r, "vec": v, "sel": "mask_precompute"}, extra_key),
                    )
                    _shr_bit1(tmp, idx, shift2_s, shift2_v, meta={"round": r, "vec": v, "sel": "mask_precompute", "bit": 2})
                    _add_vselect(
                        flow_ops,
                        extra,
                        tmp,
                        extra,
                        sel,
                        meta=_tag_temp({"round": r, "vec": v, "sel": "mask_precompute"}, extra_key),
                    )

                    # Final select between lower (extra2) and upper (extra) using bit3.
                    _shr_bit1(tmp, idx, shift3_s, shift3_v, meta={"round": r, "vec": v, "sel": "mask_precompute", "bit": 3})
                    _add_vselect(
                        flow_ops,
                        sel,
                        tmp,
                        extra,
                        extra2,
                        meta=_tag_temp({"round": r, "vec": v, "sel": "mask_precompute"}, extra2_key),
                    )
                    _node_xor(sel, meta={"round": r, "vec": v})
                else:
                    # Lower half (15..22) -> extra2
                    _bit0(tmp, idx, meta={"round": r, "vec": v, "sel": "mask"})
                    _add_vselect(
                        flow_ops,
                        sel,
                        tmp,
                        layout.node_v[16],
                        layout.node_v[15],
                        meta=_tag_temp({"round": r, "vec": v, "sel": "mask"}, tmp_read_key),
                    )
                    _add_vselect(
                        flow_ops,
                        extra,
                        tmp,
                        layout.node_v[18],
                        layout.node_v[17],
                        meta=_tag_temp(_tag_temp({"round": r, "vec": v, "sel": "mask"}, extra_key), tmp_read_key),
                    )
                    _shr_bit1(tmp, idx, shift1_s, shift1_v, meta={"round": r, "vec": v, "sel": "mask"})
                    _add_vselect(
                        flow_ops,
                        sel,
                        tmp,
                        extra,
                        sel,
                        meta=_tag_temp({"round": r, "vec": v, "sel": "mask"}, extra_key),
                    )
                    _bit0(tmp, idx, meta={"round": r, "vec": v, "sel": "mask"})
                    _add_vselect(
                        flow_ops,
                        extra,
                        tmp,
                        layout.node_v[20],
                        layout.node_v[19],
                        meta=_tag_temp(_tag_temp({"round": r, "vec": v, "sel": "mask"}, extra_key), tmp_read_key),
                    )
                    _add_vselect(
                        flow_ops,
                        extra3,
                        tmp,
                        layout.node_v[22],
                        layout.node_v[21],
                        meta=_tag_temp(_tag_temp({"round": r, "vec": v, "sel": "mask"}, extra3_key), tmp_read_key),
                    )
                    _shr_bit1(tmp, idx, shift1_s, shift1_v, meta={"round": r, "vec": v, "sel": "mask"})
                    _add_vselect(
                        flow_ops,
                        extra,
                        tmp,
                        extra3,
                        extra,
                        meta=_tag_temp({"round": r, "vec": v, "sel": "mask"}, extra3_key),
                    )
                    _shr_bit1(tmp, idx, shift2_s, shift2_v, meta={"round": r, "vec": v, "sel": "mask"})
                    _add_vselect(
                        flow_ops,
                        extra2,
                        tmp,
                        extra,
                        sel,
                        meta=_tag_temp({"round": r, "vec": v, "sel": "mask"}, extra_key),
                    )

                    # Upper half (23..30) -> extra
                    _bit0(tmp, idx, meta={"round": r, "vec": v, "sel": "mask"})
                    _add_vselect(
                        flow_ops,
                        sel,
                        tmp,
                        layout.node_v[24],
                        layout.node_v[23],
                        meta=_tag_temp({"round": r, "vec": v, "sel": "mask"}, tmp_read_key),
                    )
                    _add_vselect(
                        flow_ops,
                        extra,
                        tmp,
                        layout.node_v[26],
                        layout.node_v[25],
                        meta=_tag_temp(_tag_temp({"round": r, "vec": v, "sel": "mask"}, extra_key), tmp_read_key),
                    )
                    _shr_bit1(tmp, idx, shift1_s, shift1_v, meta={"round": r, "vec": v, "sel": "mask"})
                    _add_vselect(
                        flow_ops,
                        sel,
                        tmp,
                        extra,
                        sel,
                        meta=_tag_temp({"round": r, "vec": v, "sel": "mask"}, extra_key),
                    )
                    _bit0(tmp, idx, meta={"round": r, "vec": v, "sel": "mask"})
                    _add_vselect(
                        flow_ops,
                        extra,
                        tmp,
                        layout.node_v[28],
                        layout.node_v[27],
                        meta=_tag_temp(_tag_temp({"round": r, "vec": v, "sel": "mask"}, extra_key), tmp_read_key),
                    )
                    _add_vselect(
                        flow_ops,
                        extra3,
                        tmp,
                        layout.node_v[30],
                        layout.node_v[29],
                        meta=_tag_temp(_tag_temp({"round": r, "vec": v, "sel": "mask"}, extra3_key), tmp_read_key),
                    )
                    _shr_bit1(tmp, idx, shift1_s, shift1_v, meta={"round": r, "vec": v, "sel": "mask"})
                    _add_vselect(
                        flow_ops,
                        extra,
                        tmp,
                        extra3,
                        extra,
                        meta=_tag_temp({"round": r, "vec": v, "sel": "mask"}, extra3_key),
                    )
                    _shr_bit1(tmp, idx, shift2_s, shift2_v, meta={"round": r, "vec": v, "sel": "mask"})
                    _add_vselect(
                        flow_ops,
                        extra,
                        tmp,
                        extra,
                        sel,
                        meta=_tag_temp({"round": r, "vec": v, "sel": "mask"}, extra_key),
                    )

                # bit3 selects between lower (extra2) and upper (extra)
                _shr_bit1(tmp, idx, shift3_s, shift3_v, meta={"round": r, "vec": v, "sel": "mask"})
                _add_vselect(
                    flow_ops,
                    sel,
                    tmp,
                    extra,
                    extra2,
                    meta=_tag_temp({"round": r, "vec": v, "sel": "mask"}, extra2_key),
                )
                _node_xor(sel, meta={"round": r, "vec": v})
            else:
                nodes = [(i, layout.node_v[i]) for i in range(15, 31)]
                _select_by_eq_alu(spec, alu_ops, flow_ops, tmp, sel, idx, nodes, layout.const_s, layout.const_v, meta={"round": r, "vec": v})
                _node_xor(tmp, meta={"round": r, "vec": v})
        else:
            # Uncached: load node values
            _add_valu(valu_ops, "+", sel, idx, layout.forest_values_v, meta={"round": r, "vec": v})
            for lane in range(VLEN):
                _add_load_offset(load_ops, tmp, sel, lane, meta={"round": r, "vec": v, "lane": lane})
            _node_xor(tmp, meta={"round": r, "vec": v})

        # Hash stages
        hash_bitwise_style_global = getattr(spec, "hash_bitwise_style", "inplace")
        if hash_bitwise_style_global not in {"inplace", "tmp_op1"}:
            raise ValueError(f"unknown hash_bitwise_style {hash_bitwise_style_global!r}")
        hash_bitwise_style_by_stage = getattr(spec, "hash_bitwise_style_by_stage", None) or {}

        hash_xor_style_global = getattr(spec, "hash_xor_style", "baseline")
        if hash_xor_style_global not in {"baseline", "swap", "tmp_xor_const"}:
            raise ValueError(f"unknown hash_xor_style {hash_xor_style_global!r}")
        hash_xor_style_by_stage = getattr(spec, "hash_xor_style_by_stage", None) or {}
        if hash_variant == "ir":
            assert hash_ir_prog is not None
            assert _HashLinear is not None and _HashBitwise is not None

            for st in hash_ir_prog:
                if isinstance(st, _HashLinear):
                    mult_v = layout.const_v[st.mult]
                    add_v = layout.const_v[st.add]
                    _add_vmuladd(
                        valu_ops,
                        val,
                        val,
                        mult_v,
                        add_v,
                        meta={"round": r, "vec": v, "stage": "linear", "hash_stage": st.stage_idx},
                    )
                    continue

                assert isinstance(st, _HashBitwise)
                hash_bitwise_style = hash_bitwise_style_by_stage.get(st.stage_idx, hash_bitwise_style_global)
                hash_xor_style = hash_xor_style_by_stage.get(st.stage_idx, hash_xor_style_global)
                const_v = layout.const_v[st.const]
                shift_v = layout.const_v[st.shift]
                _add_valu(
                    valu_ops,
                    st.shift_op,
                    tmp,
                    val,
                    shift_v,
                    meta={"round": r, "vec": v, "stage": "shift", "hash_stage": st.stage_idx},
                    offloadable=getattr(spec, "offload_hash_shift", False),
                )
                if st.op1 == "^" and st.op2 == "^" and hash_xor_style != "baseline":
                    if hash_xor_style == "swap":
                        # Same semantics, but swaps which XOR is tagged op1/op2 so budgets can target them.
                        _add_valu(
                            valu_ops,
                            "^",
                            val,
                            val,
                            tmp,
                            meta={"round": r, "vec": v, "stage": "op1", "hash_stage": st.stage_idx},
                            offloadable=getattr(spec, "offload_hash_op1", True),
                        )
                        _add_valu(
                            valu_ops,
                            "^",
                            val,
                            val,
                            const_v,
                            meta={"round": r, "vec": v, "stage": "op2", "hash_stage": st.stage_idx},
                            offloadable=getattr(spec, "offload_hash_op2", False),
                        )
                        continue
                    if hash_xor_style == "tmp_xor_const":
                        # Fold const-xor into the shifted temp; reduces WAW pressure on `val`.
                        _add_valu(
                            valu_ops,
                            "^",
                            tmp,
                            tmp,
                            const_v,
                            meta={"round": r, "vec": v, "stage": "op1", "hash_stage": st.stage_idx},
                            offloadable=getattr(spec, "offload_hash_op1", True),
                        )
                        _add_valu(
                            valu_ops,
                            "^",
                            val,
                            val,
                            tmp,
                            meta={"round": r, "vec": v, "stage": "op2", "hash_stage": st.stage_idx},
                            offloadable=getattr(spec, "offload_hash_op2", False),
                        )
                        continue
                if hash_bitwise_style == "inplace":
                    _add_valu(
                        valu_ops,
                        st.op1,
                        val,
                        val,
                        const_v,
                        meta={"round": r, "vec": v, "stage": "op1", "hash_stage": st.stage_idx},
                        offloadable=getattr(spec, "offload_hash_op1", True),
                    )
                    _add_valu(
                        valu_ops,
                        st.op2,
                        val,
                        val,
                        tmp,
                        meta={"round": r, "vec": v, "stage": "op2", "hash_stage": st.stage_idx},
                        offloadable=getattr(spec, "offload_hash_op2", False),
                    )
                else:
                    tmp_op1 = sel
                    _add_valu(
                        valu_ops,
                        st.op1,
                        tmp_op1,
                        val,
                        const_v,
                        meta={"round": r, "vec": v, "stage": "op1", "hash_stage": st.stage_idx},
                        offloadable=getattr(spec, "offload_hash_op1", True),
                    )
                    _add_valu(
                        valu_ops,
                        st.op2,
                        val,
                        tmp_op1,
                        tmp,
                        meta={"round": r, "vec": v, "stage": "op2", "hash_stage": st.stage_idx},
                        offloadable=getattr(spec, "offload_hash_op2", False),
                    )
        elif hash_variant == "prog":
            # Execute a custom hash program over (val, tmp, tmp2).
            def _resolve_src(src):
                if isinstance(src, int):
                    return layout.const_v[src]
                if src == "val":
                    return val
                if src == "tmp":
                    return tmp
                if src == "tmp2":
                    return sel
                raise ValueError(f"unknown hash_prog src {src!r}")

            def _resolve_dst(dst):
                if dst == "val":
                    return val
                if dst == "tmp":
                    return tmp
                if dst == "tmp2":
                    return sel
                raise ValueError(f"unknown hash_prog dst {dst!r}")

            for inst in hash_prog:
                op = inst.get("op")
                dst = _resolve_dst(inst.get("dst"))
                stage = inst.get("stage") or inst.get("tag")
                if stage is None and op in {"<<", ">>"}:
                    stage = "shift"
                meta = {"round": r, "vec": v}
                if stage is not None:
                    meta["stage"] = stage
                offloadable = False
                if stage == "shift":
                    offloadable = bool(getattr(spec, "offload_hash_shift", False))
                elif stage == "op1":
                    offloadable = bool(getattr(spec, "offload_hash_op1", False))
                elif stage == "op2":
                    offloadable = bool(getattr(spec, "offload_hash_op2", False))

                if op == "muladd":
                    a = _resolve_src(inst.get("a"))
                    b = _resolve_src(inst.get("b"))
                    c = _resolve_src(inst.get("c"))
                    _add_vmuladd(valu_ops, dst, a, b, c, meta=meta)
                elif op == "mov":
                    a = _resolve_src(inst.get("a"))
                    _add_valu(valu_ops, "+", dst, a, layout.const_v[0], meta=meta, offloadable=offloadable)
                else:
                    a = _resolve_src(inst.get("a"))
                    b = _resolve_src(inst.get("b"))
                    _add_valu(valu_ops, op, dst, a, b, meta=meta, offloadable=offloadable)
        else:
            lin_i = 0
            bit_i = 0
            for stage_idx, (op1, _, op2, op3, _) in enumerate(HASH_STAGES):
                if op1 == "+" and op2 == "+":
                    stage = linear[lin_i]
                    lin_i += 1
                    mult_v = layout.const_v[stage.mult]
                    add_v = layout.const_v[stage.add]
                    _add_vmuladd(valu_ops, val, val, mult_v, add_v, meta={"round": r, "vec": v, "stage": "linear"})
                else:
                    stage = bitwise[bit_i]
                    bit_i += 1
                    hash_bitwise_style = hash_bitwise_style_by_stage.get(stage_idx, hash_bitwise_style_global)
                    hash_xor_style = hash_xor_style_by_stage.get(stage_idx, hash_xor_style_global)
                    const_v = layout.const_v[stage.const]
                    shift_v = layout.const_v[stage.shift]
                    _add_valu(
                        valu_ops,
                        stage.shift_op,
                        tmp,
                        val,
                        shift_v,
                        meta={"round": r, "vec": v, "stage": "shift"},
                        offloadable=getattr(spec, "offload_hash_shift", False),
                    )
                    if stage.op1 == "^" and stage.op2 == "^" and hash_xor_style != "baseline":
                        if hash_xor_style == "swap":
                            _add_valu(
                                valu_ops,
                                "^",
                                val,
                                val,
                                tmp,
                                meta={"round": r, "vec": v, "stage": "op1"},
                                offloadable=getattr(spec, "offload_hash_op1", True),
                            )
                            _add_valu(
                                valu_ops,
                                "^",
                                val,
                                val,
                                const_v,
                                meta={"round": r, "vec": v, "stage": "op2"},
                                offloadable=getattr(spec, "offload_hash_op2", False),
                            )
                            continue
                        if hash_xor_style == "tmp_xor_const":
                            _add_valu(
                                valu_ops,
                                "^",
                                tmp,
                                tmp,
                                const_v,
                                meta={"round": r, "vec": v, "stage": "op1"},
                                offloadable=getattr(spec, "offload_hash_op1", True),
                            )
                            _add_valu(
                                valu_ops,
                                "^",
                                val,
                                val,
                                tmp,
                                meta={"round": r, "vec": v, "stage": "op2"},
                                offloadable=getattr(spec, "offload_hash_op2", False),
                            )
                            continue
                    if hash_bitwise_style == "inplace":
                        _add_valu(
                            valu_ops,
                            stage.op1,
                            val,
                            val,
                            const_v,
                            meta={"round": r, "vec": v, "stage": "op1"},
                            offloadable=getattr(spec, "offload_hash_op1", True),
                        )
                        _add_valu(
                            valu_ops,
                            stage.op2,
                            val,
                            val,
                            tmp,
                            meta={"round": r, "vec": v, "stage": "op2"},
                            offloadable=getattr(spec, "offload_hash_op2", False),
                        )
                    else:
                        # SSA-ish lowering: avoid writing to `val` twice in one stage.
                        # This preserves semantics but can improve scheduling by reducing WAW pressure.
                        tmp_op1 = sel
                        _add_valu(
                            valu_ops,
                            stage.op1,
                            tmp_op1,
                            val,
                            const_v,
                            meta={"round": r, "vec": v, "stage": "op1"},
                            offloadable=getattr(spec, "offload_hash_op1", True),
                        )
                        _add_valu(
                            valu_ops,
                            stage.op2,
                            val,
                            tmp_op1,
                            tmp,
                            meta={"round": r, "vec": v, "stage": "op2"},
                            offloadable=getattr(spec, "offload_hash_op2", False),
                        )

        # Index update
        one_v = layout.const_v[1]
        two_v = layout.const_v[2]
        if r == 10:
            if spec.reset_on_valu:
                _add_valu(valu_ops, "^", idx, idx, idx, meta={"round": r, "vec": v})
                if getattr(spec, "idx_shifted", False) and not getattr(
                    spec, "proof_reset_single_op", False
                ):
                    _add_valu(valu_ops, "+", idx, idx, one_v, meta={"round": r, "vec": v})
            else:
                reset_v = one_v if getattr(spec, "idx_shifted", False) else layout.const_v[0]
                _add_vselect(
                    flow_ops,
                    idx,
                    one_v,
                    reset_v,
                    idx,
                    meta={"round": r, "vec": v, "reset": "flow"},
                )
        elif r != 15:
            if getattr(spec, "idx_shifted", False):
                # idx = idx * 2 + (val & 1)
                _add_valu(
                    valu_ops,
                    "&",
                    tmp,
                    val,
                    one_v,
                    meta={"round": r, "vec": v},
                    offloadable=getattr(spec, "offload_parity", False),
                )
                _add_vmuladd(valu_ops, idx, idx, two_v, tmp, meta={"round": r, "vec": v})
            else:
                _add_valu(
                    valu_ops,
                    "&",
                    tmp,
                    val,
                    one_v,
                    meta={"round": r, "vec": v},
                    offloadable=getattr(spec, "offload_parity", False),
                )
                _add_valu(valu_ops, "+", tmp, tmp, one_v, meta={"round": r, "vec": v})
                _add_vmuladd(valu_ops, idx, idx, two_v, tmp, meta={"round": r, "vec": v})

    # Final stores
    for v in range(spec.vectors):
        _add_vstore(store_ops, layout.val_ptr[v], layout.val[v], meta={"vec": v})

    _ORDERED_OPS = None
    _USE_VALU_SELECT = False
    _VALU_SELECT_ROUNDS = None
    _VALU_OPS_REF = None
    return OpLists(valu_ops=valu_ops, alu_ops=alu_ops, flow_ops=flow_ops, load_ops=load_ops, store_ops=store_ops)
