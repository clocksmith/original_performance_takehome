from __future__ import annotations

from dataclasses import dataclass

from problem import HASH_STAGES, SCRATCH_SIZE, VLEN


class ScratchAlloc:
    def __init__(self, limit: int = SCRATCH_SIZE):
        self.ptr = 0
        self.limit = limit
        self.map: dict[str, int] = {}

    def alloc(self, name: str, length: int = 1) -> int:
        addr = self.ptr
        self.map[name] = addr
        self.ptr += length
        if self.ptr > self.limit:
            raise RuntimeError(f"scratch overflow: {self.ptr} > {self.limit}")
        return addr


@dataclass(frozen=True)
class Layout:
    val: list[int]
    idx: list[int]
    tmp: list[int]
    tmp2: list[int]
    sel: list[int]
    extra: list[int]
    idx_ptr: list[int]
    val_ptr: list[int]
    node_v: list[int]
    node_diff_v: dict[tuple[int, int], int] # (a_addr, b_addr) -> diff_addr
    node_fused_v: list[int] # node_v[i] ^ C5
    forest_values_p: int
    forest_values_v: int
    inp_indices_p: int
    inp_values_p: int
    node_tmp: int
    const_s: dict[int, int]
    const_v: dict[int, int]


def build_layout(spec, scratch: ScratchAlloc) -> Layout:
    n_vecs = spec.vectors
    val = [scratch.alloc(f"val_{i}", VLEN) for i in range(n_vecs)]
    idx = [scratch.alloc(f"idx_{i}", VLEN) for i in range(n_vecs)]
    tmp = [scratch.alloc(f"tmp_{i}", VLEN) for i in range(n_vecs)]
    tmp2 = [scratch.alloc(f"tmp2_{i}", VLEN) for i in range(n_vecs)]
    sel = tmp2

    extra: list[int] = []
    selection_mode = getattr(spec, "selection_mode", None)
    if selection_mode is None:
        selection_mode = "bitmask" if getattr(spec, "use_bitmask_selection", False) else "eq"
    per_round_modes = getattr(spec, "selection_mode_by_round", None) or {}
    needs_extra = selection_mode in {"bitmask", "bitmask_valu", "mask", "mask_precompute"}
    if any(m in {"bitmask", "bitmask_valu", "mask", "mask_precompute"} for m in per_round_modes.values()):
        needs_extra = True
    if needs_extra:
        extra_vecs = getattr(spec, "extra_vecs", 1)
        extra = [scratch.alloc(f"extra_{i}", VLEN) for i in range(extra_vecs)]

    idx_ptr = [scratch.alloc(f"idx_ptr_{i}") for i in range(n_vecs)]
    val_ptr = [scratch.alloc(f"val_ptr_{i}") for i in range(n_vecs)]

    # Base pointers (scalar)
    forest_values_p = scratch.alloc("forest_values_p")
    forest_values_v = scratch.alloc("forest_values_v", VLEN)
    inp_indices_p = scratch.alloc("inp_indices_p")
    inp_values_p = scratch.alloc("inp_values_p")
    node_tmp = scratch.alloc("node_tmp")

    # Cached nodes as vectors. Allow an override for smaller caches (e.g. top-3).
    node_cache = getattr(spec, "cached_nodes", None)
    if node_cache is None:
        node_cache = 31
        if getattr(spec, "depth4_rounds", 0) == 0 and getattr(spec, "x5", 0) == 0:
            node_cache = 15
    node_v = [scratch.alloc(f"node_v_{i}", VLEN) for i in range(node_cache)]
    
    # Node differences for fast VALU selection.
    # These cost scratch (VLEN words each). For large node caches (e.g. depth4),
    # we sometimes need to disable diff precompute to fit in SCRATCH_SIZE.
    node_diff_v = {}
    if (
        (getattr(spec, "valu_select", False) or getattr(spec, "valu_select_leaf_pairs", False))
        and bool(getattr(spec, "valu_select_precompute_diffs", True))
    ):
        # We only need diffs for the pairs used in vselect_parity (Level 1-4)
        # Pairs are (2,1), (4,3), (6,5), (8,7), (10,9), (12,11), (14,13), etc.
        for i in range(2, node_cache + 1, 2):
            if i < len(node_v):
                addr_a = node_v[i]
                addr_b = node_v[i-1]
                diff_addr = scratch.alloc(f"node_diff_{i}_{i-1}", VLEN)
                node_diff_v[(addr_a, addr_b)] = diff_addr

    # Node fused with Stage 5 constant
    node_fused_v = []
    if getattr(spec, "fuse_stages", False):
        for i in range(node_cache):
            node_fused_v.append(scratch.alloc(f"node_fused_{i}", VLEN))

    # Constants (scalar + vector)
    const_s: dict[int, int] = {}
    const_v: dict[int, int] = {}

    def reserve_const(val: int) -> int:
        if val not in const_s:
            const_s[val] = scratch.alloc(f"const_{val}")
        return const_s[val]

    def reserve_vconst(val: int) -> int:
        if val not in const_v:
            const_v[val] = scratch.alloc(f"vconst_{val}", VLEN)
        return const_v[val]

    # Scalar consts: pointer slots + masks + hash constants.
    base_consts = {0, 1, 2, 4, 5, 6, 8, 10, 12, 14, 31, VLEN}
    if getattr(spec, "use_bitmask_selection", False):
        # Bitmask selection thresholds (depth3) require 11 and 13.
        base_consts.update({11, 13})
    for v in sorted(base_consts):
        reserve_const(v)

    # Vector consts needed for hash + shifts; small masks as needed.
    vec_consts = {1, 2}
    if not getattr(spec, "reset_on_valu", True) and not getattr(spec, "idx_shifted", False):
        vec_consts.add(0)
    if selection_mode in {"mask", "mask_precompute", "bitmask_valu"} or any(
        m in {"mask", "mask_precompute", "bitmask_valu"} for m in per_round_modes.values()
    ):
        vec_consts.add(3)
    hash_variant = getattr(spec, "hash_variant", "direct")
    if hash_variant == "prog":
        # Ensure const-0 is available for mov-style ops and collect program constants.
        vec_consts.add(0)
        prog = getattr(spec, "hash_prog", None)
        if not prog:
            preset = str(getattr(spec, "hash_prog_variant", "none") or "none")
            if preset != "none":
                from .hash_prog_presets import build_hash_prog_preset

                prog = build_hash_prog_preset(preset)
        prog = prog or []
        for inst in prog:
            for key in ("a", "b", "c"):
                imm = inst.get(key)
                if isinstance(imm, int):
                    vec_consts.add(imm)
    hash_linear_style = getattr(spec, "hash_linear_style", "muladd")
    for op1, val1, op2, op3, val3 in HASH_STAGES:
        if op1 == "+" and op2 == "+":
            mult = (1 + (1 << val3)) % (2**32)
            vec_consts.add(mult)
            vec_consts.add(val1)
            if hash_linear_style == "shift_add":
                vec_consts.add(val3)
        else:
            vec_consts.add(val1)
            vec_consts.add(val3)

    for v in sorted(vec_consts):
        reserve_const(v)
        reserve_vconst(v)

    # Scalar node indices for cached-node address setup (needed unless using incremental pointer preload).
    if not getattr(spec, "node_ptr_incremental", False):
        node_const_max = node_cache + (1 if getattr(spec, "idx_shifted", False) else 0)
        for v in range(node_const_max):
            reserve_const(v)

    # Scalar node indices for ALU equality selection (conditional).
    #
    # IMPORTANT: Even if the global selection mode is bitmask, some rounds may
    # override to "eq" via selection_mode_by_round (e.g. the 1291 kernel does
    # this for rounds 11-14). Those rounds still need scalar node-index consts.
    use_bitmask = getattr(spec, "use_bitmask_selection", False)
    depth4_rounds = getattr(spec, "depth4_rounds", 0)
    x4 = getattr(spec, "x4", 0)
    depth4_bitmask = use_bitmask and getattr(spec, "extra_vecs", 1) >= 3

    selection_mode_by_round = getattr(spec, "selection_mode_by_round", None) or {}
    selection_mode = getattr(spec, "selection_mode", None)
    needs_eq_consts = (selection_mode == "eq") or any(
        m == "eq" for m in selection_mode_by_round.values()
    )
    if needs_eq_consts:
        # For idx_shifted=True, eq-selection compares against (node_idx+1),
        # so we need consts up to 15 (for node_idx=14).
        hi = 16 if getattr(spec, "idx_shifted", False) else 15
        for v in range(1, hi):
            reserve_const(v)
    if depth4_rounds and x4 > 0 and not depth4_bitmask:
        for v in range(15, 31):
            reserve_const(v)
    if depth4_bitmask and depth4_rounds and x4 > 0:
        # Depth4 bitmask thresholds.
        for v in (17, 19, 21, 23, 25, 27, 29):
            reserve_const(v)
            if getattr(spec, "idx_shifted", False):
                reserve_const(v + 1)

    return Layout(
        val=val,
        idx=idx,
        tmp=tmp,
        tmp2=tmp2,
        sel=sel,
        extra=extra,
        idx_ptr=idx_ptr,
        val_ptr=val_ptr,
        node_v=node_v,
        node_diff_v=node_diff_v,
        node_fused_v=node_fused_v,
        forest_values_p=forest_values_p,
        forest_values_v=forest_values_v,
        inp_indices_p=inp_indices_p,
        inp_values_p=inp_values_p,
        node_tmp=node_tmp,
        const_s=const_s,
        const_v=const_v,
    )
