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
    if getattr(spec, "use_bitmask_selection", False):
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

    # Scalar consts: pointer slots + masks + hash constants
    for v in (0, 1, 2, 4, 5, 6, 8, VLEN):
        reserve_const(v)

    # Vector consts needed for hash + shifts; small masks as needed.
    vec_consts = {1, 2}
    for op1, val1, op2, op3, val3 in HASH_STAGES:
        if op1 == "+" and op2 == "+":
            mult = (1 + (1 << val3)) % (2**32)
            vec_consts.add(mult)
            vec_consts.add(val1)
        else:
            vec_consts.add(val1)
            vec_consts.add(val3)

    for v in sorted(vec_consts):
        reserve_const(v)
        reserve_vconst(v)

    # Scalar node indices for ALU equality selection (1..30)
    for v in range(1, 31):
        reserve_const(v)

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
        forest_values_p=forest_values_p,
        forest_values_v=forest_values_v,
        inp_indices_p=inp_indices_p,
        inp_values_p=inp_values_p,
        node_tmp=node_tmp,
        const_s=const_s,
        const_v=const_v,
    )
