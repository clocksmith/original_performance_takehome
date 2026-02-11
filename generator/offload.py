from __future__ import annotations

from dataclasses import dataclass

from problem import VLEN

from .ops import Op, OpLists


@dataclass
class OffloadedOps:
    valu_ops: list[Op]
    alu_ops: list[Op]
    flow_ops: list[Op]
    load_ops: list[Op]
    store_ops: list[Op]

def _offload_category(op: Op) -> str | None:
    meta = op.meta or {}
    stage = meta.get("stage")
    if stage == "shift":
        return "hash_shift"
    if stage == "op1":
        return "hash_op1"
    if stage == "op2":
        return "hash_op2"
    # Non-hash offloadables (parity/node_xor) don't carry a stage tag today.
    if op.engine == "valu":
        op_name = op.slot[0]
        if op_name == "&":
            return "parity"
        if op_name == "^":
            return "node_xor"
    return None


def apply_offload_stream(spec, ops: list[Op]) -> list[Op]:
    """
    Apply vector->scalar offload to an in-order op stream.

    This must stay in sync with scripts/graph_dp_auto_search.build_final_ops and
    generator/build_kernel_base.build_base_instrs so energy_search scores match
    real kernels.
    """
    mode = getattr(spec, "offload_mode", "prefix")
    if mode not in {"prefix", "budgeted", "budgeted_spread"}:
        raise ValueError(f"unknown offload_mode {mode!r}")

    budgets = {
        "hash_shift": int(getattr(spec, "offload_budget_hash_shift", 0)),
        "hash_op1": int(getattr(spec, "offload_budget_hash_op1", 0)),
        "hash_op2": int(getattr(spec, "offload_budget_hash_op2", 0)),
        "parity": int(getattr(spec, "offload_budget_parity", 0)),
        "node_xor": int(getattr(spec, "offload_budget_node_xor", 0)),
    }
    used = {k: 0 for k in budgets}

    offload_prefix_cap = int(getattr(spec, "offload_op1", 0))
    offloaded_prefix = 0

    offload_idxs: set[int] | None = None
    if mode == "budgeted_spread":
        # Precompute which op indices to offload so that the (typically small)
        # set of *non-offloaded* ops in a category is distributed across the
        # stream instead of being clustered at the end (which can create a VALU
        # tail and hurt scheduling).
        per_cat: dict[str, list[int]] = {k: [] for k in budgets}
        for i, op in enumerate(ops):
            if not op.offloadable:
                continue
            cat = _offload_category(op)
            if cat is None:
                continue
            if cat not in per_cat:
                continue
            per_cat[cat].append(i)

        offload_idxs = set()
        for cat, idxs in per_cat.items():
            cap = int(budgets.get(cat, 0))
            if cap <= 0 or not idxs:
                continue
            n = len(idxs)
            if cap >= n:
                offload_idxs.update(idxs)
                continue
            keep = n - cap
            if keep <= 0:
                offload_idxs.update(idxs)
                continue
            # Choose `keep` indices spaced across [0..n-1] (inclusive endpoints).
            keep_set: set[int] = set()
            if keep == 1:
                keep_set.add(idxs[n // 2])
            else:
                for k in range(keep):
                    j = (k * (n - 1)) // (keep - 1)
                    keep_set.add(idxs[j])
            for i in idxs:
                if i not in keep_set:
                    offload_idxs.add(i)

    out: list[Op] = []
    offload_alu_vec = bool(getattr(spec, "offload_alu_vec", False))
    for i, op in enumerate(ops):
        do_offload = False
        if op.offloadable:
            if mode == "prefix":
                do_offload = offloaded_prefix < offload_prefix_cap
            elif mode == "budgeted":
                cat = _offload_category(op)
                if cat is not None:
                    cap = budgets.get(cat, 0)
                    do_offload = used[cat] < cap
                    if do_offload:
                        used[cat] += 1
            else:
                assert mode == "budgeted_spread"
                do_offload = offload_idxs is not None and i in offload_idxs

        if not do_offload:
            out.append(op)
            continue

        # Expand to scalar ALU ops (one per lane). This is the canonical
        # lowering used by the current best kernels.
        #
        # When offload_alu_vec=True, we instead emit a single pseudo op
        # ("alu_vec", ...) which the scheduler accounts as VLEN ALU slots and
        # is expanded back into scalar slots when emitting bundles.
        #
        # NOTE: Only supports binary vector ops: (op, dest, a, b).
        op_name, dest, a, b = op.slot
        meta2 = dict(op.meta or {})
        meta2["offload"] = True
        if offload_alu_vec:
            out.append(Op(engine="alu", slot=("alu_vec", op_name, dest, a, b), meta=meta2))
        else:
            for lane in range(VLEN):
                out.append(
                    Op(
                        engine="alu",
                        slot=(op_name, dest + lane, a + lane, b + lane),
                        meta=meta2,
                    )
                )
        offloaded_prefix += 1

    return out


def apply_offload(spec, ops: OpLists) -> OffloadedOps:
    alu_ops: list[Op] = list(ops.alu_ops)
    valu_ops: list[Op] = []

    offloaded = 0
    offload_alu_vec = bool(getattr(spec, "offload_alu_vec", False))
    for op in ops.valu_ops:
        if op.offloadable and offloaded < spec.offload_op1:
            op_name, dest, a, b = op.slot
            meta2 = dict(op.meta or {})
            meta2["offload"] = True
            if offload_alu_vec:
                alu_ops.append(Op(engine="alu", slot=("alu_vec", op_name, dest, a, b), meta=meta2))
            else:
                for lane in range(VLEN):
                    alu_ops.append(
                        Op(
                            engine="alu",
                            slot=(op_name, dest + lane, a + lane, b + lane),
                            meta=meta2,
                        )
                    )
            offloaded += 1
        else:
            valu_ops.append(op)

    return OffloadedOps(
        valu_ops=valu_ops,
        alu_ops=alu_ops,
        flow_ops=ops.flow_ops,
        load_ops=ops.load_ops,
        store_ops=ops.store_ops,
    )
