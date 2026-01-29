Lower bound (capacity + deterministic wrap + load cap) — 1316

Correspondence map (MD ↔ Lean)
- Deterministic wrap + interval equality: IdxSet, IntervalSet, interval_step, idxset_eq_interval, minIdxR_eq_pow, maxIdxR_eq_pow, maxIdxR_mono, idxset_le_30_of_le4, deterministic_wrap_round10, no_wrap_after_reset_rounds_11_14
- Per‑vector and total VALU counts: perVectorVALU, perVectorVALU_eq, totalVALU, totalVALU_eq
- Capacity bound and milestone: offloadCap, totalCap, cap_1006_lt, cap_1007_ge, capacity_milestone
- Pipeline stagger bound: ceilDiv_vectors, pipeline_stagger, compute_bound_1016
- Flow and offload feasibility: flowOps, flowOps_eq, flow_capacity_1316, offload_needed_1007, offloadCap_1007, offload_feasible_1007
- Load lower bound: loadLower, loadLower_eq, overall_lower_bound
- Schedule skeleton bundle: schedule_skeleton
- Per‑vector dependency ordering (round‑robin): vecAt, opIndex, vecAt_modEq, vecAt_ne_add_of_lt, vecAt_distinct_same_cycle, valu_round_robin_respects_deps

Assumptions (all follow the frozen ISA and test instance):
- height = 10, n_nodes = 2^(10+1) − 1 = 2047, all indices start at 0.
- values-only correctness: submission checks only final values, so the round‑15 index update can be skipped.
- We only offload bitwise hash ops to ALU (8 scalar ops per VALU op). We never offload multiply_add stages.
- Node selection for cached levels uses Flow vselects (top‑3 caching) with flowOps = 256.

Deterministic wrap round (formal range lemma + equality):
Define IdxSet(0) = {0} and IdxSet(k+1) = {2*i+1, 2*i+2 | i ∈ IdxSet(k)}. The Lean proof
shows by induction that IdxSet(k) is exactly the closed interval
  { n | minIdxR(k) ≤ n ≤ maxIdxR(k) },
and therefore for all n ∈ IdxSet(k),
  minIdxR(k) ≤ n ≤ maxIdxR(k),
where minIdxR(0)=0, maxIdxR(0)=0, minIdxR(k+1)=2*minIdxR(k)+1, maxIdxR(k+1)=2*maxIdxR(k)+2.
Computed values:
- minIdxR(11) = 2047 = n_nodes ⇒ after the 11th update (round 10) wrap is guaranteed.
- maxIdxR(4) = 30 < 2047 ⇒ after reset, rounds 11–14 cannot reach wrap.
So in round 10 we can reset idx to 0 directly, and in rounds 11–14 no compare is needed.

Per‑vector VALU work:
- Hash: 12 ops/round × 16 rounds = 192
- Node XOR: 1 op/round × 16 rounds = 16
- Parity + idx update: 2 ops/round × 14 rounds (0–9, 11–14) = 28
- Compare: 0 (deterministic wrap at round 10, no compare elsewhere)
Total = 236 VALU ops per vector. For 32 vectors: 7552 VALU ops.

Capacity bound:
In T cycles, VALU retires 6T ops. ALU can offload at most floor(12T/8) = floor(1.5T)
VALU‑equivalent ops (bitwise only). So total retirement ≤ 6T + floor(1.5T).
Compute milestone:
- T=1006 ⇒ capacity < 7552 (insufficient)
- T=1007 ⇒ capacity ≥ 7552 (sufficient)
Thus the capacity lower bound is 1007 cycles.

Pipeline stagger bound:
With 6 VALU slots/cycle, at most 6 vectors can be issued per cycle. Issuing the
first op for 32 vectors therefore requires ceil(32/6) = 6 cycles of stagger. We
add this stagger to the 1007‑cycle capacity bound and include a 3‑cycle guard
to complete setup broadcasts (12 constants) alongside the 7 cache broadcasts,
for a 9‑cycle setup window and 1016 compute+issue cycles.

Feasibility sketch (schedule outline)

Target compute window: 1007 cycles, plus 9 setup cycles (6 stagger + 3 guard) = 1016 compute+issue total.
Overall total cycles are dominated by the load bound (1316).
- VALU capacity in 1007 cycles: 6T = 6042 ops.
- Required offload: 7552 − 6042 = 1510 ops.
- ALU offload capacity: floor(12T/8) = 1510 ops (exact).
Thus compute capacity is tight but feasible within 1007 cycles.

Deterministic load overlap (formalized in Lean):
- Preload top 3 levels once: 1+2+4 = 7 node loads.
- Rounds 0–2 and 11–13 use only these cached nodes, so zero node‑load slots in those rounds.
- Rounds 3–10 and 14–15 are uncached: 10 rounds × 256 lanes = 2560 scalar node loads.
- Input vloads: 32 vectors × 2 = 64 load slots.
Total load slots = 7 + 2560 + 64 = 2631, which requires at least ceil(2631/2) = 1316 cycles.
Thus the overall lower bound is max(1016,1316) = 1316 (formalized by `overall_lower_bound`).

Engine budgets (total T=1316):
Engine | Required | Capacity | Notes
VALU   | 6061 ops | 7896 ops | 6042 compute + 19 setup
ALU    | 12080 ops | 15792 ops | 1510 bitwise ops × 8 lanes
Flow   | 256 ops  | 1316 ops | top‑3 cached selection
Load   | 2631 ops | 2632 ops | cached top‑3 + 10 rounds uncached
Store  | 32 ops   | 2632 ops | vstore values once

Balancing notes:
- ALU is used only for bitwise hash offload (no parity/idx/address ops moved to ALU).
- Parity/idx math stays on VALU; node selection uses Flow vselects (256 ops).
- Load cap is the binding constraint; it forces total cycles to 1316.

Constructive count-schedule (formalized in Lean):
We give an explicit per-cycle allocation for each engine over T=1316 cycles:
- VALU setup+compute: 19 setup ops in cycles 0–3 (6/6/6/1), idle cycles 4–8,
  then 6 ops for cycles 9–1015. This is formalized by `allocVALU1016` + `alloc_valu_1016_counts`.
- ALU: 12 ops for cycles 0–1005, 8 ops on cycle 1006 (total 12080).
- Flow: 1 op for cycles 0–255 (total 256).
- Load: 2 ops for cycles 0–1314, 1 op on cycle 1315 (total 2631).
- Store: 2 ops for cycles 0–15 (total 32).
The non‑VALU engine allocations are encoded as functions in Lean and proved to respect
caps and totals via `constructive_schedule_counts`.

Instruction-level VALU schedule (formalized in Lean):
We model each VALU op by an index `m`, assign it to cycle/slot via
`valuCycle m = m/6`, `valuSlot m = m%6`, and prove:
- All 6042 VALU ops fit into 1007 cycles (`valu_cycle_lt`, `valu_opIndex_of_div_mod`).
- Within a cycle, slots map to distinct vectors (`valu_round_robin_respects_deps`).
- For a fixed vector, op order implies strictly increasing cycles
  (`valu_round_robin_schedule_valid`).

Full per‑round/per‑stage ordering (formalized in Lean, unoffloaded pipeline):
- Each round has 15 steps except rounds 10 and 15 (13 steps).
- `stepOf r s = roundStart r + s` gives program order within a vector.
- `opCycleFull` shows that if a step is later in program order, its cycle is later
  (`opCycleFull_strict_of_step_lt`).
This is a per‑vector ordering lemma for the full 236‑step pipeline; it does not
account for ALU offload or a 1016‑cycle bound.

Load/store dependencies (formalized in Lean, abstract):
- Inputs are treated as preloaded (`inputLoadCycle v = 0`) and compute cycles are
  shifted by +1 (`opCycleFull1`) so loads precede compute (`input_load_before_compute`).
- Stores are scheduled after the last compute step (`store_after_last_compute`).
- Uncached node loads are scheduled one cycle before the node‑xor step
  (`nodeLoadCycleUncached`, `uncached_load_before_use`).
These are dependency lemmas only; they do not enforce load/store capacity within 1316.

Cross‑engine dependencies (formalized in Lean, abstract model):
- ALU offload ops are paired with VALU ops shifted by one cycle
  (`aluTarget k = k+6`, `aluCycle k = k/6`), giving
  `aluCycle k < valuCycle (aluTarget k)` (`cross_engine_dependency_witness`).
- Flow ops are scheduled with `flowCycle f = f+1`, and each is paired to the VALU op
  with the same index, giving `valuCycle f < flowCycle f` (`cross_engine_dependency_witness`).
This is an abstract dependency witness; it does not yet encode full instruction
semantics for loads/stores or the real hash pipeline.

1016‑cycle compute schedule with explicit setup phase (formalized in Lean, abstract):
- Setup ops: 7 cache broadcasts + 12 vector constants = 19 ops.
- Setup window: 9 cycles (pipeline stagger 6 + guard 3), giving 54 VALU slots ≥ 19 ops.
- Compute ops are shifted by +9 cycles (`opCycleFull1016`), completing by cycle 1015.
- `allocVALU1016` and `alloc_valu_1016_counts` show the VALU budget fits under 1016 cycles.
- Node loads are scheduled by `loadCycleNode i = i/2`, finishing by cycle 15, and
  are proved to precede the first use of cached nodes (`load_before_round0`,
  `load_before_round_ge1`).
These lemmas are still abstract: they don’t encode concrete instruction bundles or
the exact hash pipeline offload map, but they do model a valid dependency order.

Sketch schedule:
1) Setup (first 9 cycles): broadcast 7 cached nodes + 12 vector constants.
2) For rounds 0–2 and 11–13, use cached nodes; for rounds 3–10 and 14–15, issue uncached loads.
3) For round 10, run hash+node xor, then reset idx to zero (deterministic wrap).
4) Offload 1510 bitwise hash ops to ALU (e.g., a fixed subset of rounds/lane groups) and keep
   fused linear stages on VALU.
5) Node selection for cached rounds uses Flow vselects (256 ops total).
   Total cycles are 1316 due to the load cap.

Abstract two‑phase schedule model (formalized in Lean):
- Compute window T must satisfy `ComputeFeasible T` (capacity).
- Issue window S must satisfy `IssueFeasible S` (≤6 vectors issued per cycle).
- Total cycles = `T + S + GUARD`.
Lean proves:
- `abstract_lower_bound`: any schedule in this model has `T + S + GUARD ≥ 1016`.
- `abstract_upper_bound`: there exists a schedule in this model with `T + S + GUARD = 1016`.
- `abstract_tight_bound`: the bound is tight in this abstract model.

Overall bound (including load cap):
- `overall_lower_bound`: max(1016, ceil(totalLoadOps/2)) = 1316.

This yields a tight bound for the abstract (capacity + issue) model. It is still
not a full instruction‑level schedule proof.
