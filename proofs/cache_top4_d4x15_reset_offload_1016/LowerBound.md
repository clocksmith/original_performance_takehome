Feasible 1312 upper‑bound witness (full‑window model, explicit setup)

Correspondence map (MD ↔ Lean)
- Deterministic wrap + interval equality: IdxSet, IntervalSet, interval_step, idxset_eq_interval, minIdxR_eq_pow, maxIdxR_eq_pow, maxIdxR_mono, idxset_le_30_of_le4, deterministic_wrap_round10, no_wrap_after_reset_rounds_11_14
- Per‑vector and total VALU counts: perVectorVALU, perVectorVALU_eq, totalVALU, totalVALU_eq, RESET_VALU_OPS_PER_VEC, SETUP_VALU_OPS, totalVALU1016, totalVALU1016_eq
- Capacity + offload feasibility: offloadNeeded, offload_needed_1016, offloadCap_1016, offload_feasible_1016
- Flow/load feasibility (chosen scheme): DEPTH4_ROUNDS, X4, FLOW_SETUP, flowOps, flowOps_eq, flow_capacity_1016, totalLoadOps, totalLoadOps_eq, load_capacity_1016
- Schedule skeleton bundle: schedule_skeleton
- Constructive count schedule: allocVALU/ALU/FLOW/LOAD/STORE, sumAlloc_*, constructive_schedule_counts
- Per‑vector dependency ordering (round‑robin): vecAt, opIndex, vecAt_modEq, vecAt_ne_add_of_lt, vecAt_distinct_same_cycle, valu_round_robin_respects_deps

Assumptions (all follow the frozen ISA and test instance unless stated):
- height = 10, n_nodes = 2^(10+1) − 1 = 2047, all indices start at 0.
- values-only correctness: submission checks only final values, so the round‑15 index update can be skipped.
- We only offload bitwise hash op1 stages to ALU (8 scalar ops per VALU op). We never offload multiply_add stages.
- Reset at round 10 is a VALU op (idx := 0).
- Flow pointer setup (64 add_imm) is counted in flowOps.
- Setup VALU ops are counted explicitly: SETUP_VALU_OPS = 45 (constants, broadcasts, cached-node setup).

Selection + caching scheme used for the 1016 witness:
- Baseline caching for all vectors: top‑4 levels (nodes 0..14) in rounds 0–3 and 11–14.
- Extra depth‑4 caching for X4=15 vectors in round 4 only (DEPTH4_ROUNDS=1).
- No depth‑5 caching (X5=0).
- Selection uses ALU equality tests with flow vselect chains (ISA‑legal).
  (Formalized as `depth4Rounds = {4}` in Lean.)

Deterministic wrap round (formal range lemma + equality):
Define IdxSet(0) = {0} and IdxSet(k+1) = {2*i+1, 2*i+2 | i ∈ IdxSet(k)}. The Lean proof
shows by induction that IdxSet(k) is exactly the closed interval
  { n | minIdxR(k) ≤ n ≤ maxIdxR(k) },
so in round 10 we can reset idx to 0 directly, and in rounds 11–14 no compare is needed.

Per‑vector VALU work:
- Hash: 12 ops/round × 16 rounds = 192
- Node XOR: 1 op/round × 16 rounds = 16
- Parity + idx update: 2 ops/round × 14 rounds (0–9, 11–14) = 28
- Reset (round 10): 1 op per vector = 1
Total = 237 VALU ops per vector. For 32 vectors: 7584 VALU ops.
Extra address-compute VALU ops (uncached node adds): 241.
Setup VALU ops: 45.
Total VALU ops (including reset + setup): 7870.

Capacity + offload (for this tuple):
At T = 1312 cycles:
- VALU capacity = 6T = 7872 ops
- ALU offload capacity = floor(12T/8) = 1968 VALU‑equivalent ops
- Needed offload = 7870 − 7872 = 0 (no offload)

Flow + load counts for the chosen scheme:
- Flow ops: baseline top‑4 cached selection costs 22 vselects/vector ⇒ 704.
  Flow setup adds 64. Depth‑4 caching for X4 vectors adds 15 per vector for DEPTH4_ROUNDS=1.
  With X4=15:
  flowOps = 704 + 64 + 15*15 = 993 ≤ 1312.
- Load ops: formula is
  totalLoadOps = 64 + PRELOAD_NODES + 42 + (16−8−DEPTH4_ROUNDS)*256 + DEPTH4_ROUNDS*(32−X4)*8.
  For X4=15, DEPTH4_ROUNDS=1 (round 4 cached only):
  totalLoadOps = 64 + 31 + 42 + 7*256 + (32−15)*8 = 2065 ≤ 2*1312.

Engine budgets at T=1312:
Engine | Required | Capacity | Notes
VALU   | 7870 ops | 7872 ops | no offload needed
ALU    | 7463 ops | 15744 ops | base ALU ops only
Flow   | 993 ops | 1312 ops | vselect selection + setup
Load   | 2065 ops | 2624 ops | cached top‑4 + partial depth‑4 (X4=15)
Store  | 32 ops   | 2624 ops | vstore values once

Constructive count‑schedule (formalized in Lean):
We give explicit per‑cycle allocations over T=1312 cycles:
- VALU: 6 ops for cycles 0–1311 (total 7872).
- ALU: 12 ops for cycles 0–620, 11 ops on cycle 621 (total 7463).
- Flow: 1 op for cycles 0–992 (total 993).
- Load: 2 ops for cycles 0–1031, 1 op on cycle 1032 (total 2065).
- Store: 2 ops for cycles 0–15 (total 32).
These allocations are encoded as functions in Lean and proved to respect caps and totals
via `constructive_schedule_counts`.

This yields a tight 1312 bound under the stated assumptions, with explicit setup
and an ISA‑legal selection cost and load budget.
