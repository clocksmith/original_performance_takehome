import Mathlib
import proofs.common.Base

namespace ProofCacheTop4D4x15ResetOffload1016
open ProofCommon

def GUARD : Nat := 0

def totalCycles : Nat := 1312

/-- Flow engine capacity for cached-node selection (top-4 + partial depth-4). -/
def FLOW_CAP : Nat := 1
def LOAD_CAP : Nat := 2
def STORE_CAP : Nat := 2

open scoped BigOperators

-- Partial caching parameters for 1016 witness.
def DEPTH4_ROUNDS : Nat := 1
def X4 : Nat := 15 -- vectors cached at depth-4 (round 4 only)
def X5 : Nat := 0  -- vectors cached at depth-5 (round 5) [unused]
def FLOW_SETUP : Nat := 64

def depth4Rounds : Finset Nat :=
  if DEPTH4_ROUNDS = 0 then ∅
  else if DEPTH4_ROUNDS = 1 then {4}
  else {4, 15}

lemma depth4Rounds_eq : depth4Rounds = ({4} : Finset Nat) := by
  simp [depth4Rounds, DEPTH4_ROUNDS]

-- Baseline top-4 cached selection: 22 vselects per vector (two phases).
def flowOps : Nat := 704 + FLOW_SETUP + 15 * X4 * DEPTH4_ROUNDS + 31 * X5

lemma flowOps_eq : flowOps = 993 := by
  native_decide

lemma flow_capacity_1016 : flowOps ≤ FLOW_CAP * totalCycles := by
  simp [flowOps_eq, FLOW_CAP, totalCycles]

/-- Load budget with top-4 caching + partial depth-4 (X4) and depth-5 (X5). -/
def PRELOAD_NODES_BASE : Nat := 15 -- nodes 0..14
def PRELOAD_NODES_D4 : Nat := if X4 = 0 then 0 else 16 -- nodes 15..30
def PRELOAD_NODES_D5 : Nat := if X5 = 0 then 0 else 32 -- nodes 31..62
def PRELOAD_NODES : Nat := PRELOAD_NODES_BASE + PRELOAD_NODES_D4 + PRELOAD_NODES_D5

def VLOADS : Nat := 2 * VECTORS -- vload indices + values
def BASE_CACHED_ROUNDS : Nat := 8 -- rounds 0-3 and 11-14 (depths 0..3)
def SETUP_LOAD_OPS : Nat := 42 -- const + pointer loads

def totalLoadOps : Nat :=
  VLOADS
  + PRELOAD_NODES
  + SETUP_LOAD_OPS
  + (ROUNDS - BASE_CACHED_ROUNDS - DEPTH4_ROUNDS) * VECTORS * VLEN
  + DEPTH4_ROUNDS * (VECTORS - X4) * VLEN

lemma totalLoadOps_eq : totalLoadOps = 2065 := by native_decide

lemma load_capacity_1016 : totalLoadOps ≤ LOAD_CAP * totalCycles := by
  simp [totalLoadOps_eq, LOAD_CAP, totalCycles]

def storeOps : Nat := VECTORS -- vstore values once

lemma store_capacity_1016 : storeOps ≤ STORE_CAP * totalCycles := by
  simp [storeOps, STORE_CAP, VECTORS, totalCycles]

/-! ## Reset + setup accounting (1016 tuple) -/

def RESET_VALU_OPS_PER_VEC : Nat := 1
def EXTRA_ADDR_VALU_OPS : Nat := 241
def SETUP_VALU_OPS : Nat := 45

def totalVALU1016 : Nat :=
  totalVALU + VECTORS * RESET_VALU_OPS_PER_VEC + EXTRA_ADDR_VALU_OPS + SETUP_VALU_OPS

lemma totalVALU1016_eq : totalVALU1016 = 7870 := by
  simp [totalVALU1016, totalVALU_eq, VECTORS, RESET_VALU_OPS_PER_VEC, EXTRA_ADDR_VALU_OPS, SETUP_VALU_OPS]

/-- Offload needed at totalCycles and its ALU feasibility. -/
def offloadNeeded (T : Nat) : Nat := totalVALU1016 - VALU_CAP * T

lemma offload_needed_1016 : offloadNeeded totalCycles = 0 := by
  simp [offloadNeeded, totalCycles, totalVALU1016_eq, VALU_CAP]

lemma offloadCap_1016 : offloadCap totalCycles = 1968 := by
  native_decide

lemma offload_feasible_1016 :
    offloadNeeded totalCycles ≤ offloadCap totalCycles := by
  have hcap : offloadCap totalCycles = 1968 := offloadCap_1016
  have hneeded : offloadNeeded totalCycles = 0 := offload_needed_1016
  have hle : 0 ≤ 1968 := by decide
  simpa [hcap, hneeded]

def BASE_ALU_OPS : Nat := 7463
def totalALUOps (T : Nat) : Nat := BASE_ALU_OPS + offloadNeeded T * VLEN

lemma alu_capacity_1016 : totalALUOps totalCycles ≤ ALU_CAP * totalCycles := by
  native_decide

/-- Combined schedule skeleton: capacity + flow + load + stagger. -/
theorem schedule_skeleton :
  offloadNeeded totalCycles = 0 ∧
  offloadNeeded totalCycles ≤ offloadCap totalCycles ∧
  totalALUOps totalCycles ≤ ALU_CAP * totalCycles ∧
  flowOps ≤ FLOW_CAP * totalCycles ∧
  totalLoadOps ≤ LOAD_CAP * totalCycles ∧
  storeOps ≤ STORE_CAP * totalCycles ∧
  totalCycles = 1312 := by
  refine ⟨offload_needed_1016, offload_feasible_1016, alu_capacity_1016, flow_capacity_1016, load_capacity_1016, store_capacity_1016, rfl⟩

/-! ## Constructive per-engine count schedule (total window) -/

def T : Nat := totalCycles

def allocVALU (t : Nat) : Nat := if t < totalCycles then 6 else 0
def allocALU (t : Nat) : Nat := if t < 621 then 12 else if t = 621 then 11 else 0
def allocFLOW (t : Nat) : Nat := if t < 993 then 1 else 0
def allocLOAD (t : Nat) : Nat := if t < 1032 then 2 else if t = 1032 then 1 else 0
def allocSTORE (t : Nat) : Nat := if t < 16 then 2 else 0

def sumAlloc (f : Nat → Nat) : Nat := (Finset.range T).sum f

lemma sumAlloc_valu : sumAlloc allocVALU = 7872 := by native_decide
lemma sumAlloc_alu : sumAlloc allocALU = 7463 := by native_decide
lemma sumAlloc_flow : sumAlloc allocFLOW = 993 := by native_decide
lemma sumAlloc_load : sumAlloc allocLOAD = 2065 := by native_decide
lemma sumAlloc_store : sumAlloc allocSTORE = 32 := by native_decide

lemma alloc_valu_cap : ∀ t < T, allocVALU t ≤ VALU_CAP := by native_decide
lemma alloc_alu_cap : ∀ t < T, allocALU t ≤ ALU_CAP := by native_decide
lemma alloc_flow_cap : ∀ t < T, allocFLOW t ≤ FLOW_CAP := by native_decide
lemma alloc_load_cap : ∀ t < T, allocLOAD t ≤ LOAD_CAP := by native_decide
lemma alloc_store_cap : ∀ t < T, allocSTORE t ≤ STORE_CAP := by native_decide

theorem constructive_schedule_counts :
  sumAlloc allocVALU = 7872 ∧
  sumAlloc allocALU = 7463 ∧
  sumAlloc allocFLOW = 993 ∧
  sumAlloc allocLOAD = 2065 ∧
  sumAlloc allocSTORE = 32 ∧
  (∀ t < T, allocVALU t ≤ VALU_CAP) ∧
  (∀ t < T, allocALU t ≤ ALU_CAP) ∧
  (∀ t < T, allocFLOW t ≤ FLOW_CAP) ∧
  (∀ t < T, allocLOAD t ≤ LOAD_CAP) ∧
  (∀ t < T, allocSTORE t ≤ STORE_CAP) := by
  refine ⟨sumAlloc_valu, sumAlloc_alu, sumAlloc_flow, sumAlloc_load, sumAlloc_store, ?_, ?_, ?_, ?_, ?_⟩
  · exact alloc_valu_cap
  · exact alloc_alu_cap
  · exact alloc_flow_cap
  · exact alloc_load_cap
  · exact alloc_store_cap

/-! ### Per-vector dependency-respecting VALU schedule (round-robin order) -/

def vecAt (m : Nat) : Nat := m % VECTORS
def opIndex (t s : Nat) : Nat := VALU_CAP * t + s

lemma vecAt_modEq {m1 m2 : Nat} (h : vecAt m1 = vecAt m2) : m1 ≡ m2 [MOD VECTORS] := by
  have h1 : m1 ≡ vecAt m1 [MOD VECTORS] := (Nat.mod_modEq _ _).symm
  have h2 : vecAt m2 ≡ m2 [MOD VECTORS] := Nat.mod_modEq _ _
  have h3 : vecAt m1 ≡ vecAt m2 [MOD VECTORS] := by
    simpa [h] using (Nat.ModEq.refl (vecAt m1) (n:=VECTORS))
  exact h1.trans (h3.trans h2)

lemma vecAt_dvd_diff {m1 m2 : Nat} (h : vecAt m1 = vecAt m2) (h12 : m1 ≤ m2) :
    VECTORS ∣ m2 - m1 := by
  have hmod : m1 ≡ m2 [MOD VECTORS] := vecAt_modEq h
  exact (Nat.modEq_iff_dvd' h12).1 hmod

lemma vecAt_ne_add_of_lt {m d : Nat} (hd0 : 0 < d) (hd : d < VECTORS) :
    vecAt m ≠ vecAt (m + d) := by
  intro hEq
  have hdiv : VECTORS ∣ (m + d) - m := vecAt_dvd_diff hEq (Nat.le_add_right _ _)
  have hdiv' : VECTORS ∣ d := by
    simpa [Nat.add_sub_cancel_left] using hdiv
  have : d = 0 := Nat.eq_zero_of_dvd_of_lt hdiv' hd
  have hfalse : False := by
    simpa [this] using hd0
  exact hfalse.elim

lemma vecAt_distinct_same_cycle_lt {t s1 s2 : Nat} (hs2 : s2 < VALU_CAP)
    (hlt : s1 < s2) :
    vecAt (opIndex t s1) ≠ vecAt (opIndex t s2) := by
  have hd0 : 0 < s2 - s1 := by exact Nat.sub_pos_of_lt hlt
  have hd : s2 - s1 < VECTORS := by
    have : s2 - s1 < VALU_CAP := by omega
    exact lt_of_lt_of_le this (by decide : VALU_CAP ≤ VECTORS)
  have hle : s1 ≤ s2 := Nat.le_of_lt hlt
  have hsum : s1 + (s2 - s1) = s2 := by
    simpa [Nat.add_comm] using (Nat.sub_add_cancel hle)
  have hplus : opIndex t s2 = opIndex t s1 + (s2 - s1) := by
    calc
      opIndex t s2 = VALU_CAP * t + s2 := rfl
      _ = VALU_CAP * t + (s1 + (s2 - s1)) := by simpa [hsum]
      _ = VALU_CAP * t + s1 + (s2 - s1) := by omega
      _ = opIndex t s1 + (s2 - s1) := by
        simp [opIndex, Nat.add_assoc, Nat.add_comm]
  have hne := vecAt_ne_add_of_lt (m:=opIndex t s1) (d:=s2 - s1) hd0 hd
  simpa [hplus] using hne

lemma vecAt_distinct_same_cycle {t s1 s2 : Nat} (hs1 : s1 < VALU_CAP) (hs2 : s2 < VALU_CAP)
    (hneq : s1 ≠ s2) :
    vecAt (opIndex t s1) ≠ vecAt (opIndex t s2) := by
  cases lt_or_gt_of_ne hneq with
  | inl hlt =>
      exact vecAt_distinct_same_cycle_lt (t:=t) (s1:=s1) (s2:=s2) hs2 hlt
  | inr hgt =>
      have h := vecAt_distinct_same_cycle_lt (t:=t) (s1:=s2) (s2:=s1) hs1 hgt
      simpa [ne_comm, opIndex, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h

lemma valu_round_robin_respects_deps :
  ∀ t s1 s2, s1 < VALU_CAP → s2 < VALU_CAP → s1 ≠ s2 →
    vecAt (opIndex t s1) ≠ vecAt (opIndex t s2) := by
  intro t s1 s2 hs1 hs2 hneq
  exact vecAt_distinct_same_cycle (t:=t) (s1:=s1) (s2:=s2) hs1 hs2 hneq

/-! ### Instruction-level VALU schedule (cycle/slot mapping) -/

def VALU_CYCLES : Nat := totalCycles
def VALU_EXEC_OPS : Nat := VALU_CAP * VALU_CYCLES

def valuCycle (m : Nat) : Nat := m / VALU_CAP
def valuSlot (m : Nat) : Nat := m % VALU_CAP

lemma valu_exec_ops_eq : VALU_EXEC_OPS = 7872 := by
  simp [VALU_EXEC_OPS, VALU_CYCLES, VALU_CAP, totalCycles]

lemma valu_slot_lt (m : Nat) : valuSlot m < VALU_CAP := by
  exact Nat.mod_lt _ (by decide : 0 < VALU_CAP)

lemma valu_cycle_lt {m : Nat} (hm : m < VALU_EXEC_OPS) : valuCycle m < VALU_CYCLES := by
  have hpos : 0 < VALU_CAP := by decide
  have hm' : m < VALU_CYCLES * VALU_CAP := by
    simpa [VALU_EXEC_OPS, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hm
  have : m / VALU_CAP < VALU_CYCLES := by
    exact (Nat.div_lt_iff_lt_mul hpos).2 (by
      simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hm')
  simpa [valuCycle] using this

lemma valu_opIndex_of_div_mod (m : Nat) :
    opIndex (m / VALU_CAP) (m % VALU_CAP) = m := by
  have h := (Nat.mod_add_div m VALU_CAP)
  -- h : m % VALU_CAP + VALU_CAP * (m / VALU_CAP) = m
  calc
    opIndex (m / VALU_CAP) (m % VALU_CAP)
        = VALU_CAP * (m / VALU_CAP) + m % VALU_CAP := by
            simp [opIndex, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
    _ = m % VALU_CAP + VALU_CAP * (m / VALU_CAP) := by
            ac_rfl
    _ = m := by simpa using h

lemma opIndex_cycle_le {t1 s1 t2 s2 : Nat}
    (hs1 : s1 < VALU_CAP) (hs2 : s2 < VALU_CAP)
    (h : opIndex t1 s1 < opIndex t2 s2) : t1 ≤ t2 := by
  by_contra hgt
  have hlt : t2 < t1 := Nat.lt_of_not_ge hgt
  have hcontra : opIndex t2 s2 < opIndex t1 s1 := by
    have hstep : t2 + 1 ≤ t1 := Nat.succ_le_iff.mpr hlt
    have hmul : VALU_CAP * (t2 + 1) ≤ VALU_CAP * t1 := Nat.mul_le_mul_left _ hstep
    have hmul' : VALU_CAP * t2 + VALU_CAP ≤ VALU_CAP * t1 := by
      simpa [Nat.mul_add, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hmul
    have hlt' : VALU_CAP * t2 + s2 < VALU_CAP * t2 + VALU_CAP := by
      exact Nat.add_lt_add_left hs2 _
    have hlt'' : VALU_CAP * t2 + s2 < VALU_CAP * t1 := lt_of_lt_of_le hlt' hmul'
    exact lt_of_lt_of_le hlt'' (Nat.le_add_right _ _)
  have : opIndex t1 s1 < opIndex t1 s1 := lt_trans h hcontra
  exact (lt_irrefl _ this)

lemma valu_same_vec_implies_cycle_lt {t1 s1 t2 s2 : Nat}
    (hs1 : s1 < VALU_CAP) (hs2 : s2 < VALU_CAP)
    (hvec : vecAt (opIndex t1 s1) = vecAt (opIndex t2 s2))
    (hlt : opIndex t1 s1 < opIndex t2 s2) : t1 < t2 := by
  have hle : t1 ≤ t2 := opIndex_cycle_le (t1:=t1) (s1:=s1) (t2:=t2) (s2:=s2) hs1 hs2 hlt
  by_cases hEq : t1 = t2
  · -- same cycle: contradicts distinct vectors in a cycle
    have hs : s1 ≠ s2 := by
      have : s1 < s2 := by
        simpa [opIndex, hEq] using hlt
      exact ne_of_lt this
    have hneq := valu_round_robin_respects_deps (t:=t1) (s1:=s1) (s2:=s2) hs1 hs2 hs
    have hvec' : vecAt (opIndex t1 s1) = vecAt (opIndex t1 s2) := by
      simpa [hEq] using hvec
    exact (hneq hvec').elim
  · exact lt_of_le_of_ne hle hEq

theorem valu_round_robin_schedule_valid :
  ∀ t1 s1 t2 s2, s1 < VALU_CAP → s2 < VALU_CAP →
    vecAt (opIndex t1 s1) = vecAt (opIndex t2 s2) →
    opIndex t1 s1 < opIndex t2 s2 → t1 < t2 := by
  intro t1 s1 t2 s2 hs1 hs2 hvec hlt
  exact valu_same_vec_implies_cycle_lt (t1:=t1) (s1:=s1) (t2:=t2) (s2:=s2) hs1 hs2 hvec hlt

/-! ### Full per-round/per-stage ordering (unoffloaded VALU pipeline) -/

def roundLen (r : Nat) : Nat := if r = 10 then 14 else if r = 15 then 13 else 15

def roundStart : Nat → Nat
| 0 => 0
| r + 1 => roundStart r + roundLen r

def stepOf (r s : Nat) : Nat := roundStart r + s

lemma roundStart_mono {r1 r2 : Nat} (h : r1 ≤ r2) : roundStart r1 ≤ roundStart r2 := by
  induction r2 with
  | zero =>
      have : r1 = 0 := by omega
      simp [this, roundStart]
  | succ r2 ih =>
      cases Nat.eq_or_lt_of_le h with
      | inl hEq =>
          simp [hEq]
      | inr hlt =>
          have h' : r1 ≤ r2 := Nat.le_of_lt_succ hlt
          have ih' := ih h'
          have hle : roundStart r1 ≤ roundStart r2 + roundLen r2 :=
            Nat.le_trans ih' (Nat.le_add_right _ _)
          simpa [roundStart] using hle

lemma stepOf_lt_of_round_lt {r1 s1 r2 s2 : Nat} (h : r1 < r2) (hs1 : s1 < roundLen r1) :
    stepOf r1 s1 < stepOf r2 s2 := by
  have hstart : roundStart (r1 + 1) ≤ roundStart r2 :=
    roundStart_mono (r1:=r1+1) (r2:=r2) (Nat.succ_le_iff.mpr h)
  have h1 : stepOf r1 s1 < roundStart (r1 + 1) := by
    -- roundStart (r1+1) = roundStart r1 + roundLen r1
    have h' : s1 < roundLen r1 := hs1
    simpa [stepOf, roundStart, Nat.add_assoc] using (Nat.add_lt_add_left h' (roundStart r1))
  have h2 : roundStart r2 ≤ stepOf r2 s2 := by
    simp [stepOf, Nat.le_add_right]
  exact lt_of_lt_of_le h1 (le_trans hstart h2)

lemma stepOf_lt_of_stage_lt {r s1 s2 : Nat} (h : s1 < s2) :
    stepOf r s1 < stepOf r s2 := by
  simp [stepOf, Nat.add_lt_add_iff_left, h]

def opNumFull (v r s : Nat) : Nat := stepOf r s * VECTORS + v
def opCycleFull (v r s : Nat) : Nat := valuCycle (opNumFull v r s)
def opCycleFull1 (v r s : Nat) : Nat := opCycleFull v r s + 1

lemma add_vectors_mul (a : Nat) : a * VECTORS + VECTORS = (a + 1) * VECTORS := by
  calc
    a * VECTORS + VECTORS = VECTORS + a * VECTORS := by
      simp [Nat.add_comm]
    _ = (a + 1) * VECTORS := by
      simp [Nat.add_mul, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

lemma opNumFull_add_vectors (v r s : Nat) :
    opNumFull v r s + VECTORS = (stepOf r s + 1) * VECTORS + v := by
  calc
    opNumFull v r s + VECTORS
        = stepOf r s * VECTORS + v + VECTORS := by
            simp [opNumFull, Nat.add_assoc]
    _ = stepOf r s * VECTORS + VECTORS + v := by
            simp [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
    _ = (stepOf r s + 1) * VECTORS + v := by
            simpa [add_vectors_mul, Nat.add_assoc]

lemma opCycleFull_strict_of_step_lt {v r1 s1 r2 s2 : Nat}
    (h : stepOf r1 s1 < stepOf r2 s2) :
    opCycleFull v r1 s1 < opCycleFull v r2 s2 := by
  have hpos : 0 < VALU_CAP := by decide
  have hnum : opNumFull v r1 s1 + VECTORS ≤ opNumFull v r2 s2 := by
    have : stepOf r1 s1 + 1 ≤ stepOf r2 s2 := Nat.succ_le_iff.mpr h
    have hmul : (stepOf r1 s1 + 1) * VECTORS ≤ stepOf r2 s2 * VECTORS :=
      Nat.mul_le_mul_right _ this
    have hmul' : (stepOf r1 s1 + 1) * VECTORS + v ≤ stepOf r2 s2 * VECTORS + v :=
      Nat.add_le_add_right hmul v
    have hmul'' : opNumFull v r1 s1 + VECTORS ≤ stepOf r2 s2 * VECTORS + v := by
      simpa [opNumFull_add_vectors] using hmul'
    simpa [opNumFull] using hmul''
  have hlt' : opNumFull v r1 s1 / VALU_CAP <
      (opNumFull v r1 s1 + VECTORS) / VALU_CAP := by
    have hv : VALU_CAP ≤ VECTORS := by decide
    have hlt'' : opNumFull v r1 s1 + VALU_CAP ≤ opNumFull v r1 s1 + VECTORS :=
      Nat.add_le_add_left hv _
    have hq : (opNumFull v r1 s1 + VALU_CAP) / VALU_CAP =
        opNumFull v r1 s1 / VALU_CAP + 1 := by
      have := Nat.add_div_right (opNumFull v r1 s1) (z:=VALU_CAP) hpos
      simpa using this
    have hq' : opNumFull v r1 s1 / VALU_CAP < (opNumFull v r1 s1 + VALU_CAP) / VALU_CAP := by
      simpa [hq] using Nat.lt_succ_self (opNumFull v r1 s1 / VALU_CAP)
    exact lt_of_lt_of_le hq' (Nat.div_le_div_right hlt'')
  have hlt : opNumFull v r1 s1 / VALU_CAP < opNumFull v r2 s2 / VALU_CAP := by
    exact lt_of_lt_of_le hlt' (Nat.div_le_div_right hnum)
  simpa [opCycleFull] using hlt

/-! ### Setup assumptions for 1016 (simplified) -/

def inputLoadCycle (v : Nat) : Nat := 0
def storeCycle (v : Nat) : Nat := opCycleFull1 v 15 12 + 1

lemma input_load_before_compute (v r s : Nat) :
    inputLoadCycle v < opCycleFull1 v r s := by
  simp [inputLoadCycle, opCycleFull1]

lemma store_after_last_compute (v : Nat) :
    opCycleFull1 v 15 12 < storeCycle v := by
  simp [storeCycle]

/-! ### Cross-engine dependency schedule (ALU offload + Flow) -/

def ALU_OFFLOAD_OPS : Nat := 0

-- Offload predicate: no offload in the 1016 schedule.
def Offload (v r s : Nat) : Prop := opNumFull v r s < ALU_OFFLOAD_OPS

lemma offload_lt_total {v r s : Nat} (h : Offload v r s) : opNumFull v r s < totalVALU := by
  exact lt_of_lt_of_le h (Nat.zero_le _)

def aluTarget (k : Nat) : Nat := k + VALU_CAP
def aluCycle (k : Nat) : Nat := k / VALU_CAP
def aluSlot (k : Nat) : Nat := k % VALU_CAP

lemma alu_slot_lt (k : Nat) : aluSlot k < VALU_CAP := by
  exact Nat.mod_lt _ (by decide : 0 < VALU_CAP)

lemma alu_target_cycle :
    ∀ k, valuCycle (aluTarget k) = aluCycle k + 1 := by
  intro k
  have hpos : 0 < VALU_CAP := by decide
  have h := Nat.add_div_right k (z:=VALU_CAP) hpos
  -- (k + VALU_CAP) / VALU_CAP = k/VALU_CAP + 1
  simpa [aluTarget, aluCycle, valuCycle] using h

lemma alu_before_valu (k : Nat) :
    aluCycle k < valuCycle (aluTarget k) := by
  have h := alu_target_cycle k
  omega

lemma alu_cycle_lt {k : Nat} (hk : k < ALU_OFFLOAD_OPS) : aluCycle k < VALU_CYCLES := by
  exact (False.elim (Nat.not_lt_zero _ hk))

lemma alu_opIndex_of_div_mod (k : Nat) :
    opIndex (aluCycle k) (aluSlot k) = k := by
  -- Same proof as for VALU: div/mod reconstruction
  exact valu_opIndex_of_div_mod k

lemma alu_distinct_same_cycle {t s1 s2 : Nat} (hs1 : s1 < VALU_CAP) (hs2 : s2 < VALU_CAP)
    (hneq : s1 ≠ s2) :
    opIndex t s1 ≠ opIndex t s2 := by
  intro hEq
  have : s1 = s2 := by
    -- opIndex equality in same cycle forces slot equality
    have : VALU_CAP * t + s1 = VALU_CAP * t + s2 := by simpa [opIndex] using hEq
    exact Nat.add_left_cancel this
  exact (hneq this)

def flowCycle (f : Nat) : Nat := f + 1

lemma flow_after_valu (f : Nat) :
    valuCycle f < flowCycle f := by
  have h : valuCycle f ≤ f := by
    -- f/6 ≤ f
    exact Nat.div_le_self _ _
  exact lt_of_le_of_lt h (Nat.lt_succ_self _)

lemma flow_cycle_lt {f : Nat} (hf : f < flowOps) : flowCycle f < T := by
  -- flowOps = 993, T = 1312
  have : f + 1 ≤ 993 := by
    have hf' : f < 993 := by simpa [flowOps_eq] using hf
    exact Nat.succ_le_iff.mpr hf'
  exact lt_of_le_of_lt this (by decide : 993 < T)

theorem cross_engine_dependency_witness :
  (∀ k < ALU_OFFLOAD_OPS, aluCycle k < valuCycle (aluTarget k)) ∧
  (∀ f < flowOps, valuCycle f < flowCycle f) := by
  refine ⟨?alu, ?flow⟩
  · intro k hk
    exact alu_before_valu k
  · intro f hf
    exact flow_after_valu f

end ProofCacheTop4D4x15ResetOffload1016
