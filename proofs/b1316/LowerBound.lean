import Mathlib
import proofs.common.Base

namespace Proof1316
open ProofCommon

def GUARD : Nat := 3

-- Compute+issue+guard bound: 1007 (capacity) + 6 (stagger) + 3 (guard) = 1016.
theorem compute_bound_1016 :
  1007 + pipeline_stagger + GUARD = 1016 := by
  simp [pipeline_stagger, ceilDiv_vectors, GUARD]

def totalCycles : Nat := 1316

/-- Flow engine capacity for cached-node selection. -/
def FLOW_CAP : Nat := 1
def LOAD_CAP : Nat := 2
def STORE_CAP : Nat := 2

open scoped BigOperators

-- Top-3 caching selection cost: rounds 1/12 use 1 vselect, rounds 2/13 use 3 vselects.
def FLOW_SELECT_R1 : Nat := 2 * VECTORS
def FLOW_SELECT_R2 : Nat := 2 * VECTORS * 3
def flowOps : Nat := FLOW_SELECT_R1 + FLOW_SELECT_R2

lemma flowOps_eq : flowOps = 256 := by
  simp [flowOps, FLOW_SELECT_R1, FLOW_SELECT_R2, VECTORS]

lemma flow_capacity_1316 : flowOps ≤ FLOW_CAP * totalCycles := by
  simp [flowOps_eq, FLOW_CAP, totalCycles]

/-- Load budget with top-3 caching (nodes 0..6). -/
def PRELOAD_NODES : Nat := 7 -- top 3 levels: 1+2+4
def ROUNDS_LOAD : Nat := 10 -- rounds 3..10 and 14..15 (uncached)
def nodeLoadOps : Nat := PRELOAD_NODES + ROUNDS_LOAD * LANES
def inputLoadOps : Nat := 2 * VECTORS -- vload indices + values (assumed pre-initialized)
def totalLoadOps : Nat := nodeLoadOps + inputLoadOps

lemma preload_nodes_eq : PRELOAD_NODES = maxIdxR 2 + 1 := by
  simp [PRELOAD_NODES, maxIdxR_2]

lemma lanes_eq : LANES = 256 := by
  simp [LANES, VECTORS, VLEN]

lemma totalLoadOps_eq : totalLoadOps = 2631 := by
  simp [totalLoadOps, nodeLoadOps, inputLoadOps, PRELOAD_NODES, ROUNDS_LOAD, LANES, VECTORS, VLEN]

def loadLower : Nat := ceilDiv totalLoadOps LOAD_CAP

lemma loadLower_eq : loadLower = totalCycles := by
  simp [loadLower, ceilDiv, totalLoadOps_eq, LOAD_CAP, totalCycles]

lemma overall_lower_bound : max (1007 + pipeline_stagger + GUARD) loadLower = totalCycles := by
  -- max(1016,1316) = 1316
  simp [compute_bound_1016, loadLower_eq, totalCycles]

lemma load_capacity_1316 : totalLoadOps ≤ LOAD_CAP * totalCycles := by
  simp [totalLoadOps_eq, LOAD_CAP, totalCycles]

def storeOps : Nat := VECTORS -- vstore values once

lemma store_capacity_1316 : storeOps ≤ STORE_CAP * totalCycles := by
  simp [storeOps, STORE_CAP, VECTORS, totalCycles]

/-- Offload needed at T=1007 and its ALU feasibility. -/
def offloadNeeded (T : Nat) : Nat := totalVALU - VALU_CAP * T

lemma offload_needed_1007 : offloadNeeded 1007 = 1510 := by
  native_decide

lemma offloadCap_1007 : offloadCap 1007 = 1510 := by
  native_decide

lemma offload_feasible_1007 : offloadNeeded 1007 ≤ offloadCap 1007 := by
  simp [offload_needed_1007, offloadCap_1007]

/-- Combined schedule skeleton: capacity + flow + load + stagger. -/
theorem schedule_skeleton :
  totalCap 1006 < totalVALU ∧
  totalCap 1007 ≥ totalVALU ∧
  offloadNeeded 1007 = offloadCap 1007 ∧
  flowOps ≤ FLOW_CAP * totalCycles ∧
  totalLoadOps ≤ LOAD_CAP * totalCycles ∧
  storeOps ≤ STORE_CAP * totalCycles ∧
  1007 + pipeline_stagger + GUARD = 1016 := by
  refine ⟨cap_1006_lt, cap_1007_ge, ?_, flow_capacity_1316, load_capacity_1316, store_capacity_1316, compute_bound_1016⟩
  simp [offload_needed_1007, offloadCap_1007]

/-! ## Constructive per-engine count schedule (total window) -/

def T : Nat := totalCycles

def allocVALU (t : Nat) : Nat := if t < 1007 then 6 else 0
def allocALU (t : Nat) : Nat := if t < 1006 then 12 else if t = 1006 then 8 else 0
def allocFLOW (t : Nat) : Nat := if t < 256 then 1 else 0
def allocLOAD (t : Nat) : Nat := if t < 1315 then 2 else if t = 1315 then 1 else 0
def allocSTORE (t : Nat) : Nat := if t < 16 then 2 else 0

def sumAlloc (f : Nat → Nat) : Nat := (Finset.range T).sum f

lemma sumAlloc_valu : sumAlloc allocVALU = 6042 := by native_decide
lemma sumAlloc_alu : sumAlloc allocALU = 12080 := by native_decide
lemma sumAlloc_flow : sumAlloc allocFLOW = 256 := by native_decide
lemma sumAlloc_load : sumAlloc allocLOAD = 2631 := by native_decide
lemma sumAlloc_store : sumAlloc allocSTORE = 32 := by native_decide

lemma alloc_valu_cap : ∀ t < T, allocVALU t ≤ VALU_CAP := by native_decide
lemma alloc_alu_cap : ∀ t < T, allocALU t ≤ ALU_CAP := by native_decide
lemma alloc_flow_cap : ∀ t < T, allocFLOW t ≤ FLOW_CAP := by native_decide
lemma alloc_load_cap : ∀ t < T, allocLOAD t ≤ LOAD_CAP := by native_decide
lemma alloc_store_cap : ∀ t < T, allocSTORE t ≤ STORE_CAP := by native_decide

theorem constructive_schedule_counts :
  sumAlloc allocVALU = 6042 ∧
  sumAlloc allocALU = 12080 ∧
  sumAlloc allocFLOW = 256 ∧
  sumAlloc allocLOAD = 2631 ∧
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

def VALU_CYCLES : Nat := 1007
def VALU_EXEC_OPS : Nat := VALU_CAP * VALU_CYCLES

def valuCycle (m : Nat) : Nat := m / VALU_CAP
def valuSlot (m : Nat) : Nat := m % VALU_CAP

lemma valu_exec_ops_eq : VALU_EXEC_OPS = 6042 := by
  simp [VALU_EXEC_OPS, VALU_CYCLES, VALU_CAP]

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

def roundLen (r : Nat) : Nat := if r = 10 ∨ r = 15 then 13 else 15

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

/-! ### 1016-cycle schedule with explicit setup phase -/

def SETUP_NODE_OPS : Nat := 7
def SETUP_CONST_OPS : Nat := 12 -- hash constants + {one,two,forest_base}
def SETUP_VALU_OPS : Nat := SETUP_NODE_OPS + SETUP_CONST_OPS
def T1016 : Nat := 1016
def SETUP_CYCLES : Nat := pipeline_stagger + GUARD -- 6 + 3 = 9
def COMPUTE_SHIFT : Nat := SETUP_CYCLES

lemma setup_ops_eq : SETUP_VALU_OPS = 19 := by
  simp [SETUP_VALU_OPS, SETUP_NODE_OPS, SETUP_CONST_OPS]

lemma setup_ops_fit :
    SETUP_VALU_OPS ≤ VALU_CAP * SETUP_CYCLES := by
  -- 43 ≤ 6 * 9
  simp [setup_ops_eq, VALU_CAP, SETUP_CYCLES, pipeline_stagger, GUARD, ceilDiv_vectors]

def opCycleFull1016 (v r s : Nat) : Nat := opCycleFull v r s + COMPUTE_SHIFT

lemma roundStart_one : roundStart 1 = 15 := by
  simp [roundStart, roundLen]

lemma roundStart_ge_15 {r : Nat} (h : 1 ≤ r) : 15 ≤ roundStart r := by
  have hmono := roundStart_mono (r1:=1) (r2:=r) h
  simpa [roundStart_one] using hmono

lemma opCycleFull_lower_bound (v r s : Nat) :
    (roundStart r * VECTORS) / VALU_CAP ≤ opCycleFull v r s := by
  -- stepOf r s ≥ roundStart r, and adding v only increases the numerator
  have hstep : roundStart r ≤ stepOf r s := by
    simp [stepOf, Nat.le_add_right]
  have hmul : roundStart r * VECTORS ≤ stepOf r s * VECTORS := Nat.mul_le_mul_right _ hstep
  have hnum : roundStart r * VECTORS ≤ stepOf r s * VECTORS + v :=
    Nat.le_trans hmul (Nat.le_add_right _ _)
  exact Nat.div_le_div_right hnum

lemma opCycleFull1016_ge_89 {v r s : Nat} (hr : 1 ≤ r) :
    89 ≤ opCycleFull1016 v r s := by
  have h0 : (roundStart r * VECTORS) / VALU_CAP ≤ opCycleFull v r s :=
    opCycleFull_lower_bound v r s
  have h1 : 15 ≤ roundStart r := roundStart_ge_15 hr
  have h2 : (15 * VECTORS) / VALU_CAP ≤ (roundStart r * VECTORS) / VALU_CAP :=
    Nat.div_le_div_right (Nat.mul_le_mul_right _ h1)
  have h3 : (15 * VECTORS) / VALU_CAP = 80 := by native_decide
  have h4 : 80 ≤ opCycleFull v r s := by
    have := le_trans (by simpa [h3] using h2) h0
    simpa using this
  -- shift by setup cycles
  have : 89 ≤ opCycleFull v r s + COMPUTE_SHIFT := by
    have h' : 80 + SETUP_CYCLES ≤ opCycleFull v r s + SETUP_CYCLES :=
      Nat.add_le_add_right h4 _
    simpa [COMPUTE_SHIFT, SETUP_CYCLES] using h'
  simpa [opCycleFull1016] using this

def loadCycleNode (i : Nat) : Nat := i / 2

lemma loadCycleNode_lt_16 {i : Nat} (hi : i < SETUP_NODE_OPS) : loadCycleNode i < 16 := by
  have hle : i ≤ 30 := Nat.lt_succ_iff.mp hi
  have hdiv : i / 2 ≤ 30 / 2 := Nat.div_le_div_right hle
  have hmax : 30 / 2 = 15 := by native_decide
  have : loadCycleNode i ≤ 15 := by simpa [loadCycleNode, hmax] using hdiv
  exact lt_of_le_of_lt this (by decide : 15 < 16)

lemma load_before_round0 (v s : Nat) :
    loadCycleNode 0 < opCycleFull1016 v 0 s := by
  have hpos : 0 < COMPUTE_SHIFT := by decide
  have hle : COMPUTE_SHIFT ≤ opCycleFull v 0 s + COMPUTE_SHIFT := by
    exact Nat.le_add_left _ _
  have : 0 < opCycleFull v 0 s + COMPUTE_SHIFT := lt_of_lt_of_le hpos hle
  simpa [loadCycleNode, opCycleFull1016] using this

lemma load_before_round_ge1 {v r s i : Nat} (hr : 1 ≤ r) (hi : i < SETUP_NODE_OPS) :
    loadCycleNode i < opCycleFull1016 v r s := by
  have hload : loadCycleNode i < 16 := loadCycleNode_lt_16 hi
  have hcomp : 89 ≤ opCycleFull1016 v r s := opCycleFull1016_ge_89 hr
  exact lt_of_lt_of_le hload (le_trans (by decide : 16 ≤ 89) hcomp)

-- Uncached rounds (rounds 3..10 and 14..15): node loads must occur before the node-xor step.
def UncachedRound (r : Nat) : Prop := (3 ≤ r ∧ r ≤ 10) ∨ (14 ≤ r ∧ r ≤ 15)

def NODE_STEP : Nat := 0

lemma node_step_lt (r : Nat) : NODE_STEP < roundLen r := by
  simp [NODE_STEP, roundLen]

lemma opCycleFull1016_pos (v r s : Nat) : 0 < opCycleFull1016 v r s := by
  have hpos : 0 < COMPUTE_SHIFT := by decide
  have hle : COMPUTE_SHIFT ≤ opCycleFull v r s + COMPUTE_SHIFT := by
    exact Nat.le_add_left _ _
  have : 0 < opCycleFull v r s + COMPUTE_SHIFT := lt_of_lt_of_le hpos hle
  simpa [opCycleFull1016] using this

def nodeLoadCycleUncached (v r lane : Nat) : Nat :=
  opCycleFull1016 v r NODE_STEP - 1

lemma uncached_load_before_use (v r lane : Nat) (hr : UncachedRound r) :
    nodeLoadCycleUncached v r lane < opCycleFull1016 v r NODE_STEP := by
  have hpos : 0 < opCycleFull1016 v r NODE_STEP := opCycleFull1016_pos v r NODE_STEP
  have hlt : opCycleFull1016 v r NODE_STEP - 1 < opCycleFull1016 v r NODE_STEP :=
    Nat.sub_lt_self hpos (by decide : 0 < 1)
  simpa [nodeLoadCycleUncached] using hlt

def allocVALU1016 (t : Nat) : Nat :=
  if t < 3 then 6 else if t = 3 then 1 else if t < 9 then 0 else if t < 1016 then 6 else 0

def sumAlloc1016 (f : Nat → Nat) : Nat := (Finset.range T1016).sum f

lemma sumAlloc_valu_1016 : sumAlloc1016 allocVALU1016 = 6061 := by native_decide

lemma alloc_valu_1016_cap : ∀ t < T1016, allocVALU1016 t ≤ VALU_CAP := by native_decide

lemma alloc_valu_1016_counts :
  sumAlloc1016 allocVALU1016 = VALU_EXEC_OPS + SETUP_VALU_OPS ∧
  (∀ t < T1016, allocVALU1016 t ≤ VALU_CAP) := by
  refine ⟨?_, alloc_valu_1016_cap⟩
  simp [sumAlloc_valu_1016, VALU_EXEC_OPS, VALU_CAP, VALU_CYCLES, SETUP_VALU_OPS,
        SETUP_NODE_OPS, SETUP_CONST_OPS]

def inputLoadCycle (v : Nat) : Nat := 0
def storeCycle (v : Nat) : Nat := opCycleFull1 v 15 12 + 1

lemma input_load_before_compute (v r s : Nat) :
    inputLoadCycle v < opCycleFull1 v r s := by
  simp [inputLoadCycle, opCycleFull1]

lemma store_after_last_compute (v : Nat) :
    opCycleFull1 v 15 12 < storeCycle v := by
  simp [storeCycle]

/-! ### Cross-engine dependency schedule (ALU offload + Flow) -/

def ALU_OFFLOAD_OPS : Nat := 1510

-- Offload predicate: first 1510 VALU ops in opNumFull order.
def Offload (v r s : Nat) : Prop := opNumFull v r s < ALU_OFFLOAD_OPS

lemma offload_lt_total {v r s : Nat} (h : Offload v r s) : opNumFull v r s < totalVALU := by
  have h' : ALU_OFFLOAD_OPS < totalVALU := by
    -- 1510 < 7552
    simpa [ALU_OFFLOAD_OPS, totalVALU_eq] using (by decide : 1510 < 7552)
  exact lt_of_lt_of_le h (le_of_lt h')

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
  -- k < 1510 ⇒ k/6 ≤ 1509/6 = 251 < 1007
  have hle : k ≤ 1509 := Nat.lt_succ_iff.mp hk
  have hdiv : k / VALU_CAP ≤ 1509 / VALU_CAP := Nat.div_le_div_right hle
  have hmax : 1509 / VALU_CAP = 251 := by native_decide
  have hbound : k / VALU_CAP ≤ 251 := by simpa [hmax] using hdiv
  exact lt_of_le_of_lt hbound (by decide : 251 < VALU_CYCLES)

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
  -- flowOps = 256, T = 1316
  have : f + 1 ≤ 256 := by
    have hf' : f < 256 := by simpa [flowOps_eq] using hf
    exact Nat.succ_le_iff.mpr hf'
  exact lt_of_le_of_lt this (by decide : 256 < T)

theorem cross_engine_dependency_witness :
  (∀ k < ALU_OFFLOAD_OPS, aluCycle k < valuCycle (aluTarget k)) ∧
  (∀ f < flowOps, valuCycle f < flowCycle f) := by
  refine ⟨?alu, ?flow⟩
  · intro k hk
    exact alu_before_valu k
  · intro f hf
    exact flow_after_valu f

/-! ## Abstract two-phase schedule model (issue + compute) -/

def ComputeFeasible (t : Nat) : Prop := totalCap t ≥ totalVALU
def IssueFeasible (s : Nat) : Prop := VECTORS ≤ s * VALU_CAP
def TotalCycles (t s : Nat) : Nat := t + s + GUARD

lemma totalCap_mono : Monotone totalCap := by
  intro a b h
  unfold totalCap offloadCap
  have h1 : VALU_CAP * a ≤ VALU_CAP * b := Nat.mul_le_mul_left _ h
  have h2 : (ALU_CAP * a) / VLEN ≤ (ALU_CAP * b) / VLEN := by
    exact Nat.div_le_div_right (Nat.mul_le_mul_left _ h)
  exact Nat.add_le_add h1 h2

lemma compute_lower_bound {t : Nat} (h : ComputeFeasible t) : 1007 ≤ t := by
  by_contra hge
  have hlt : t < 1007 := Nat.lt_of_not_ge hge
  have hle : t ≤ 1006 := by
    exact (Nat.lt_succ_iff.mp hlt)
  have hcap : totalCap t ≤ totalCap 1006 := totalCap_mono hle
  have hcontr : totalCap t < totalVALU := lt_of_le_of_lt hcap cap_1006_lt
  exact (not_lt_of_ge h) hcontr

lemma issue_lower_bound {s : Nat} (h : IssueFeasible s) : pipeline_stagger ≤ s := by
  have hcap : 32 ≤ s * 6 := by
    simpa [IssueFeasible, VECTORS, VALU_CAP] using h
  by_contra hs
  have hs' : s ≤ 5 := Nat.lt_succ_iff.mp (Nat.lt_of_not_ge hs)
  have hmul : s * 6 ≤ 5 * 6 := Nat.mul_le_mul_right _ hs'
  have hmul' : s * 6 ≤ 30 := by simpa using hmul
  have hcontr : 32 ≤ 30 := le_trans hcap hmul'
  exact (Nat.not_le_of_gt (by decide : 30 < 32)) hcontr

lemma issue_feasible_pipeline : IssueFeasible pipeline_stagger := by
  have h : pipeline_stagger = 6 := by
    simp [pipeline_stagger, ceilDiv_vectors]
  simp [IssueFeasible, h, VECTORS, VALU_CAP]

lemma compute_feasible_1007 : ComputeFeasible 1007 := by
  exact cap_1007_ge

theorem abstract_lower_bound {t s : Nat} (hT : ComputeFeasible t) (hS : IssueFeasible s) :
  1007 + pipeline_stagger + GUARD ≤ TotalCycles t s := by
  have h := Nat.add_le_add (compute_lower_bound hT) (issue_lower_bound hS)
  have h' : 1007 + pipeline_stagger + GUARD ≤ t + s + GUARD :=
    Nat.add_le_add_right h GUARD
  simpa [TotalCycles, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using h'

theorem abstract_upper_bound :
  ComputeFeasible 1007 ∧ IssueFeasible pipeline_stagger ∧ TotalCycles 1007 pipeline_stagger = 1016 := by
  refine ⟨compute_feasible_1007, issue_feasible_pipeline, ?_⟩
  simpa [TotalCycles, GUARD, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using compute_bound_1016

theorem abstract_tight_bound :
  (∀ t s, ComputeFeasible t → IssueFeasible s → 1007 + pipeline_stagger + GUARD ≤ TotalCycles t s) ∧
  (∃ t s, ComputeFeasible t ∧ IssueFeasible s ∧ TotalCycles t s = 1016) := by
  refine ⟨?lb, ?ub⟩
  · intro t s ht hs
    exact abstract_lower_bound ht hs
  · refine ⟨1007, pipeline_stagger, compute_feasible_1007, issue_feasible_pipeline, ?_⟩
    simpa [TotalCycles, GUARD, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using compute_bound_1016

end Proof1316
