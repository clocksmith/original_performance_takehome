import Mathlib
import proofs.common.ISA

namespace ProofCommon
open ProofISA

/-- Hash cost per round per vector: 3 fused linear + 3 bitwise*3 = 12. -/
def HASH_OPS_PER_ROUND : Nat := 12

def NODE_XOR_PER_ROUND : Nat := 1

def PARITY_PER_ROUND : Nat := 1

def IDX_UPDATE_PER_ROUND : Nat := 1

/-- Recursive min/max bounds for index after k updates. -/
def minIdxR : Nat → Nat
| 0 => 0
| k + 1 => 2 * minIdxR k + 1

def maxIdxR : Nat → Nat
| 0 => 0
| k + 1 => 2 * maxIdxR k + 2

/-- Index set after k updates starting from 0. -/
def IdxSet : Nat → Set Nat
| 0 => {0}
| k + 1 => {n | ∃ i, i ∈ IdxSet k ∧ (n = 2 * i + 1 ∨ n = 2 * i + 2)}

/-- Closed-form interval as a set. -/
def IntervalSet (k : Nat) : Set Nat := {n | minIdxR k ≤ n ∧ n ≤ maxIdxR k}

lemma interval_step {a b n : Nat} (hn1 : 2 * a + 1 ≤ n) (hn2 : n ≤ 2 * b + 2) :
    ∃ i, a ≤ i ∧ i ≤ b ∧ (n = 2 * i + 1 ∨ n = 2 * i + 2) := by
  obtain ⟨k, hk | hk⟩ := Nat.even_or_odd' n
  · -- even: n = 2*k
    have hn1' := hn1
    have hn2' := hn2
    simp [hk] at hn1' hn2'
    have hk1 : a + 1 ≤ k := by omega
    have hk2 : k ≤ b + 1 := by omega
    have hkpos : 1 ≤ k := by omega
    let i := k - 1
    have hi1 : a ≤ i := by omega
    have hi2 : i ≤ b := by omega
    refine ⟨i, hi1, hi2, ?_⟩
    right
    have hk' : k - 1 + 1 = k := Nat.sub_add_cancel hkpos
    calc
      n = 2 * k := by simp [hk]
      _ = 2 * (k - 1 + 1) := by simp [hk']
      _ = 2 * (k - 1) + 2 := by
        simp [Nat.mul_add, Nat.add_comm]
      _ = 2 * i + 2 := by simp [i]
  · -- odd: n = 2*k + 1
    have hn1' := hn1
    have hn2' := hn2
    simp [hk] at hn1' hn2'
    have hk1 : a ≤ k := by omega
    have hk2 : k ≤ b := by omega
    refine ⟨k, hk1, hk2, ?_⟩
    left
    simp [hk, Nat.add_comm]

lemma idxset_bounds : ∀ {k n}, n ∈ IdxSet k → minIdxR k ≤ n ∧ n ≤ maxIdxR k := by
  intro k
  induction k with
  | zero =>
      intro n hn
      have hn' : n = 0 := by
        simpa [IdxSet] using hn
      subst hn'
      simp [minIdxR, maxIdxR]
  | succ k ih =>
      intro n hn
      rcases hn with ⟨i, hi, hni⟩
      have hbounds := ih hi
      rcases hbounds with ⟨hlo, hhi⟩
      cases hni with
      | inl h1 =>
          subst h1
          constructor
          ·
            have : 2 * minIdxR k + 1 ≤ 2 * i + 1 := by
              exact Nat.add_le_add_right (Nat.mul_le_mul_left 2 hlo) 1
            simpa [minIdxR] using this
          ·
            have : 2 * i + 1 ≤ 2 * maxIdxR k + 2 := by
              have := Nat.mul_le_mul_left 2 hhi
              exact Nat.add_le_add_right (Nat.le_trans this (Nat.le_succ _)) 1
            simpa [maxIdxR, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using this
      | inr h2 =>
          subst h2
          constructor
          ·
            have : 2 * minIdxR k + 1 ≤ 2 * i + 2 := by
              have := Nat.mul_le_mul_left 2 hlo
              exact Nat.le_trans (Nat.add_le_add_right this 1) (Nat.le_succ _)
            simpa [minIdxR, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using this
          ·
            have : 2 * i + 2 ≤ 2 * maxIdxR k + 2 := by
              exact Nat.add_le_add_right (Nat.mul_le_mul_left 2 hhi) 2
            simpa [maxIdxR, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using this

lemma minIdxR_eq_pow : ∀ k, minIdxR k = 2^k - 1 := by
  intro k
  induction k with
  | zero =>
      simp [minIdxR]
  | succ k ih =>
      have hpos : 1 ≤ 2^k := by
        exact (Nat.succ_le_iff.mpr (pow_pos (by decide : 0 < 2) k))
      have hstep : minIdxR (k + 1) + 1 = 2^(k + 1) := by
        calc
          minIdxR (k + 1) + 1 = (2 * minIdxR k + 1) + 1 := by simp [minIdxR]
          _ = 2 * minIdxR k + 2 := by simp [Nat.add_assoc]
          _ = 2 * minIdxR k + 2 * 1 := by simp
          _ = 2 * (minIdxR k + 1) := by
            simp [Nat.mul_add, Nat.add_comm]
          _ = 2 * (2^k) := by
            simp [ih, Nat.sub_add_cancel hpos]
          _ = 2^(k + 1) := by
            simp [Nat.pow_succ, Nat.mul_comm]
      calc
        minIdxR (k + 1) = (minIdxR (k + 1) + 1) - 1 := by simp
        _ = 2^(k + 1) - 1 := by simp [hstep]

lemma maxIdxR_eq_pow : ∀ k, maxIdxR k = 2^(k+1) - 2 := by
  intro k
  induction k with
  | zero =>
      simp [maxIdxR]
  | succ k ih =>
      have hpos : 2 ≤ 2^(k + 1) := by
        have h1 : 1 ≤ 2^k := by
          exact (Nat.succ_le_iff.mpr (pow_pos (by decide : 0 < 2) k))
        have hmul : 2 * 1 ≤ 2 * (2^k) := Nat.mul_le_mul_left 2 h1
        simpa [Nat.pow_succ, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hmul
      have hstep : maxIdxR (k + 1) + 2 = 2^(k + 2) := by
        calc
          maxIdxR (k + 1) + 2 = (2 * maxIdxR k + 2) + 2 := by simp [maxIdxR]
          _ = 2 * maxIdxR k + 4 := by simp [Nat.add_assoc]
          _ = 2 * maxIdxR k + 2 * 2 := by simp
          _ = 2 * (maxIdxR k + 2) := by
            simp [Nat.mul_add, Nat.add_comm]
          _ = 2 * (2^(k + 1)) := by
            simp [ih, Nat.sub_add_cancel hpos]
          _ = 2^(k + 2) := by
            simp [Nat.pow_succ, Nat.mul_comm]
      calc
        maxIdxR (k + 1) = (maxIdxR (k + 1) + 2) - 2 := by simp
        _ = 2^(k + 2) - 2 := by simp [hstep]

/-- Closed-form interval bound for IdxSet. -/
lemma idxset_bounds_closed_form {k n : Nat} (h : n ∈ IdxSet k) :
    2^k - 1 ≤ n ∧ n ≤ 2^(k+1) - 2 := by
  have h' := idxset_bounds h
  rcases h' with ⟨hlo, hhi⟩
  constructor
  · simpa [minIdxR_eq_pow k] using hlo
  · simpa [maxIdxR_eq_pow k] using hhi

lemma idxset_eq_interval : ∀ k, IdxSet k = IntervalSet k := by
  intro k
  induction k with
  | zero =>
      ext n
      constructor <;> intro h
      · have : n = 0 := by simpa [IdxSet] using h
        subst this
        simp [IntervalSet, minIdxR, maxIdxR]
      · have h' : n = 0 := by
          have h1 : n ≤ 0 := h.2
          exact Nat.le_antisymm h1 h.1
        simpa [IdxSet] using h'
  | succ k ih =>
      ext n
      constructor
      · intro h
        have h' := idxset_bounds h
        simpa [IntervalSet] using h'
      · intro h
        have hn1 : 2 * minIdxR k + 1 ≤ n := by
          simpa [minIdxR] using h.1
        have hn2 : n ≤ 2 * maxIdxR k + 2 := by
          simpa [maxIdxR] using h.2
        rcases interval_step (a:=minIdxR k) (b:=maxIdxR k) (n:=n) hn1 hn2 with
          ⟨i, hi1, hi2, hform⟩
        have hi : i ∈ IdxSet k := by
          have : i ∈ IntervalSet k := ⟨hi1, hi2⟩
          simpa [ih, IntervalSet] using this
        exact ⟨i, hi, hform⟩

lemma minIdxR_11 : minIdxR 11 = 2047 := by
  native_decide

lemma maxIdxR_4 : maxIdxR 4 = 30 := by
  native_decide

lemma maxIdxR_2 : maxIdxR 2 = 6 := by
  native_decide

lemma idxset4_le_30 {n : Nat} (h : n ∈ IdxSet 4) : n ≤ 30 := by
  have h' := (idxset_bounds h).2
  simpa [maxIdxR_4] using h'

lemma maxIdxR_mono {k m : Nat} (h : k ≤ m) : maxIdxR k ≤ maxIdxR m := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  induction d with
  | zero =>
      simp
  | succ d ih =>
      have ih' : maxIdxR k ≤ maxIdxR (k + d) := ih (Nat.le_add_right _ _)
      have hstep : maxIdxR (k + d) ≤ maxIdxR (k + d + 1) := by
        simp [maxIdxR]
        omega
      exact Nat.le_trans ih' hstep

lemma idxset_le_30_of_le4 {k n : Nat} (hk : k ≤ 4) (h : n ∈ IdxSet k) : n ≤ 30 := by
  have h' := (idxset_bounds h).2
  have hmax : maxIdxR k ≤ maxIdxR 4 := maxIdxR_mono hk
  have h'' : n ≤ maxIdxR 4 := Nat.le_trans h' hmax
  simpa [maxIdxR_4] using h''

lemma idxset_union_le4 {n : Nat} (hn : n ≤ 30) : ∃ k, k ≤ 4 ∧ n ∈ IdxSet k := by
  classical
  have hcases :
      n = 0 ∨ (1 ≤ n ∧ n ≤ 2) ∨ (3 ≤ n ∧ n ≤ 6) ∨ (7 ≤ n ∧ n ≤ 14) ∨ (15 ≤ n ∧ n ≤ 30) := by
    omega
  rcases hcases with h0 | h1 | h2 | h3 | h4
  · subst h0
    refine ⟨0, by omega, ?_⟩
    simp [IdxSet]
  · refine ⟨1, by omega, ?_⟩
    have : n ∈ IntervalSet 1 := by
      simpa [IntervalSet, minIdxR, maxIdxR] using h1
    simpa [idxset_eq_interval, IntervalSet] using this
  · refine ⟨2, by omega, ?_⟩
    have : n ∈ IntervalSet 2 := by
      simpa [IntervalSet, minIdxR, maxIdxR] using h2
    simpa [idxset_eq_interval, IntervalSet] using this
  · refine ⟨3, by omega, ?_⟩
    have : n ∈ IntervalSet 3 := by
      simpa [IntervalSet, minIdxR, maxIdxR] using h3
    simpa [idxset_eq_interval, IntervalSet] using this
  · refine ⟨4, by omega, ?_⟩
    have : n ∈ IntervalSet 4 := by
      simpa [IntervalSet, minIdxR, maxIdxR] using h4
    simpa [idxset_eq_interval, IntervalSet] using this

lemma idxset_le4_iff_le30 {n : Nat} : (∃ k, k ≤ 4 ∧ n ∈ IdxSet k) ↔ n ≤ 30 := by
  constructor
  · intro h
    rcases h with ⟨k, hk, hn⟩
    exact idxset_le_30_of_le4 hk hn
  · intro hn
    exact idxset_union_le4 hn

/-- Deterministic wrap: after 11th update (round 10), idx >= n_nodes. -/
lemma deterministic_wrap_round10 : minIdxR 11 = N_NODES := by
  simp [N_NODES, HEIGHT, minIdxR_11]

/-- After reset to 0, four more updates (rounds 11–14) stay < n_nodes. -/
lemma no_wrap_after_reset_rounds_11_14 : maxIdxR 4 < N_NODES := by
  simp [maxIdxR_4, N_NODES, HEIGHT]

/-- Rounds where parity+idx update are needed: rounds 0–9 and 11–14. -/
def ROUNDS_WITH_UPDATES : Nat := 14

/-- Per-vector VALU ops with deterministic wrap at round 10 and final-round skip. -/
def perVectorVALU : Nat :=
  HASH_OPS_PER_ROUND * ROUNDS
  + NODE_XOR_PER_ROUND * ROUNDS
  + PARITY_PER_ROUND * ROUNDS_WITH_UPDATES
  + IDX_UPDATE_PER_ROUND * ROUNDS_WITH_UPDATES

lemma perVectorVALU_eq : perVectorVALU = 236 := by
  simp [perVectorVALU, HASH_OPS_PER_ROUND, NODE_XOR_PER_ROUND,
        PARITY_PER_ROUND, IDX_UPDATE_PER_ROUND, ROUNDS, ROUNDS_WITH_UPDATES]

/-- Total VALU ops across 32 vectors. -/
def totalVALU : Nat := VECTORS * perVectorVALU

lemma totalVALU_eq : totalVALU = 7552 := by
  simp [totalVALU, VECTORS, perVectorVALU_eq]

/-- ALU can offload only bitwise ops: 1 VALU op = 8 scalar ops. -/
def offloadCap (T : Nat) : Nat := (ALU_CAP * T) / VLEN

/-- Total retirement capacity per T cycles, assuming only bitwise offload. -/
def totalCap (T : Nat) : Nat := VALU_CAP * T + offloadCap T

lemma cap_1006_lt : totalCap 1006 < totalVALU := by
  native_decide

lemma cap_1007_ge : totalCap 1007 ≥ totalVALU := by
  native_decide

/-- Capacity milestone: 1006 cycles is insufficient, 1007 cycles is sufficient. -/
theorem capacity_milestone : totalCap 1006 < totalVALU ∧ totalCap 1007 ≥ totalVALU := by
  exact ⟨cap_1006_lt, cap_1007_ge⟩

def ceilDiv (n d : Nat) : Nat := (n + d - 1) / d

lemma ceilDiv_vectors : ceilDiv VECTORS VALU_CAP = 6 := by
  simp [ceilDiv, VECTORS, VALU_CAP]

/-- Pipeline stagger bound: at most 6 vectors can be issued per cycle. -/
def pipeline_stagger : Nat := ceilDiv VECTORS VALU_CAP

end ProofCommon
