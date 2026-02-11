import proofs.global_lower_bound.LowerBound.MachineTraceEq
import proofs.global_lower_bound.LowerBound.Specs

namespace ProofGlobalLowerBound
open ProofCommon
open ProofMachine
open ProofISA

/-! ### Structured adversary: distinct addresses per (round, lane, copy) -/

def RoundDistinctNodes (mem : Memory) (k : Nat) : Prop :=
  let rounds := memAt mem 0
  ∃ f : Fin rounds → Fin BATCH_SIZE → Fin k → Nat,
    (∀ r i j, AddrSafe mem (f r i j)) ∧
    (∀ r i j, ∃ lane : Fin BATCH_SIZE,
      spec_kernel (memUpdate mem (f r i j) (memAt mem (f r i j) + 1)) lane ≠
        spec_kernel mem lane) ∧
    Function.Injective (fun t : (Fin rounds × Fin BATCH_SIZE × Fin k) =>
      f t.1 t.2.1 t.2.2)

theorem adversaryK_of_roundDistinct (mem : Memory) (k : Nat)
    (h : RoundDistinctNodes mem k) : AdversaryK mem k := by
  classical
  -- Unpack the structured adversary.
  dsimp [RoundDistinctNodes] at h
  rcases h with ⟨f, hf_safe, hf_sens, hf_inj⟩
  -- Enumerate all triples (round, lane, copy) and map them through `f`.
  let rounds : Nat := memAt mem 0
  let g : (Fin rounds × Fin BATCH_SIZE × Fin k) → Nat :=
    fun t => f t.1 t.2.1 t.2.2
  let triples : List (Fin rounds × Fin BATCH_SIZE × Fin k) :=
    (Finset.univ : Finset (Fin rounds × Fin BATCH_SIZE × Fin k)).toList
  let L : List Nat := triples.map g
  refine ⟨L, ?_, ?_⟩
  · -- `AdversaryList mem L`
    refine ⟨?_, ?_, ?_⟩
    · -- Nodup from injectivity of `g`.
      have htriples : triples.Nodup := by
        simpa [triples] using
          (Finset.nodup_toList (Finset.univ : Finset (Fin rounds × Fin BATCH_SIZE × Fin k)))
      have hg_inj : Function.Injective g := hf_inj
      simpa [L] using (htriples.map hg_inj)
    · -- Every address is safe.
      intro addr hadd
      rcases (List.mem_map.1 hadd) with ⟨t, _ht, htEq⟩
      -- rewrite `addr` to a concrete `g t`
      cases htEq
      exact hf_safe t.1 t.2.1 t.2.2
    · -- Every address is sensitive.
      intro addr hadd
      rcases (List.mem_map.1 hadd) with ⟨t, _ht, htEq⟩
      cases htEq
      exact hf_sens t.1 t.2.1 t.2.2
  · -- Length: one address per triple.
    have hlen_triples :
        triples.length = rounds * BATCH_SIZE * k := by
      -- `toList` enumerates `univ` without duplicates, so length is the card.
      -- `α × β × γ` is right-associated as `α × (β × γ)`.
      simp [triples, rounds, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
    have hlen_L : L.length = rounds * BATCH_SIZE * k := by
      simpa [L] using hlen_triples
    -- Match the multiplicative order in `AdversaryK`.
    -- `rounds = memAt mem 0` by definition.
    have : rounds * BATCH_SIZE * k = k * BATCH_SIZE * memAt mem 0 := by
      -- `rounds` is definitional equal to `memAt mem 0`.
      -- Normalize using associativity/commutativity of `Nat.mul`.
      simp [rounds, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    simpa [L, rounds] using (hlen_L.trans this)
def BIG_M : Nat := Nat.pow 2 (ROUNDS + 2)

def bigIdxNat (i : Nat) : Nat := (2 * i + 1) * BIG_M

def bigIdx (i : Fin BATCH_SIZE) : Nat := bigIdxNat i

def bSeq (r : Nat) : Nat :=
  if iterHash (r + 1) 0 % 2 = 0 then 1 else 2

def cSeq : Nat → Nat
  | 0 => 0
  | r+1 => 2 * cSeq r + bSeq r

def idxAt (r : Nat) (i : Fin BATCH_SIZE) : Nat :=
  (Nat.pow 2 r) * bigIdx i + cSeq r

def N_NODES_BIG : Nat :=
  (Nat.pow 2 ROUNDS) * (2 * BATCH_SIZE) * BIG_M + BIG_M

def BIG_FOREST_BASE : Nat := HEADER_SIZE
def BIG_IDX_BASE : Nat := BIG_FOREST_BASE + N_NODES_BIG
def BIG_VAL_BASE : Nat := BIG_IDX_BASE + BATCH_SIZE
def MEM_BIG_SIZE : Nat := BIG_VAL_BASE + BATCH_SIZE

def memBig : Memory :=
  { data :=
      fun a =>
        if a = 0 then ROUNDS
        else if a = 1 then N_NODES_BIG
        else if a = 2 then BATCH_SIZE
        else if a = 3 then HEIGHT
        else if a = PTR_FOREST then BIG_FOREST_BASE
        else if a = PTR_INP_IDX then BIG_IDX_BASE
        else if a = PTR_INP_VAL then BIG_VAL_BASE
        else if BIG_FOREST_BASE ≤ a ∧ a < BIG_FOREST_BASE + N_NODES_BIG then 0
        else if BIG_IDX_BASE ≤ a ∧ a < BIG_IDX_BASE + BATCH_SIZE then
          bigIdxNat (a - BIG_IDX_BASE)
        else if BIG_VAL_BASE ≤ a ∧ a < BIG_VAL_BASE + BATCH_SIZE then 0
        else 0,
    size := MEM_BIG_SIZE }

lemma bSeq_le_two (r : Nat) : bSeq r ≤ 2 := by
  unfold bSeq
  by_cases h : iterHash (r + 1) 0 % 2 = 0
  · simp [h]
  · simp [h]

lemma cSeq_bound_le : ∀ r, cSeq r ≤ Nat.pow 2 (r + 1) - 2 := by
  intro r
  induction r with
  | zero =>
      simp [cSeq]
  | succ r ih =>
      have hb : bSeq r ≤ 2 := bSeq_le_two r
      set t := Nat.pow 2 (r + 1)
      have h1 : 2 * cSeq r + bSeq r ≤ 2 * (t - 2) + 2 := by
        exact Nat.add_le_add (Nat.mul_le_mul_left _ ih) hb
      have h2 : 2 * (t - 2) + 2 ≤ 2 * t - 2 := by
        have ht : 2 ≤ t := by
          have hpow : Nat.pow 2 1 ≤ Nat.pow 2 (r + 1) := by
            exact Nat.pow_le_pow_right (by decide : 0 < 2) (Nat.succ_le_succ (Nat.zero_le r))
          simpa [t] using hpow
        -- omega handles the linear arithmetic with t ≥ 2
        omega
      have h2' : 2 * (t - 2) + 2 ≤ Nat.pow 2 (r + 2) - 2 := by
        -- rewrite 2 * t as 2^(r+2)
        simpa [t, Nat.pow_succ, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using h2
      -- unfold cSeq at succ
      simpa [cSeq] using (le_trans h1 h2')

lemma cSeq_bound : ∀ r, cSeq r < Nat.pow 2 (r + 1) := by
  intro r
  have hle : cSeq r ≤ Nat.pow 2 (r + 1) - 2 := cSeq_bound_le r
  have hlt : Nat.pow 2 (r + 1) - 2 < Nat.pow 2 (r + 1) := by
    have hpos : 0 < Nat.pow 2 (r + 1) := by
      exact Nat.pow_pos (by decide : 0 < 2)
    exact Nat.sub_lt hpos (by decide : 0 < (2:Nat))
  exact lt_of_le_of_lt hle hlt

lemma pow_le_bigM {r : Nat} (hr : r < ROUNDS) :
    Nat.pow 2 (r + 1) ≤ BIG_M := by
  unfold BIG_M
  have hle1 : r + 1 ≤ ROUNDS := Nat.succ_le_of_lt hr
  have hle2 : ROUNDS ≤ ROUNDS + 2 := Nat.le_add_right _ _
  have hle : r + 1 ≤ ROUNDS + 2 := Nat.le_trans hle1 hle2
  exact Nat.pow_le_pow_right (Nat.succ_pos 1) hle
lemma idxAt_lt_N_NODES_BIG (r : Nat) (i : Fin BATCH_SIZE) (hr : r < ROUNDS) :
    idxAt r i < N_NODES_BIG := by
  have hpow : Nat.pow 2 r ≤ Nat.pow 2 ROUNDS := by
    exact Nat.pow_le_pow_right (by decide : 0 < 2) (Nat.le_of_lt hr)
  have hi2 : 2 * (i : Nat) < 2 * BATCH_SIZE := by
    exact (Nat.mul_lt_mul_left (a:=2) (b:=i) (c:=BATCH_SIZE) (by decide : 0 < (2:Nat))).2
      i.is_lt
  have hle : 2 * (i : Nat) + 1 ≤ 2 * BATCH_SIZE := by
    exact Nat.succ_le_of_lt hi2
  have hbig : bigIdx i ≤ (2 * BATCH_SIZE) * BIG_M := by
    dsimp [bigIdx, bigIdxNat]
    exact Nat.mul_le_mul_right _ hle
  have hidx1 : Nat.pow 2 r * bigIdx i ≤ Nat.pow 2 ROUNDS * bigIdx i := by
    exact Nat.mul_le_mul_right _ hpow
  have hidx2 : Nat.pow 2 ROUNDS * bigIdx i ≤ Nat.pow 2 ROUNDS * ((2 * BATCH_SIZE) * BIG_M) := by
    exact Nat.mul_le_mul_left _ hbig
  have hidx : Nat.pow 2 r * bigIdx i ≤ Nat.pow 2 ROUNDS * ((2 * BATCH_SIZE) * BIG_M) :=
    Nat.le_trans hidx1 hidx2
  have hval : cSeq r < BIG_M := by
    have hc : cSeq r < Nat.pow 2 (r + 1) := cSeq_bound r
    exact lt_of_lt_of_le hc (pow_le_bigM hr)
  have hsum : idxAt r i < Nat.pow 2 ROUNDS * ((2 * BATCH_SIZE) * BIG_M) + BIG_M := by
    dsimp [idxAt]
    exact Nat.add_lt_add_of_le_of_lt hidx hval
  simpa [N_NODES_BIG, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hsum

def idxAtR (r : Fin ROUNDS) (i : Fin BATCH_SIZE) : Nat := idxAt (r : Nat) i

lemma idxAtR_lt (r : Fin ROUNDS) (i : Fin BATCH_SIZE) :
    idxAtR r i < N_NODES_BIG := by
  exact idxAt_lt_N_NODES_BIG (r := r) i r.is_lt
lemma memBig_safe : MemSafeKernel memBig := by
  dsimp [MemSafeKernel]
  constructor
  · -- size bound
    have hpos : 0 < BATCH_SIZE := by decide
    dsimp [memBig, MEM_BIG_SIZE, BIG_VAL_BASE, BIG_IDX_BASE, BIG_FOREST_BASE, HEADER_SIZE]
    omega
  constructor
  · -- memAt memBig 2 = BATCH_SIZE
    simp [memAt, memBig]
  -- remaining bounds
  have h1 : BIG_FOREST_BASE + N_NODES_BIG ≤ MEM_BIG_SIZE := by
    dsimp [MEM_BIG_SIZE, BIG_VAL_BASE, BIG_IDX_BASE, BIG_FOREST_BASE, HEADER_SIZE]
    omega
  simp [memAt, memBig, MEM_BIG_SIZE, BIG_VAL_BASE, BIG_IDX_BASE, BIG_FOREST_BASE, PTR_FOREST,
    PTR_INP_IDX, PTR_INP_VAL]
  exact h1

lemma memBig_rounds : memAt memBig 0 = ROUNDS := by
  simp [memAt, memBig]

lemma memBig_ptrs :
    memAt memBig PTR_FOREST = BIG_FOREST_BASE ∧
    memAt memBig PTR_INP_IDX = BIG_IDX_BASE ∧
    memAt memBig PTR_INP_VAL = BIG_VAL_BASE := by
  constructor
  · simp [memAt, memBig, PTR_FOREST, PTR_INP_IDX, PTR_INP_VAL]
  constructor
  · simp [memAt, memBig, PTR_FOREST, PTR_INP_IDX, PTR_INP_VAL]
  · simp [memAt, memBig, PTR_FOREST, PTR_INP_IDX, PTR_INP_VAL]

lemma memBig_idx (i : Fin BATCH_SIZE) :
    memAt memBig (BIG_IDX_BASE + i) = bigIdx i := by
  set a := BIG_IDX_BASE + i
  have hge : HEADER_SIZE ≤ a := by
    have h1 : HEADER_SIZE ≤ BIG_IDX_BASE := by
      dsimp [BIG_IDX_BASE, BIG_FOREST_BASE]
      exact Nat.le_add_right HEADER_SIZE N_NODES_BIG
    exact Nat.le_trans h1 (Nat.le_add_right _ _)
  have hne : ∀ k, k < HEADER_SIZE → a ≠ k := by
    intro k hk
    exact ne_of_gt (lt_of_lt_of_le hk hge)
  have hne0 : a ≠ 0 := hne 0 (by decide)
  have hne1 : a ≠ 1 := hne 1 (by decide)
  have hne2 : a ≠ 2 := hne 2 (by decide)
  have hne3 : a ≠ 3 := hne 3 (by decide)
  have hneF : a ≠ PTR_FOREST := by
    exact hne 4 (by decide)
  have hneI : a ≠ PTR_INP_IDX := by
    exact hne 5 (by decide)
  have hneV : a ≠ PTR_INP_VAL := by
    exact hne 6 (by decide)
  have hforest : ¬(BIG_FOREST_BASE ≤ a ∧ a < BIG_FOREST_BASE + N_NODES_BIG) := by
    intro h
    have hge2 : BIG_FOREST_BASE + N_NODES_BIG ≤ a := by
      dsimp [a, BIG_IDX_BASE, BIG_FOREST_BASE]
      exact Nat.le_add_right _ _
    exact (not_lt_of_ge hge2) h.2
  have hidx : BIG_IDX_BASE ≤ a ∧ a < BIG_IDX_BASE + BATCH_SIZE := by
    constructor
    · exact Nat.le_add_right _ _
    · exact Nat.add_lt_add_left i.is_lt _
  have hmem : memAt memBig a = bigIdxNat (a - BIG_IDX_BASE) := by
    simp [memAt, memBig, hne0, hne1, hne2, hne3, hneF, hneI, hneV, hforest, hidx]
  simpa [a, bigIdx, bigIdxNat] using hmem

lemma memBig_val (i : Fin BATCH_SIZE) :
    memAt memBig (BIG_VAL_BASE + i) = 0 := by
  set a := BIG_VAL_BASE + i
  have hge : HEADER_SIZE ≤ a := by
    have h1 : HEADER_SIZE ≤ BIG_VAL_BASE := by
      dsimp [BIG_VAL_BASE, BIG_IDX_BASE, BIG_FOREST_BASE]
      have h1 : HEADER_SIZE ≤ HEADER_SIZE + N_NODES_BIG := by
        exact Nat.le_add_right _ _
      have h2 : HEADER_SIZE + N_NODES_BIG ≤ HEADER_SIZE + N_NODES_BIG + BATCH_SIZE := by
        exact Nat.le_add_right _ _
      exact Nat.le_trans h1 h2
    exact Nat.le_trans h1 (Nat.le_add_right _ _)
  have hne : ∀ k, k < HEADER_SIZE → a ≠ k := by
    intro k hk
    exact ne_of_gt (lt_of_lt_of_le hk hge)
  have hne0 : a ≠ 0 := hne 0 (by decide)
  have hne1 : a ≠ 1 := hne 1 (by decide)
  have hne2 : a ≠ 2 := hne 2 (by decide)
  have hne3 : a ≠ 3 := hne 3 (by decide)
  have hneF : a ≠ PTR_FOREST := by
    exact hne 4 (by decide)
  have hneI : a ≠ PTR_INP_IDX := by
    exact hne 5 (by decide)
  have hneV : a ≠ PTR_INP_VAL := by
    exact hne 6 (by decide)
  have hforest : ¬(BIG_FOREST_BASE ≤ a ∧ a < BIG_FOREST_BASE + N_NODES_BIG) := by
    intro h
    have hge2 : BIG_FOREST_BASE + N_NODES_BIG ≤ a := by
      dsimp [a, BIG_VAL_BASE, BIG_IDX_BASE, BIG_FOREST_BASE]
      have h1 : HEADER_SIZE + N_NODES_BIG ≤ HEADER_SIZE + N_NODES_BIG + BATCH_SIZE := by
        exact Nat.le_add_right _ _
      have h2 : HEADER_SIZE + N_NODES_BIG + BATCH_SIZE ≤
          HEADER_SIZE + N_NODES_BIG + BATCH_SIZE + i := by
        exact Nat.le_add_right _ _
      exact Nat.le_trans h1 h2
    exact (not_lt_of_ge hge2) h.2
  have hidx : ¬(BIG_IDX_BASE ≤ a ∧ a < BIG_IDX_BASE + BATCH_SIZE) := by
    intro h
    have hge2 : BIG_IDX_BASE + BATCH_SIZE ≤ a := by
      dsimp [a, BIG_VAL_BASE]
      exact Nat.le_add_right _ _
    exact (not_lt_of_ge hge2) h.2
  have hval : BIG_VAL_BASE ≤ a ∧ a < BIG_VAL_BASE + BATCH_SIZE := by
    constructor
    · exact Nat.le_add_right _ _
    · exact Nat.add_lt_add_left i.is_lt _
  have hmem : memAt memBig a = 0 := by
    simp [memAt, memBig, hne0, hne1, hne2, hne3, hneF, hneI, hneV, hforest, hidx]
  simpa [a] using hmem

lemma memBig_tree (k : Nat) (hk : k < N_NODES_BIG) :
    memAt memBig (BIG_FOREST_BASE + k) = 0 := by
  set a := BIG_FOREST_BASE + k
  have hge : HEADER_SIZE ≤ a := by
    subst a
    dsimp [BIG_FOREST_BASE]
    exact Nat.le_add_right HEADER_SIZE k
  have hne : ∀ k, k < HEADER_SIZE → a ≠ k := by
    intro k hk'
    exact ne_of_gt (lt_of_lt_of_le hk' hge)
  have hne0 : a ≠ 0 := hne 0 (by decide)
  have hne1 : a ≠ 1 := hne 1 (by decide)
  have hne2 : a ≠ 2 := hne 2 (by decide)
  have hne3 : a ≠ 3 := hne 3 (by decide)
  have hneF : a ≠ PTR_FOREST := by
    exact hne 4 (by decide)
  have hneI : a ≠ PTR_INP_IDX := by
    exact hne 5 (by decide)
  have hneV : a ≠ PTR_INP_VAL := by
    exact hne 6 (by decide)
  have hforest : BIG_FOREST_BASE ≤ a ∧ a < BIG_FOREST_BASE + N_NODES_BIG := by
    constructor
    · exact Nat.le_add_right _ _
    · exact Nat.add_lt_add_left hk _
  have hmem : memAt memBig a = 0 := by
    simp [memAt, memBig, hne0, hne1, hne2, hne3, hneF, hneI, hneV, hforest]
  simpa [a] using hmem

def memBigTreeAddrs : Finset Nat :=
  (Finset.univ.image (fun t : Fin ROUNDS × Fin BATCH_SIZE =>
    BIG_FOREST_BASE + idxAtR t.1 t.2))

def memBigValAddrs : Finset Nat :=
  (Finset.univ.image (fun i : Fin BATCH_SIZE => BIG_VAL_BASE + i))

def memBigAllAddrs : Finset Nat :=
  memBigTreeAddrs ∪ memBigValAddrs

lemma bSeq_ge_one (r : Nat) : 1 ≤ bSeq r := by
  unfold bSeq
  by_cases h : iterHash (r + 1) 0 % 2 = 0 <;> simp [h]

lemma cSeq_lt_succ (r : Nat) : cSeq r < cSeq (r + 1) := by
  have hb : 1 ≤ bSeq r := bSeq_ge_one r
  have hb' : 0 < bSeq r := lt_of_lt_of_le (by decide : 0 < (1:Nat)) hb
  have h1 : cSeq r < cSeq r + bSeq r :=
    Nat.lt_add_of_pos_right (n:=cSeq r) (k:=bSeq r) hb'
  have h2 : cSeq r + bSeq r ≤ 2 * cSeq r + bSeq r := by
    have hc : cSeq r ≤ 2 * cSeq r := Nat.le_mul_of_pos_left _ (by decide : 0 < (2:Nat))
    exact Nat.add_le_add_right hc _
  have h : cSeq r < 2 * cSeq r + bSeq r := lt_of_lt_of_le h1 h2
  simpa [cSeq] using h

lemma cSeq_lt_of_lt {a b : Nat} (h : a < b) : cSeq a < cSeq b := by
  induction b with
  | zero =>
      cases (Nat.not_lt_zero _ h)
  | succ b ih =>
      have hb : cSeq b < cSeq (b + 1) := cSeq_lt_succ b
      have hle : a ≤ b := Nat.lt_succ_iff.mp h
      cases lt_or_eq_of_le hle with
      | inl hlt => exact lt_trans (ih hlt) hb
      | inr hEq => simpa [hEq] using hb

lemma cSeq_strict_mono : StrictMono cSeq := by
  intro a b h
  exact cSeq_lt_of_lt h

lemma cSeq_lt_bigM (r : Nat) (hr : r < ROUNDS) : cSeq r < BIG_M := by
  exact lt_of_lt_of_le (cSeq_bound r) (pow_le_bigM hr)

lemma idxAt_mod (r : Nat) (i : Fin BATCH_SIZE) (hr : r < ROUNDS) :
    idxAt r i % BIG_M = cSeq r := by
  have hmul :
      Nat.pow 2 r * bigIdx i =
        BIG_M * (Nat.pow 2 r * (2 * (i : Nat) + 1)) := by
    simp [bigIdx, bigIdxNat, Nat.mul_assoc, Nat.mul_comm]
  have hlt : cSeq r < BIG_M := cSeq_lt_bigM r hr
  have hmodc : cSeq r % BIG_M = cSeq r := Nat.mod_eq_of_lt hlt
  have hstep : idxAt r i % BIG_M =
      (cSeq r + BIG_M * (Nat.pow 2 r * (2 * (i : Nat) + 1))) % BIG_M := by
    calc
      idxAt r i % BIG_M =
          (Nat.pow 2 r * bigIdx i + cSeq r) % BIG_M := by rfl
      _ =
          (BIG_M * (Nat.pow 2 r * (2 * (i : Nat) + 1)) + cSeq r) % BIG_M := by
            rw [hmul]
      _ =
          (cSeq r + BIG_M * (Nat.pow 2 r * (2 * (i : Nat) + 1))) % BIG_M := by
            simp [Nat.add_comm]
  calc
    idxAt r i % BIG_M =
        (cSeq r + BIG_M * (Nat.pow 2 r * (2 * (i : Nat) + 1))) % BIG_M := hstep
    _ = cSeq r % BIG_M := by
          simp
    _ = cSeq r := by simp [hmodc]

lemma bigIdx_inj {i j : Fin BATCH_SIZE} (h : bigIdx i = bigIdx j) : i = j := by
  apply Fin.ext
  have h' : bigIdxNat i = bigIdxNat j := by simpa [bigIdx] using h
  have hpos : 0 < BIG_M := by
    dsimp [BIG_M]
    exact Nat.two_pow_pos _
  have hmul : (2 * (i : Nat) + 1) = (2 * (j : Nat) + 1) := by
    have h'' : BIG_M * (2 * (i : Nat) + 1) = BIG_M * (2 * (j : Nat) + 1) := by
      simpa [bigIdxNat, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using h'
    exact Nat.mul_left_cancel (n:=BIG_M) (np:=hpos) h''
  have h2 : 2 * (i : Nat) = 2 * (j : Nat) := by
    exact Nat.add_right_cancel hmul
  have h3 : (i : Nat) = (j : Nat) := by
    exact Nat.mul_left_cancel (n:=2) (np:=(by decide : 0 < (2:Nat))) h2
  exact h3

lemma idxAtR_inj :
    Function.Injective (fun t : Fin ROUNDS × Fin BATCH_SIZE => idxAtR t.1 t.2) := by
  intro a b h
  rcases a with ⟨r, i⟩
  rcases b with ⟨r', i'⟩
  have hmod : cSeq r = cSeq r' := by
    have hmod' := congrArg (fun x => x % BIG_M) h
    simpa [idxAtR, idxAt_mod (r:=r) (i:=i) r.is_lt,
      idxAt_mod (r:=r') (i:=i') r'.is_lt] using hmod'
  have hr' : (r : Nat) = (r' : Nat) := (cSeq_strict_mono.injective) hmod
  have hr : r = r' := by
    apply Fin.ext
    exact hr'
  have h0 : idxAt r i = idxAt r i' := by
    simpa [idxAtR, hr] using h
  have h1 : Nat.pow 2 r * bigIdx i = Nat.pow 2 r * bigIdx i' := by
    have h' : Nat.pow 2 r * bigIdx i + cSeq r =
        Nat.pow 2 r * bigIdx i' + cSeq r := by
      simpa [idxAt] using h0
    exact Nat.add_right_cancel h'
  have hpos : 0 < Nat.pow 2 r := Nat.two_pow_pos _
  have h2 : bigIdx i = bigIdx i' := Nat.mul_left_cancel (n:=Nat.pow 2 r) (np:=hpos) h1
  have hi : i = i' := bigIdx_inj h2
  cases hr
  cases hi
  rfl

lemma memBigTreeAddrs_card :
    memBigTreeAddrs.card = ROUNDS * BATCH_SIZE := by
  classical
  have hinj :
      Function.Injective
        (fun t : Fin ROUNDS × Fin BATCH_SIZE => BIG_FOREST_BASE + idxAtR t.1 t.2) := by
    intro a b h
    apply idxAtR_inj
    exact Nat.add_left_cancel h
  simpa [memBigTreeAddrs] using
    (Finset.card_image_of_injective (s:=Finset.univ) hinj)
lemma memBigValAddrs_card :
    memBigValAddrs.card = BATCH_SIZE := by
  classical
  have hinj : Function.Injective (fun i : Fin BATCH_SIZE => BIG_VAL_BASE + i) := by
    intro a b h
    apply Fin.ext
    exact Nat.add_left_cancel h
  simpa [memBigValAddrs] using
    (Finset.card_image_of_injective (s:=Finset.univ) hinj)
lemma memBigAddrs_disjoint :
    Disjoint memBigTreeAddrs memBigValAddrs := by
  classical
  refine Finset.disjoint_left.2 ?_
  intro a ha hb
  rcases Finset.mem_image.1 ha with ⟨t, _ht, rfl⟩
  rcases Finset.mem_image.1 hb with ⟨i, _hi, hEq⟩
  have hlt : BIG_FOREST_BASE + idxAtR t.1 t.2 < BIG_IDX_BASE := by
    have hidx : idxAtR t.1 t.2 < N_NODES_BIG := idxAtR_lt t.1 t.2
    have hlt' : BIG_FOREST_BASE + idxAtR t.1 t.2 < BIG_FOREST_BASE + N_NODES_BIG := by
      exact Nat.add_lt_add_left hidx _
    simpa [BIG_IDX_BASE, BIG_FOREST_BASE] using hlt'
  have hge : BIG_VAL_BASE ≤ BIG_FOREST_BASE + idxAtR t.1 t.2 := by
    -- rewrite via the val address equality
    have : BIG_VAL_BASE ≤ BIG_VAL_BASE + i := by
      exact Nat.le_add_right _ _
    simpa [hEq] using this
  have hpos : 0 < BATCH_SIZE := by decide
  have hgt : BIG_IDX_BASE < BIG_VAL_BASE := by
    -- BIG_VAL_BASE = BIG_IDX_BASE + BATCH_SIZE
    simpa [BIG_VAL_BASE] using
      (Nat.lt_add_of_pos_right (n:=BIG_IDX_BASE) (k:=BATCH_SIZE) hpos)
  have hgt' : BIG_IDX_BASE < BIG_FOREST_BASE + idxAtR t.1 t.2 :=
    lt_of_lt_of_le hgt hge
  exact (lt_irrefl _ (lt_trans hgt' hlt))
lemma memBigAllAddrs_card :
    memBigAllAddrs.card = BATCH_SIZE * (ROUNDS + 1) := by
  classical
  -- Union is disjoint, so card is additive.
  have hcard :
      memBigAllAddrs.card = memBigTreeAddrs.card + memBigValAddrs.card := by
    simpa [memBigAllAddrs] using
      (Finset.card_union_of_disjoint memBigAddrs_disjoint)
  -- Substitute the known cards and simplify the arithmetic.
  calc
    memBigAllAddrs.card = memBigTreeAddrs.card + memBigValAddrs.card := hcard
    _ = ROUNDS * BATCH_SIZE + BATCH_SIZE := by
      simp [memBigTreeAddrs_card, memBigValAddrs_card]
    _ = BATCH_SIZE * ROUNDS + BATCH_SIZE := by
      simp [Nat.mul_comm]
    _ = BATCH_SIZE * (ROUNDS + 1) := by
      simp [Nat.mul_add, Nat.mul_one, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]

-- NOTE: Earlier versions of this development carried axioms about `memBig`
-- sensitivity (flipping specific tree/value addresses changes `spec_kernel`) and
-- a structured adversary construction (`RoundDistinctNodes memBig 1`).
--
-- Those facts are currently unused by the Lean lower-bound pipeline, and keeping
-- them as axioms adds "trust-me" surface area. If/when we need them, prefer to
-- reintroduce them as theorems with proofs.

/-!
### `memBig` satisfies `RoundDistinctNodes memBig 1`

This is the "structured adversary" witness that upgrades the load-throughput lower bound
from `16` (valid-input / value-slice) to `256` in the worst case.

Key idea:
- On `memBig`, the forest is all-zero and all input values are zero.
- Lane `i` reads the node at index `idxAtR r i` at round `r`.
- Bumping that forest node from 0 to 1 changes the value update at that round and therefore
  changes the final `spec_kernel` output for that lane.

We *do not* need `myhash`/`iterHash` to be injective: since `ROUNDS = 16`, we can compute
the per-round sensitivity of the "flip node at round r" perturbation via `native_decide`.
-/

def memBigTree (mem : Memory) : Nat → Nat :=
  fun k => memAt mem (BIG_FOREST_BASE + k)

lemma memBigTree_zero (k : Nat) (hk : k < N_NODES_BIG) :
    memBigTree memBig k = 0 := by
  simpa [memBigTree] using memBig_tree k hk

lemma memBig_rounds_nat : memAt memBig 0 = ROUNDS := memBig_rounds

lemma memBig_nodes_nat : memAt memBig 1 = N_NODES_BIG := by
  simp [memAt, memBig]

lemma memBig_val0 (i : Fin BATCH_SIZE) :
    memAt memBig (BIG_VAL_BASE + i) = 0 := memBig_val i

lemma memBig_idx0 (i : Fin BATCH_SIZE) :
    memAt memBig (BIG_IDX_BASE + i) = bigIdx i := memBig_idx i

lemma idxAt_zero (i : Fin BATCH_SIZE) : idxAt 0 i = bigIdx i := by
  simp [idxAt, cSeq]

lemma idxAt_succ (r : Nat) (i : Fin BATCH_SIZE) :
    idxAt (r + 1) i = 2 * idxAt r i + bSeq r := by
  -- Expand and regroup:
  -- idxAt (r+1) i = 2^(r+1) * bigIdx i + cSeq (r+1)
  --               = 2 * (2^r * bigIdx i + cSeq r) + bSeq r
  simp [idxAt, cSeq, Nat.pow_succ, Nat.mul_add, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm,
    Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm, Nat.left_distrib]

lemma idxAt_lt_N_NODES_BIG_le (r : Nat) (i : Fin BATCH_SIZE) (hr : r ≤ ROUNDS) :
    idxAt r i < N_NODES_BIG := by
  -- Reuse the existing `<` proof for `r < ROUNDS` when possible; handle the `r = ROUNDS` edge case.
  cases lt_or_eq_of_le hr with
  | inl hlt =>
      exact idxAt_lt_N_NODES_BIG (r := r) (i := i) hlt
  | inr hEq =>
      -- `r = ROUNDS`: the same bounding argument as `idxAt_lt_N_NODES_BIG` works.
      subst hEq
      -- `idxAt ROUNDS i = 2^ROUNDS * bigIdx i + cSeq ROUNDS`
      have hi2 : 2 * (i : Nat) < 2 * BATCH_SIZE := by
        exact (Nat.mul_lt_mul_left (a:=2) (b:=i) (c:=BATCH_SIZE) (by decide : 0 < (2:Nat))).2
          i.is_lt
      have hle : 2 * (i : Nat) + 1 ≤ 2 * BATCH_SIZE := Nat.succ_le_of_lt hi2
      have hbig : bigIdx i ≤ (2 * BATCH_SIZE) * BIG_M := by
        dsimp [bigIdx, bigIdxNat]
        exact Nat.mul_le_mul_right _ hle
      have hidx :
          Nat.pow 2 ROUNDS * bigIdx i ≤ Nat.pow 2 ROUNDS * ((2 * BATCH_SIZE) * BIG_M) := by
        exact Nat.mul_le_mul_left _ hbig
      have hval : cSeq ROUNDS < BIG_M := by
        have hc : cSeq ROUNDS < Nat.pow 2 (ROUNDS + 1) := cSeq_bound ROUNDS
        have : Nat.pow 2 (ROUNDS + 1) ≤ BIG_M := by
          -- `BIG_M = 2^(ROUNDS+2)`
          unfold BIG_M
          -- monotonicity of `Nat.pow` in the exponent
          exact Nat.pow_le_pow_right (by decide : 0 < (2:Nat)) (Nat.le_succ (ROUNDS + 1))
        exact lt_of_lt_of_le hc this
      have hsum : idxAt ROUNDS i < Nat.pow 2 ROUNDS * ((2 * BATCH_SIZE) * BIG_M) + BIG_M := by
        dsimp [idxAt]
        exact Nat.add_lt_add_of_le_of_lt hidx hval
      simpa [N_NODES_BIG, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hsum

lemma spec_kernel_memBig (i : Fin BATCH_SIZE) :
    spec_kernel memBig i = iterHash ROUNDS 0 := by
  classical
  -- Unfold spec at lane `i`.
  have hrounds : memAt memBig 0 = ROUNDS := memBig_rounds
  have hnodes : memAt memBig 1 = N_NODES_BIG := memBig_nodes_nat
  have hptrF : memAt memBig PTR_FOREST = BIG_FOREST_BASE := (memBig_ptrs).1
  have hptrI : memAt memBig PTR_INP_IDX = BIG_IDX_BASE := (memBig_ptrs).2.1
  have hptrV : memAt memBig PTR_INP_VAL = BIG_VAL_BASE := (memBig_ptrs).2.2
  have hidx0 : memAt memBig (memAt memBig PTR_INP_IDX + i) = bigIdx i := by
    simpa [hptrI] using memBig_idx0 i
  have hval0 : memAt memBig (memAt memBig PTR_INP_VAL + i) = 0 := by
    simpa [hptrV] using memBig_val0 i
  -- The forest is all-zero on `[0, N_NODES_BIG)`.
  let tree : Nat → Nat := fun k => memAt memBig (BIG_FOREST_BASE + k)
  have htree0 : ∀ k < N_NODES_BIG, tree k = 0 := by
    intro k hk
    simpa [tree] using memBigTree_zero k hk
  have hnpos : 0 < N_NODES_BIG := by decide
  have hidx0_lt : (bigIdx i) < N_NODES_BIG := by
    -- `bigIdx i = idxAt 0 i`.
    simpa [idxAt_zero] using (idxAt_lt_N_NODES_BIG_le (r := 0) (i := i) (by decide : 0 ≤ ROUNDS))
  -- Apply the zero-tree value lemma at `n = ROUNDS - 1` (same as in `spec_kernel_uniform_val`,
  -- but for an arbitrary in-range `idx0`).
  have hrounds_pos : 1 ≤ ROUNDS := by decide
  have hrounds_succ : (ROUNDS - 1) + 1 = ROUNDS := Nat.sub_add_cancel hrounds_pos
  have hvalF :
      (iterRounds tree N_NODES_BIG ((ROUNDS - 1) + 1) (bigIdx i) 0).2 =
        iterHash ((ROUNDS - 1) + 1) (mod32 0) := by
    simpa using
      iterRounds_zero_tree_val_range_succ tree N_NODES_BIG htree0 hnpos (n := ROUNDS - 1)
        (idx := bigIdx i) (val := 0) hidx0_lt
  -- Turn `hvalF` into the `ROUNDS`-form.
  have hvalF' :
      (iterRounds tree N_NODES_BIG ROUNDS (bigIdx i) 0).2 = iterHash ROUNDS 0 := by
    simpa [hrounds_succ, mod32] using hvalF
  -- Finish by unfolding `spec_kernel` and rewriting pointers/inputs to match `hvalF'`.
  -- (We rewrite the lane's `idx0/val0` via the concrete `memBig_*` lemmas.)
  unfold spec_kernel
  -- `simp` turns the spec into `(iterRounds tree ...).2` and then we can apply `hvalF'`.
  simpa [hrounds, hnodes, hptrF, hptrI, hptrV, memBig_idx0, memBig_val0, tree] using hvalF'

/-!
Per-round sensitivity of the "flip a single forest node at round `r`" perturbation.

This is a *value-level* fact (no machine/program), so we compute it via `native_decide`
once we reduce the spec to a pure `iterHash` expression.
-/
lemma iterHash_bump_round_ne (r : Fin ROUNDS) :
    iterHash ROUNDS 0 ≠
      iterHash (ROUNDS - (r.1 + 1))
        (myhash (aluEval AluOp.xor (iterHash r.1 0) 1)) := by
  -- There are only `ROUNDS = 16` cases.
  fin_cases r <;> native_decide

lemma memBig_tree_addr_safe (r : Fin ROUNDS) (i : Fin BATCH_SIZE) :
    AddrSafe memBig (BIG_FOREST_BASE + idxAtR r i) := by
  have hge : HEADER_SIZE ≤ BIG_FOREST_BASE + idxAtR r i := by
    dsimp [BIG_FOREST_BASE, HEADER_SIZE]
    exact Nat.le_add_right _ _
  have hlt_base : BIG_FOREST_BASE + idxAtR r i < BIG_FOREST_BASE + N_NODES_BIG := by
    exact Nat.add_lt_add_left (idxAtR_lt r i) _
  have hsize : BIG_FOREST_BASE + N_NODES_BIG ≤ memBig.size := by
    dsimp [memBig, MEM_BIG_SIZE, BIG_VAL_BASE, BIG_IDX_BASE, BIG_FOREST_BASE, HEADER_SIZE]
    omega
  have hlt : BIG_FOREST_BASE + idxAtR r i < memBig.size :=
    lt_of_lt_of_le hlt_base hsize
  exact ⟨hge, hlt⟩

lemma memBig_val_addr_safe (i : Fin BATCH_SIZE) :
    AddrSafe memBig (BIG_VAL_BASE + i) := by
  have hge : HEADER_SIZE ≤ BIG_VAL_BASE + i := by
    dsimp [BIG_VAL_BASE, BIG_IDX_BASE, BIG_FOREST_BASE, HEADER_SIZE]
    have h1 : 7 ≤ 7 + N_NODES_BIG + BATCH_SIZE := by
      have h1' : 7 ≤ 7 + N_NODES_BIG := by
        exact Nat.le_add_right _ _
      have h2' : 7 + N_NODES_BIG ≤ 7 + N_NODES_BIG + BATCH_SIZE := by
        exact Nat.le_add_right _ _
      exact Nat.le_trans h1' h2'
    have h2 : 7 + N_NODES_BIG + BATCH_SIZE ≤ 7 + N_NODES_BIG + BATCH_SIZE + i := by
      exact Nat.le_add_right _ _
    exact Nat.le_trans h1 h2
  have hlt : BIG_VAL_BASE + i < memBig.size := by
    have hlt' : BIG_VAL_BASE + i < BIG_VAL_BASE + BATCH_SIZE := by
      exact Nat.add_lt_add_left i.is_lt _
    dsimp [memBig, MEM_BIG_SIZE]
    exact hlt'
  exact ⟨hge, hlt⟩

theorem min_required_words_kernel_machine_memBig_all (p : Program)
    (hsubset : memBigAllAddrs ⊆ (readWordsMachine p memBig).toFinset) :
    BATCH_SIZE * (ROUNDS + 1) ≤ readWordCountMachine p memBig := by
  have hcard_le : memBigAllAddrs.card ≤ (readWordsMachine p memBig).toFinset.card := by
    simpa using (Finset.card_le_card hsubset)
  have hlen : (readWordsMachine p memBig).toFinset.card ≤ (readWordsMachine p memBig).length := by
    simpa using (List.toFinset_card_le (l := readWordsMachine p memBig))
  have hcard_le_len : memBigAllAddrs.card ≤ (readWordsMachine p memBig).length :=
    le_trans hcard_le hlen
  have : BATCH_SIZE * (ROUNDS + 1) ≤ (readWordsMachine p memBig).length := by
    simpa [memBigAllAddrs_card] using hcard_le_len
  simpa [readWordCountMachine] using this

lemma memUpdate_header_eq (mem : Memory) {addr val k : Nat}
    (hk : k < HEADER_SIZE) (haddr : HEADER_SIZE ≤ addr) :
    memAt (memUpdate mem addr val) k = memAt mem k := by
  have hne : k ≠ addr := by
    exact ne_of_lt (lt_of_lt_of_le hk haddr)
  simp [memUpdate, memAt, hne]
lemma addr_ge_header_of_layout (mem : Memory) (i : Fin BATCH_SIZE)
    (hlayout : KernelLayout mem) : HEADER_SIZE ≤ memAt mem PTR_INP_VAL + i := by
  dsimp [KernelLayout] at hlayout
  rcases hlayout with ⟨_hforest, _hidx, hval⟩
  exact Nat.le_trans hval (Nat.le_add_right _ _)
lemma memSafeKernel_update_addr (mem : Memory) (addr : Nat)
    (hsafe : MemSafeKernel mem) (haddr : AddrSafe mem addr) :
    MemSafeKernel (memUpdate mem addr (memAt mem addr + 1)) := by
  rcases haddr with ⟨hge, _⟩
  have hne : ∀ k, k < HEADER_SIZE → k ≠ addr := by
    intro k hk
    exact ne_of_lt (lt_of_lt_of_le hk hge)
  have hne1 : 1 ≠ addr := hne 1 (by decide)
  have hne2 : 2 ≠ addr := hne 2 (by decide)
  have hneF : PTR_FOREST ≠ addr := hne 4 (by decide)
  have hneI : PTR_INP_IDX ≠ addr := hne 5 (by decide)
  have hneV : PTR_INP_VAL ≠ addr := hne 6 (by decide)
  dsimp [MemSafeKernel] at hsafe ⊢
  simpa [memUpdate, memAt, hne1, hne2, hneF, hneI, hneV] using hsafe

lemma memSafeKernel_update_val (mem : Memory) (i : Fin BATCH_SIZE)
    (hlayout : KernelLayout mem) (hsafe : MemSafeKernel mem) :
    MemSafeKernel
      (memUpdate mem (memAt mem PTR_INP_VAL + i)
        (memAt mem (memAt mem PTR_INP_VAL + i) + 1)) := by
  -- show the updated address is safe, then reuse the general lemma
  have hge : HEADER_SIZE ≤ memAt mem PTR_INP_VAL + i :=
    addr_ge_header_of_layout mem i hlayout
  -- upper bound from MemSafeKernel
  dsimp [MemSafeKernel] at hsafe
  rcases hsafe with ⟨hsize, hbatch, hrest⟩
  rcases hrest with ⟨hforest, hidx, hval⟩
  -- hval : valPtr + BATCH_SIZE ≤ mem.size
  have hlt : memAt mem PTR_INP_VAL + i < mem.size := by
    have hle : memAt mem PTR_INP_VAL + i < memAt mem PTR_INP_VAL + BATCH_SIZE := by
      exact Nat.add_lt_add_left i.is_lt _
    exact lt_of_lt_of_le hle hval
  have haddr : AddrSafe mem (memAt mem PTR_INP_VAL + i) := ⟨hge, hlt⟩
  -- apply general update lemma
  exact memSafeKernel_update_addr mem (memAt mem PTR_INP_VAL + i) (by
    -- reconstruct MemSafeKernel mem
    exact ⟨hsize, hbatch, hforest, hidx, hval⟩) haddr
def memUniform1 : Memory :=
  memUpdate memUniform0 VAL_BASE 1

def memUniformVal (j : Fin BATCH_SIZE) : Memory :=
  memUpdate memUniform0 (VAL_BASE + j) 1

lemma BATCH_SIZE_pos : 0 < BATCH_SIZE := by
  native_decide

instance : NeZero BATCH_SIZE := ⟨ne_of_gt BATCH_SIZE_pos⟩

lemma memUniform0_safe : MemSafeKernel memUniform0 := by
  unfold MemSafeKernel
  refine And.intro ?hsize (And.intro ?hbatch ?hrest)
  · have h : (7 : Nat) < MEM_SIZE := by
      native_decide
    simpa [memUniform0] using h
  · simp [memUniform0, memAt]
  · -- header-derived bounds are purely numeric
    have h :
        FOREST_BASE + N_NODES ≤ MEM_SIZE ∧
        IDX_BASE + BATCH_SIZE ≤ MEM_SIZE ∧
        VAL_BASE + BATCH_SIZE ≤ MEM_SIZE := by
      native_decide
    simpa [memUniform0, PTR_FOREST, PTR_INP_IDX, PTR_INP_VAL,
      FOREST_BASE, IDX_BASE, VAL_BASE] using h
lemma val_base_ge_header : HEADER_SIZE ≤ VAL_BASE := by
  have h1 : HEADER_SIZE ≤ IDX_BASE := by
    dsimp [IDX_BASE, FOREST_BASE]
    exact Nat.le_add_right HEADER_SIZE N_NODES
  have h2 : IDX_BASE ≤ VAL_BASE := by
    dsimp [VAL_BASE]
    exact Nat.le_add_right IDX_BASE BATCH_SIZE
  exact Nat.le_trans h1 h2
lemma memUniformVal_header_eq (j : Fin BATCH_SIZE) (k : Nat) (hk : k < HEADER_SIZE) :
    memAt (memUniformVal j) k = memAt memUniform0 k := by
  have hlt : k < VAL_BASE := lt_of_lt_of_le hk val_base_ge_header
  have hle : VAL_BASE ≤ VAL_BASE + (j : Nat) := Nat.le_add_right _ _
  have hne : k ≠ VAL_BASE + (j : Nat) := by
    exact ne_of_lt (lt_of_lt_of_le hlt hle)
  simp [memUniformVal, memUpdate, memAt, hne]
lemma memUniformVal_safe (j : Fin BATCH_SIZE) : MemSafeKernel (memUniformVal j) := by
  have hsize : memUniform0.size = (memUniformVal j).size := rfl
  have h0 : memAt memUniform0 0 = memAt (memUniformVal j) 0 := by
    symm; exact memUniformVal_header_eq j 0 (by decide)
  have h1 : memAt memUniform0 1 = memAt (memUniformVal j) 1 := by
    symm; exact memUniformVal_header_eq j 1 (by decide)
  have h2 : memAt memUniform0 2 = memAt (memUniformVal j) 2 := by
    symm; exact memUniformVal_header_eq j 2 (by decide)
  have hforest : memAt memUniform0 PTR_FOREST = memAt (memUniformVal j) PTR_FOREST := by
    symm; exact memUniformVal_header_eq j PTR_FOREST (by decide)
  have hidx : memAt memUniform0 PTR_INP_IDX = memAt (memUniformVal j) PTR_INP_IDX := by
    symm; exact memUniformVal_header_eq j PTR_INP_IDX (by decide)
  have hval : memAt memUniform0 PTR_INP_VAL = memAt (memUniformVal j) PTR_INP_VAL := by
    symm; exact memUniformVal_header_eq j PTR_INP_VAL (by decide)
  have hsafe := memSafeKernel_of_eq_header memUniform0 (memUniformVal j)
    hsize h1 h2 hforest hidx hval memUniform0_safe
  simpa using hsafe
lemma memUniform_ptrs :
    memAt memUniform0 PTR_FOREST = FOREST_BASE ∧
    memAt memUniform0 PTR_INP_IDX = IDX_BASE ∧
    memAt memUniform0 PTR_INP_VAL = VAL_BASE := by
  simp [memUniform0, memAt, PTR_FOREST, PTR_INP_IDX, PTR_INP_VAL]
lemma memUniform_idx (i : Nat) :
    memAt memUniform0 (IDX_BASE + i) = 0 := by
  set a := IDX_BASE + i
  have hge : HEADER_SIZE ≤ a := by
    have h1 : HEADER_SIZE ≤ IDX_BASE := by
      dsimp [IDX_BASE, FOREST_BASE]
      exact Nat.le_add_right HEADER_SIZE N_NODES
    exact Nat.le_trans h1 (Nat.le_add_right _ _)
  have hne : ∀ k, k < HEADER_SIZE → a ≠ k := by
    intro k hk
    exact ne_of_gt (lt_of_lt_of_le hk hge)
  have hne0 : a ≠ 0 := hne 0 (by decide)
  have hne1 : a ≠ 1 := hne 1 (by decide)
  have hne2 : a ≠ 2 := hne 2 (by decide)
  have hne3 : a ≠ 3 := hne 3 (by decide)
  have hneF : a ≠ PTR_FOREST := by
    exact hne 4 (by decide)
  have hneI : a ≠ PTR_INP_IDX := by
    exact hne 5 (by decide)
  have hneV : a ≠ PTR_INP_VAL := by
    exact hne 6 (by decide)
  simp [memUniform0, memAt, hne0, hne1, hne2, hne3, hneF, hneI, hneV]
lemma memUniform_val (i : Nat) :
    memAt memUniform0 (VAL_BASE + i) = 0 := by
  set a := VAL_BASE + i
  have hge : HEADER_SIZE ≤ a := by
    exact Nat.le_trans val_base_ge_header (Nat.le_add_right _ _)
  have hne : ∀ k, k < HEADER_SIZE → a ≠ k := by
    intro k hk
    exact ne_of_gt (lt_of_lt_of_le hk hge)
  have hne0 : a ≠ 0 := hne 0 (by decide)
  have hne1 : a ≠ 1 := hne 1 (by decide)
  have hne2 : a ≠ 2 := hne 2 (by decide)
  have hne3 : a ≠ 3 := hne 3 (by decide)
  have hneF : a ≠ PTR_FOREST := by
    exact hne 4 (by decide)
  have hneI : a ≠ PTR_INP_IDX := by
    exact hne 5 (by decide)
  have hneV : a ≠ PTR_INP_VAL := by
    exact hne 6 (by decide)
  simp [memUniform0, memAt, hne0, hne1, hne2, hne3, hneF, hneI, hneV]
lemma memUniform_forest (i : Nat) :
    memAt memUniform0 (FOREST_BASE + i) = 0 := by
  set a := FOREST_BASE + i
  have hge : HEADER_SIZE ≤ a := by
    subst a
    dsimp [FOREST_BASE]
    exact Nat.le_add_right HEADER_SIZE i
  have hne : ∀ k, k < HEADER_SIZE → a ≠ k := by
    intro k hk
    exact ne_of_gt (lt_of_lt_of_le hk hge)
  have hne0 : a ≠ 0 := hne 0 (by decide)
  have hne1 : a ≠ 1 := hne 1 (by decide)
  have hne2 : a ≠ 2 := hne 2 (by decide)
  have hne3 : a ≠ 3 := hne 3 (by decide)
  have hneF : a ≠ PTR_FOREST := by
    exact hne 4 (by decide)
  have hneI : a ≠ PTR_INP_IDX := by
    exact hne 5 (by decide)
  have hneV : a ≠ PTR_INP_VAL := by
    simpa [PTR_INP_VAL] using (hne 6 (by decide))
  simp [memUniform0, memAt, hne0, hne1, hne2, hne3, hneF, hneI, hneV]
lemma memUniform_idx_fin (i : Fin BATCH_SIZE) :
    memAt memUniform0 (IDX_BASE + i) = 0 := by
  simpa using memUniform_idx (i := (i : Nat))
lemma memUniform_val_fin (i : Fin BATCH_SIZE) :
    memAt memUniform0 (VAL_BASE + i) = 0 := by
  simpa using memUniform_val (i := (i : Nat))

lemma kernelLayout_memUniform0 : KernelLayout memUniform0 := by
  -- All pointers are at or above the fixed header region.
  dsimp [KernelLayout]
  refine And.intro ?_ (And.intro ?_ ?_)
  · -- forestPtr = HEADER_SIZE
    simpa [memUniform_ptrs, FOREST_BASE]
  · -- idxPtr = HEADER_SIZE + N_NODES
    have hle : HEADER_SIZE ≤ IDX_BASE := by
      simpa [IDX_BASE, FOREST_BASE] using (Nat.le_add_right HEADER_SIZE N_NODES)
    simpa [memUniform_ptrs] using hle
  · -- valPtr = idxPtr + BATCH_SIZE
    have hle_idx : HEADER_SIZE ≤ IDX_BASE := by
      simpa [IDX_BASE, FOREST_BASE] using (Nat.le_add_right HEADER_SIZE N_NODES)
    have hle : HEADER_SIZE ≤ VAL_BASE :=
      Nat.le_trans hle_idx (by simpa [VAL_BASE] using (Nat.le_add_right IDX_BASE BATCH_SIZE))
    simpa [memUniform_ptrs] using hle

lemma kernelDisjoint_memUniform0 : KernelDisjoint memUniform0 := by
  -- With the standard pointer layout, the regions are exactly adjacent.
  dsimp [KernelDisjoint]
  constructor <;> simp [memUniform0, memAt, PTR_FOREST, PTR_INP_IDX, PTR_INP_VAL,
    FOREST_BASE, IDX_BASE, VAL_BASE]

lemma uniformZeroKernel_memUniform0 : UniformZeroKernel memUniform0 := by
  refine ⟨memUniform0_safe, ?_, ?_, ?_, ?_, kernelLayout_memUniform0, kernelDisjoint_memUniform0, ?_, ?_, ?_⟩
  · simp [memUniform0, memAt]
  · simp [memUniform0, memAt]
  · simp [memUniform0, memAt]
  · simp [memUniform0, memAt]
  · intro k _hk
    have hptrF : memAt memUniform0 PTR_FOREST = FOREST_BASE := (memUniform_ptrs).1
    simpa [hptrF] using (memUniform_forest (i := k))
  · intro i
    have hptrI : memAt memUniform0 PTR_INP_IDX = IDX_BASE := (memUniform_ptrs).2.1
    simpa [hptrI] using (memUniform_idx_fin (i := i))
  · intro i
    have hptrV : memAt memUniform0 PTR_INP_VAL = VAL_BASE := (memUniform_ptrs).2.2
    simpa [hptrV] using (memUniform_val_fin (i := i))
lemma spec_kernel_uniform0 (i : Fin BATCH_SIZE) :
    spec_kernel memUniform0 i = iterHash ROUNDS 0 := by
  have hrounds : memAt memUniform0 0 = ROUNDS := by
    simp [memUniform0, memAt]
  have hnodes : memAt memUniform0 1 = N_NODES := by
    simp [memUniform0, memAt]
  have hptrF : memAt memUniform0 PTR_FOREST = FOREST_BASE := (memUniform_ptrs).1
  have hptrI : memAt memUniform0 PTR_INP_IDX = IDX_BASE := (memUniform_ptrs).2.1
  have hptrV : memAt memUniform0 PTR_INP_VAL = VAL_BASE := (memUniform_ptrs).2.2
  have hforest :
      ∀ k, k < N_NODES → memAt memUniform0 (memAt memUniform0 PTR_FOREST + k) = 0 := by
    intro k _hk
    simpa [hptrF] using memUniform_forest k
  have hidx : memAt memUniform0 (memAt memUniform0 PTR_INP_IDX + i) = 0 := by
    simpa [hptrI] using memUniform_idx_fin i
  have hval : memAt memUniform0 (memAt memUniform0 PTR_INP_VAL + i) = 0 := by
    simpa [hptrV] using memUniform_val_fin i
  have hs :=
    spec_kernel_uniform_val memUniform0 i 0 hrounds hnodes hforest hidx hval
  simpa [mod32] using hs

lemma memUniformVal_at (j i : Fin BATCH_SIZE) :
    memAt (memUniformVal j) (VAL_BASE + i) = if i = j then 1 else 0 := by
  by_cases h : i = j
  · subst h
    simp [memUniformVal, memUpdate, memAt]
  · have hneNat : (i : Nat) ≠ (j : Nat) := by
      intro hEq
      apply h
      exact Fin.ext hEq
    have hLHS : memAt (memUniformVal j) (VAL_BASE + i) = 0 := by
      simp [memUniformVal, memUpdate, memAt, hneNat]
      simpa [memAt] using memUniform_val_fin i
    simpa [h, hLHS]

lemma spec_kernel_uniformVal (j i : Fin BATCH_SIZE) :
    spec_kernel (memUniformVal j) i = iterHash ROUNDS (if i = j then 1 else 0) := by
  have hrounds : memAt (memUniformVal j) 0 = ROUNDS := by
    have h0 := memUniformVal_header_eq j 0 (by decide)
    simpa [memUniform0, memAt] using h0
  have hnodes : memAt (memUniformVal j) 1 = N_NODES := by
    have h1 := memUniformVal_header_eq j 1 (by decide)
    simpa [memUniform0, memAt] using h1
  have hptrF : memAt (memUniformVal j) PTR_FOREST = FOREST_BASE := by
    have h := memUniformVal_header_eq j PTR_FOREST (by decide)
    simpa [memUniform0, memAt] using h
  have hptrI : memAt (memUniformVal j) PTR_INP_IDX = IDX_BASE := by
    have h := memUniformVal_header_eq j PTR_INP_IDX (by decide)
    simpa [memUniform0, memAt] using h
  have hptrV : memAt (memUniformVal j) PTR_INP_VAL = VAL_BASE := by
    have h := memUniformVal_header_eq j PTR_INP_VAL (by decide)
    simpa [memUniform0, memAt] using h
  have hforest :
      ∀ k, k < N_NODES → memAt (memUniformVal j) (memAt (memUniformVal j) PTR_FOREST + k) = 0 := by
    intro k hk
    have hlt : FOREST_BASE + k < VAL_BASE := by
      have hk' : FOREST_BASE + k < FOREST_BASE + N_NODES := Nat.add_lt_add_left hk _
      have hle : FOREST_BASE + N_NODES ≤ FOREST_BASE + N_NODES + BATCH_SIZE :=
        Nat.le_add_right _ _
      have : FOREST_BASE + k < FOREST_BASE + N_NODES + BATCH_SIZE := lt_of_lt_of_le hk' hle
      simpa [VAL_BASE, IDX_BASE, Nat.add_assoc] using this
    have hne : FOREST_BASE + k ≠ VAL_BASE + (j : Nat) := by
      have hle : VAL_BASE ≤ VAL_BASE + (j : Nat) := Nat.le_add_right _ _
      have : FOREST_BASE + k < VAL_BASE + (j : Nat) := lt_of_lt_of_le hlt hle
      exact ne_of_lt this
    have h0 : memUniform0.data (FOREST_BASE + k) = 0 := by
      simpa [memAt] using memUniform_forest k
    have : memAt (memUniformVal j) (FOREST_BASE + k) = 0 := by
      simp [memUniformVal, memUpdate, memAt, hne, h0]
    simpa [hptrF] using this
  have hidx : memAt (memUniformVal j) (memAt (memUniformVal j) PTR_INP_IDX + i) = 0 := by
    have hlt : IDX_BASE + (i : Nat) < VAL_BASE := by
      have hi : (i : Nat) < BATCH_SIZE := i.is_lt
      have : IDX_BASE + (i : Nat) < IDX_BASE + BATCH_SIZE := Nat.add_lt_add_left hi _
      simpa [VAL_BASE] using this
    have hne : IDX_BASE + (i : Nat) ≠ VAL_BASE + (j : Nat) := by
      have hle : VAL_BASE ≤ VAL_BASE + (j : Nat) := Nat.le_add_right _ _
      have : IDX_BASE + (i : Nat) < VAL_BASE + (j : Nat) := lt_of_lt_of_le hlt hle
      exact ne_of_lt this
    have h0 : memUniform0.data (IDX_BASE + i) = 0 := by
      simpa [memAt] using memUniform_idx_fin i
    have : memAt (memUniformVal j) (IDX_BASE + i) = 0 := by
      simp [memUniformVal, memUpdate, memAt, hne, h0]
    simpa [hptrI] using this
  by_cases h : i = j
  · have hval : memAt (memUniformVal j) (memAt (memUniformVal j) PTR_INP_VAL + i) = 1 := by
      simpa [hptrV, h] using (memUniformVal_at j i)
    have hs :=
      spec_kernel_uniform_val (memUniformVal j) i 1 hrounds hnodes hforest hidx hval
    have h1 : (1 : Nat) < MOD32 := by native_decide
    have hmod : mod32 1 = 1 := by
      simp [mod32, Nat.mod_eq_of_lt h1]
    simpa [h, hmod] using hs
  · have hval : memAt (memUniformVal j) (memAt (memUniformVal j) PTR_INP_VAL + i) = 0 := by
      simpa [hptrV, h] using (memUniformVal_at j i)
    have hs :=
      spec_kernel_uniform_val (memUniformVal j) i 0 hrounds hnodes hforest hidx hval
    simpa [mod32, h] using hs

lemma spec_kernel_uniform1 (i : Fin BATCH_SIZE) :
    spec_kernel memUniform1 i = iterHash ROUNDS (if i = (0 : Fin BATCH_SIZE) then 1 else 0) := by
  simpa [memUniform1, memUniformVal] using
    (spec_kernel_uniformVal (j := (0 : Fin BATCH_SIZE)) (i := i))
lemma iterHash_ne : iterHash ROUNDS 0 ≠ iterHash ROUNDS 1 := by
  native_decide
lemma iterHash_ne_zero : iterHash ROUNDS 0 ≠ 0 := by
  native_decide
lemma spec_kernel_diff_uniform0 :
    spec_kernel memUniform1 (0 : Fin BATCH_SIZE) ≠ spec_kernel memUniform0 (0 : Fin BATCH_SIZE) := by
  intro hEq
  have h1 : spec_kernel memUniform1 (0 : Fin BATCH_SIZE) = iterHash ROUNDS 1 := by
    simpa using (spec_kernel_uniform1 (i := (0 : Fin BATCH_SIZE)))
  have h0 : spec_kernel memUniform0 (0 : Fin BATCH_SIZE) = iterHash ROUNDS 0 := by
    simpa using (spec_kernel_uniform0 (i := (0 : Fin BATCH_SIZE)))
  have : iterHash ROUNDS 1 = iterHash ROUNDS 0 := by
    calc
      iterHash ROUNDS 1 = spec_kernel memUniform1 (0 : Fin BATCH_SIZE) := by symm; exact h1
      _ = spec_kernel memUniform0 (0 : Fin BATCH_SIZE) := hEq
      _ = iterHash ROUNDS 0 := h0
  exact iterHash_ne (by symm; exact this)

lemma spec_kernel_diff_uniformVal (j : Fin BATCH_SIZE) :
    spec_kernel (memUniformVal j) j ≠ spec_kernel memUniform0 j := by
  intro hEq
  have h1 : spec_kernel (memUniformVal j) j = iterHash ROUNDS 1 := by
    simpa using (spec_kernel_uniformVal (j := j) (i := j))
  have h0 : spec_kernel memUniform0 j = iterHash ROUNDS 0 := by
    simpa using (spec_kernel_uniform0 (i := j))
  have : iterHash ROUNDS 1 = iterHash ROUNDS 0 := by
    calc
      iterHash ROUNDS 1 = spec_kernel (memUniformVal j) j := by symm; exact h1
      _ = spec_kernel memUniform0 j := hEq
      _ = iterHash ROUNDS 0 := h0
  exact iterHash_ne (by symm; exact this)

lemma kernelSensitive_uniform_zero (mem : Memory)
    (hunif : UniformZeroKernel mem) : KernelSensitive mem := by
  intro i
  rcases hunif with
    ⟨_hsafe, hrounds, hnodes, _hbatch, _hheight, hlayout, hdisjoint, hforest, hidx, hval⟩
  -- original output is `iterHash ROUNDS 0` on this uniform-zero memory
  have hspec0 : spec_kernel mem i = iterHash ROUNDS 0 := by
    have hs :=
      spec_kernel_uniform_val mem i 0 hrounds hnodes hforest (hidx i) (by simpa using hval i)
    simpa [mod32] using hs
  -- after bumping the input value at lane `i`, output becomes `iterHash ROUNDS 1`
  set addr := memAt mem PTR_INP_VAL + i
  let mem' := memUpdate mem addr (memAt mem addr + 1)
  have haddr_ge : HEADER_SIZE ≤ addr := addr_ge_header_of_layout mem i hlayout
  have hne_hdr : ∀ k, k < HEADER_SIZE → k ≠ addr := by
    intro k hk
    exact ne_of_lt (lt_of_lt_of_le hk haddr_ge)
  have hrounds' : memAt mem' 0 = ROUNDS := by
    calc
      memAt mem' 0 = memAt mem 0 := by
        simpa [mem', addr] using
          (memUpdate_eq_of_ne mem addr (memAt mem addr + 1) 0 (hne_hdr 0 (by decide)))
      _ = ROUNDS := hrounds
  have hnodes' : memAt mem' 1 = N_NODES := by
    calc
      memAt mem' 1 = memAt mem 1 := by
        simpa [mem', addr] using
          (memUpdate_eq_of_ne mem addr (memAt mem addr + 1) 1 (hne_hdr 1 (by decide)))
      _ = N_NODES := hnodes
  have hptrF' : memAt mem' PTR_FOREST = memAt mem PTR_FOREST := by
    simpa [mem', addr] using
      (memUpdate_eq_of_ne mem addr (memAt mem addr + 1) PTR_FOREST (hne_hdr PTR_FOREST (by decide)))
  have hptrI' : memAt mem' PTR_INP_IDX = memAt mem PTR_INP_IDX := by
    simpa [mem', addr] using
      (memUpdate_eq_of_ne mem addr (memAt mem addr + 1) PTR_INP_IDX (hne_hdr PTR_INP_IDX (by decide)))
  have hptrV' : memAt mem' PTR_INP_VAL = memAt mem PTR_INP_VAL := by
    simpa [mem', addr] using
      (memUpdate_eq_of_ne mem addr (memAt mem addr + 1) PTR_INP_VAL (hne_hdr PTR_INP_VAL (by decide)))
  have hforest' :
      ∀ k, k < N_NODES → memAt mem' (memAt mem' PTR_FOREST + k) = 0 := by
    intro k hk
    have hlt1 : memAt mem PTR_FOREST + k < memAt mem PTR_INP_IDX := by
      -- forestPtr + k < forestPtr + N_NODES ≤ idxPtr
      have hk' : memAt mem PTR_FOREST + k < memAt mem PTR_FOREST + N_NODES := by
        exact Nat.add_lt_add_left hk _
      have hle : memAt mem PTR_FOREST + N_NODES ≤ memAt mem PTR_INP_IDX := by
        -- from KernelDisjoint + mem[1] = N_NODES
        dsimp [KernelDisjoint] at hdisjoint
        have hnodesN : memAt mem 1 = N_NODES := hnodes
        simpa [hnodesN] using hdisjoint.1
      exact lt_of_lt_of_le hk' hle
    have hle2 : memAt mem PTR_INP_IDX ≤ memAt mem PTR_INP_VAL := by
      dsimp [KernelDisjoint] at hdisjoint
      exact le_trans (Nat.le_add_right _ _) hdisjoint.2
    have hlt : memAt mem PTR_FOREST + k < memAt mem PTR_INP_VAL := lt_of_lt_of_le hlt1 hle2
    have hlt' : memAt mem PTR_FOREST + k < addr := by
      -- addr = valPtr + i
      have hle : memAt mem PTR_INP_VAL ≤ memAt mem PTR_INP_VAL + i := Nat.le_add_right _ _
      simpa [addr] using lt_of_lt_of_le hlt hle
    have hne : memAt mem PTR_FOREST + k ≠ addr := ne_of_lt hlt'
    have h0 : memAt mem (memAt mem PTR_FOREST + k) = 0 := hforest k hk
    -- mem' agrees with mem at this forest address
    have hmem :
        memAt mem' (memAt mem PTR_FOREST + k) = memAt mem (memAt mem PTR_FOREST + k) := by
      simpa [mem', addr] using
        (memUpdate_eq_of_ne mem addr (memAt mem addr + 1) (memAt mem PTR_FOREST + k) hne)
    -- rewrite ptr and conclude
    simpa [hptrF', h0] using hmem
  have hidx' : memAt mem' (memAt mem' PTR_INP_IDX + i) = 0 := by
    have hlt : memAt mem PTR_INP_IDX + (i : Nat) < memAt mem PTR_INP_VAL := by
      dsimp [KernelDisjoint] at hdisjoint
      have hi : memAt mem PTR_INP_IDX + (i : Nat) < memAt mem PTR_INP_IDX + BATCH_SIZE :=
        Nat.add_lt_add_left i.is_lt _
      have : memAt mem PTR_INP_IDX + (i : Nat) < memAt mem PTR_INP_VAL :=
        lt_of_lt_of_le hi hdisjoint.2
      simpa using this
    have hlt' : memAt mem PTR_INP_IDX + (i : Nat) < addr := by
      have hle : memAt mem PTR_INP_VAL ≤ memAt mem PTR_INP_VAL + i := Nat.le_add_right _ _
      simpa [addr] using lt_of_lt_of_le hlt hle
    have hne : memAt mem PTR_INP_IDX + (i : Nat) ≠ addr := ne_of_lt hlt'
    have h0 : memAt mem (memAt mem PTR_INP_IDX + i) = 0 := hidx i
    have hmem :
        memAt mem' (memAt mem PTR_INP_IDX + i) = memAt mem (memAt mem PTR_INP_IDX + i) := by
      simpa [mem', addr] using
        (memUpdate_eq_of_ne mem addr (memAt mem addr + 1) (memAt mem PTR_INP_IDX + i) hne)
    simpa [hptrI', h0] using hmem
  have hval' : memAt mem' (memAt mem' PTR_INP_VAL + i) = 1 := by
    have h0 : memAt mem addr = 0 := by simpa [addr] using hval i
    have hadd : memAt mem' PTR_INP_VAL + i = addr := by
      simpa [addr, hptrV']
    have hmem : memAt mem' addr = memAt mem addr + 1 := by
      simp [mem', memUpdate, memAt]
    calc
      memAt mem' (memAt mem' PTR_INP_VAL + i) = memAt mem' addr := by
        simpa [hadd]
      _ = memAt mem addr + 1 := hmem
      _ = 1 := by
        simpa [h0]
  have hs' := spec_kernel_uniform_val mem' i 1 hrounds' hnodes' hforest' hidx' hval'
  have h1 : (1 : Nat) < MOD32 := by native_decide
  have hmod : mod32 1 = 1 := by
    simp [mod32, Nat.mod_eq_of_lt h1]
  have hspec1 : spec_kernel mem' i = iterHash ROUNDS 1 := by
    simpa [hmod, mem'] using hs'
  -- conclude the sensitivity at lane `i`
  -- (iterHash 0) ≠ (iterHash 1)
  have hneq : iterHash ROUNDS 1 ≠ iterHash ROUNDS 0 := by
    simpa [eq_comm] using iterHash_ne
  -- rewrite and finish
  simpa [KernelSensitive, addr, mem', hspec0, hspec1] using hneq

lemma outputDiffers_uniform_zero (mem : Memory)
    (hunif : UniformZeroKernel mem) : OutputDiffers mem := by
  intro i
  rcases hunif with
    ⟨_hsafe, hrounds, hnodes, _hbatch, _hheight, _hlayout, _hdisjoint, hforest, hidx, hval⟩
  have hspec : spec_kernel mem i = iterHash ROUNDS 0 := by
    have hs :=
      spec_kernel_uniform_val mem i 0 hrounds hnodes hforest (hidx i) (by simpa using hval i)
    simpa [mod32] using hs
  have hinp : memAt mem (memAt mem PTR_INP_VAL + i) = 0 := hval i
  simpa [hspec, hinp] using iterHash_ne_zero

lemma writesOutput_of_correct_outputDiffers (p : Program)
    (hcorrect : CorrectOn spec_kernel p MemSafeKernel) :
    ∀ mem, MemSafeKernel mem → OutputDiffers mem → WritesOutput p mem := by
  intro mem hsafe hdiff
  intro a ha
  classical
  rcases Finset.mem_image.1 ha with ⟨i, _hi, rfl⟩
  have hcorr_i := congrArg (fun f => f i) (hcorrect mem hsafe)
  have hrun :
      memAt (runMem p mem) (memAt mem PTR_INP_VAL + i) = spec_kernel mem i := by
    simpa [run, outputOf] using hcorr_i
  have hwrite : (memAt mem PTR_INP_VAL + i) ∈ writeWords p mem := by
    by_contra hnot
    have hEq :
        memAt (runMem p mem) (memAt mem PTR_INP_VAL + i) =
          memAt mem (memAt mem PTR_INP_VAL + i) :=
      runMem_eq_of_not_written p mem (memAt mem PTR_INP_VAL + i) hnot
    have hspec_eq : spec_kernel mem i = memAt mem (memAt mem PTR_INP_VAL + i) := by
      calc
        spec_kernel mem i
            = memAt (runMem p mem) (memAt mem PTR_INP_VAL + i) := by
                symm
                exact hrun
        _ = memAt mem (memAt mem PTR_INP_VAL + i) := hEq
    exact (hdiff i) hspec_eq
  exact List.mem_toFinset.2 hwrite

theorem must_read_kernel_values_for_mem (p : Program) (hstraight : StraightLine p)
    (hcorrect : CorrectOn spec_kernel p MemSafeKernel)
    (hsafeExec : ∀ mem, MemSafeKernel mem → SafeExec p mem) :
    ∀ mem, MemSafeKernel mem → KernelLayout mem → KernelSensitive mem → OutputDiffers mem →
      ∀ i : Fin BATCH_SIZE, (memAt mem PTR_INP_VAL + i) ∈ readWords p mem := by
  intro mem hsafe hlayout hks hdiff i
  by_contra hnot
  set addr := memAt mem PTR_INP_VAL + i
  let mem' := memUpdate mem addr (memAt mem addr + 1)
  have hneq : addr ≠ PTR_INP_VAL :=
    ptr_inp_val_ne_input_addr (valuesLayout_of_kernelLayout mem hlayout) i
  have hptr : memAt mem PTR_INP_VAL = memAt mem' PTR_INP_VAL := by
    symm
    simpa [mem', addr] using memUpdate_ptr_eq mem addr (memAt mem addr + 1) hneq
  have hsize : mem.size = mem'.size := by
    simp [mem', memUpdate]
  have hsafe' : MemSafeKernel mem' := by
    simpa [mem', addr] using memSafeKernel_update_val mem i hlayout hsafe
  have hwrites : WritesOutput p mem :=
    writesOutput_of_correct_outputDiffers p hcorrect mem hsafe hdiff
  have hagree : AgreeOnList (readWords p mem) mem mem' := by
    refine ⟨hsize, ?_⟩
    intro a ha
    have hneq' : a ≠ addr := by
      intro hEq
      apply hnot
      simpa [addr, hEq] using ha
    simpa [mem', addr] using
      (memUpdate_eq_of_ne mem addr (memAt mem addr + 1) a hneq').symm
  have hrun : run p mem = run p mem' :=
    run_eq_of_agree p mem mem' hptr hagree hwrites
      (hsafeExec mem hsafe) (hsafeExec mem' hsafe')
  have hspec : spec_kernel mem' i ≠ spec_kernel mem i := by
    simpa [KernelSensitive, mem', addr] using hks i
  have hcorr1 := congrArg (fun f => f i) (hcorrect mem hsafe)
  have hcorr2 := congrArg (fun f => f i) (hcorrect mem' hsafe')
  have hrun_i := congrArg (fun f => f i) hrun
  have : spec_kernel mem' i = spec_kernel mem i := by
    calc
      spec_kernel mem' i = run p mem' i := by symm; exact hcorr2
      _ = run p mem i := by symm; exact hrun_i
      _ = spec_kernel mem i := hcorr1
  exact hspec this

theorem must_read_kernel_values_for_mem_machine (p : Program)
    (hstraight : StraightLine p)
    (hcorrect : CorrectOnMachine spec_kernel p MemSafeKernel)
    (hsafeExec : ∀ mem, MemSafeKernel mem → SafeExec p mem) :
    ∀ mem, MemSafeKernel mem → KernelLayout mem → KernelSensitive mem → OutputDiffers mem →
      ∀ i : Fin BATCH_SIZE, (memAt mem PTR_INP_VAL + i) ∈ readWordsMachine p mem := by
  intro mem hsafe hlayout hks hdiff i
  have htrace : MachineTraceAgrees p mem :=
    MachineTraceAgrees_of_StraightLine p hstraight mem
  have hcorrect' : CorrectOn spec_kernel p MemSafeKernel :=
    CorrectOnMachine_to_CorrectOn spec_kernel p MemSafeKernel hcorrect
      (fun m _hm => MachineTraceAgrees_of_StraightLine p hstraight m)
  have hmem : (memAt mem PTR_INP_VAL + i) ∈ readWords p mem :=
    must_read_kernel_values_for_mem p hstraight hcorrect' hsafeExec mem hsafe hlayout hks hdiff i
  have hreads : readOpsMachine p mem = readOps p mem := by
    have := congrArg (fun t => t.2) htrace
    simpa [readOpsMachine, readOps] using this
  simpa [readWordsMachine, readWords, hreads] using hmem

theorem must_read_addr (p : Program)
    (hcorrect : CorrectOn spec_kernel p MemSafeKernel)
    (hsafeExec : ∀ mem, MemSafeKernel mem → SafeExec p mem) :
    ∀ mem, MemSafeKernel mem → WritesOutput p mem → ∀ addr, AddrSafe mem addr →
      (∃ i : Fin BATCH_SIZE,
        spec_kernel (memUpdate mem addr (memAt mem addr + 1)) i ≠ spec_kernel mem i) →
      addr ∈ readWords p mem := by
  intro mem hsafe hwrites addr haddr hsens
  by_contra hnot
  let mem' := memUpdate mem addr (memAt mem addr + 1)
  have hneq : addr ≠ PTR_INP_VAL := by
    intro hEq
    have hle : HEADER_SIZE ≤ PTR_INP_VAL := by simpa [hEq] using haddr.1
    have hlt : PTR_INP_VAL < HEADER_SIZE := by decide
    exact (not_le_of_gt hlt) hle
  have hptr : memAt mem PTR_INP_VAL = memAt mem' PTR_INP_VAL := by
    symm
    simpa [mem'] using memUpdate_ptr_eq mem addr (memAt mem addr + 1) hneq
  have hsize : mem.size = mem'.size := by
    simp [mem', memUpdate]
  have hsafe' : MemSafeKernel mem' := by
    simpa [mem'] using memSafeKernel_update_addr mem addr hsafe haddr
  have hagree : AgreeOnList (readWords p mem) mem mem' := by
    refine ⟨hsize, ?_⟩
    intro a ha
    have hneq' : a ≠ addr := by
      intro hEq
      apply hnot
      simpa [hEq] using ha
    simpa [mem'] using
      (memUpdate_eq_of_ne mem addr (memAt mem addr + 1) a hneq').symm
  have hrun : run p mem = run p mem' :=
    run_eq_of_agree p mem mem' hptr hagree hwrites
      (hsafeExec mem hsafe) (hsafeExec mem' hsafe')
  rcases hsens with ⟨i, hsens_i⟩
  have hsens_i' :
      spec_kernel mem' i ≠ spec_kernel mem i := by
    simpa [mem'] using hsens_i
  have hcorr1 := congrArg (fun f => f i) (hcorrect mem hsafe)
  have hcorr2 := congrArg (fun f => f i) (hcorrect mem' hsafe')
  have hrun_i := congrArg (fun f => f i) hrun
  have : spec_kernel mem' i = spec_kernel mem i := by
    calc
      spec_kernel mem' i = run p mem' i := by symm; exact hcorr2
      _ = run p mem i := by symm; exact hrun_i
      _ = spec_kernel mem i := hcorr1
  exact hsens_i' this

theorem must_read_addr_machine (p : Program)
    (hstraight : StraightLine p)
    (hcorrect : CorrectOnMachine spec_kernel p MemSafeKernel)
    (hsafeExec : ∀ mem, MemSafeKernel mem → SafeExec p mem) :
    ∀ mem, MemSafeKernel mem → WritesOutput p mem → ∀ addr, AddrSafe mem addr →
      (∃ i : Fin BATCH_SIZE,
        spec_kernel (memUpdate mem addr (memAt mem addr + 1)) i ≠ spec_kernel mem i) →
      addr ∈ readWordsMachine p mem := by
  intro mem hsafe hwrites addr haddr hsens
  have htrace : MachineTraceAgrees p mem :=
    MachineTraceAgrees_of_StraightLine p hstraight mem
  have hcorrect' : CorrectOn spec_kernel p MemSafeKernel :=
    CorrectOnMachine_to_CorrectOn spec_kernel p MemSafeKernel hcorrect
      (fun m _hm => MachineTraceAgrees_of_StraightLine p hstraight m)
  have hmem : addr ∈ readWords p mem :=
    must_read_addr p hcorrect' hsafeExec mem hsafe hwrites addr haddr hsens
  have hreads : readOpsMachine p mem = readOps p mem := by
    have := congrArg (fun t => t.2) htrace
    simpa [readOpsMachine, readOps] using this
  simpa [readWordsMachine, readWords, hreads] using hmem

theorem must_read_addr_machine_fuel (p : Program) (fuel : Nat)
    (hfull : fuel = p.program.length)
    (hstraight : StraightLine p)
    (hcorrect : CorrectOnMachineFuel spec_kernel p MemSafeKernel fuel)
    (hsafeExec : ∀ mem, MemSafeKernel mem → SafeExec p mem) :
    ∀ mem, MemSafeKernel mem → WritesOutput p mem → ∀ addr, AddrSafe mem addr →
      (∃ i : Fin BATCH_SIZE,
        spec_kernel (memUpdate mem addr (memAt mem addr + 1)) i ≠ spec_kernel mem i) →
      addr ∈ readWordsMachineFuel p fuel mem := by
  intro mem hsafe hwrites addr haddr hsens
  subst hfull
  have hcorrectM : CorrectOnMachine spec_kernel p MemSafeKernel := by
    intro m hm
    have := hcorrect m hm
    simpa [CorrectOnMachine, CorrectOnMachineFuel, runMachine, runMachineFuel, runMemMachine,
      runMemMachineFuel, runMachineTrace, runMachineTraceFuel] using this
  have hmem : addr ∈ readWordsMachine p mem :=
    must_read_addr_machine p hstraight hcorrectM hsafeExec mem hsafe hwrites addr haddr hsens
  simpa [readWordsMachine, readWordsMachineFuel, readOpsMachine, readOpsMachineFuel,
    runMachineTrace, runMachineTraceFuel] using hmem

theorem must_read_kernel_values_for_mem_machine_fuel (p : Program) (fuel : Nat)
    (hfull : fuel = p.program.length)
    (hstraight : StraightLine p)
    (hcorrect : CorrectOnMachineFuel spec_kernel p MemSafeKernel fuel)
    (hsafeExec : ∀ mem, MemSafeKernel mem → SafeExec p mem) :
    ∀ mem, MemSafeKernel mem → KernelLayout mem → KernelSensitive mem → OutputDiffers mem →
      ∀ i : Fin BATCH_SIZE, (memAt mem PTR_INP_VAL + i) ∈ readWordsMachineFuel p fuel mem := by
  intro mem hsafe hlayout hks hdiff i
  subst hfull
  have hcorrectM : CorrectOnMachine spec_kernel p MemSafeKernel := by
    intro m hm
    have := hcorrect m hm
    simpa [CorrectOnMachine, CorrectOnMachineFuel, runMachine, runMachineFuel, runMemMachine,
      runMemMachineFuel, runMachineTrace, runMachineTraceFuel] using this
  have hmem : (memAt mem PTR_INP_VAL + i) ∈ readWordsMachine p mem :=
    must_read_kernel_values_for_mem_machine p hstraight hcorrectM hsafeExec mem hsafe hlayout hks hdiff i
  simpa [readWordsMachine, readWordsMachineFuel, readOpsMachine, readOpsMachineFuel,
    runMachineTrace, runMachineTraceFuel] using hmem
theorem must_read_kernel_values (p : Program) (hstraight : StraightLine p)
    (hcorrect : CorrectOn spec_kernel p MemSafeKernel)
    (hsafeExec : ∀ mem, MemSafeKernel mem → SafeExec p mem) :
    ∀ i : Fin BATCH_SIZE,
      (memAt memUniform0 PTR_INP_VAL + i) ∈ readWords p memUniform0 := by
  intro i
  have hunif : UniformZeroKernel memUniform0 := uniformZeroKernel_memUniform0
  have hks : KernelSensitive memUniform0 := kernelSensitive_uniform_zero memUniform0 hunif
  have hdiff : OutputDiffers memUniform0 := outputDiffers_uniform_zero memUniform0 hunif
  rcases hunif with ⟨hsafe, _hrounds, _hnodes, _hbatch, _hheight, hlayout, _hdisjoint, _hforest, _hidx, _hval⟩
  exact must_read_kernel_values_for_mem p hstraight hcorrect hsafeExec memUniform0 hsafe hlayout hks hdiff i

theorem outputAddrs_subset_readWords_kernel_for_mem (p : Program) (hstraight : StraightLine p)
    (hcorrect : CorrectOn spec_kernel p MemSafeKernel)
    (hsafeExec : ∀ mem, MemSafeKernel mem → SafeExec p mem) :
    ∀ mem, MemSafeKernel mem → KernelLayout mem → KernelSensitive mem → OutputDiffers mem →
      outputAddrs mem ⊆ (readWords p mem).toFinset := by
  intro mem hsafe hlayout hks hdiff
  intro a ha
  classical
  rcases Finset.mem_image.1 ha with ⟨i, _hi, rfl⟩
  have hmem :
      (memAt mem PTR_INP_VAL + i) ∈ readWords p mem :=
    must_read_kernel_values_for_mem p hstraight hcorrect hsafeExec mem hsafe hlayout hks hdiff i
  simpa using hmem

theorem outputAddrs_subset_readWords_kernel (p : Program) (hstraight : StraightLine p)
    (hcorrect : CorrectOn spec_kernel p MemSafeKernel)
    (hsafeExec : ∀ mem, MemSafeKernel mem → SafeExec p mem) :
    outputAddrs memUniform0 ⊆ (readWords p memUniform0).toFinset := by
  have hunif : UniformZeroKernel memUniform0 := uniformZeroKernel_memUniform0
  have hks : KernelSensitive memUniform0 := kernelSensitive_uniform_zero memUniform0 hunif
  have hdiff : OutputDiffers memUniform0 := outputDiffers_uniform_zero memUniform0 hunif
  rcases hunif with ⟨hsafe, _hrounds, _hnodes, _hbatch, _hheight, hlayout, _hdisjoint, _hforest, _hidx, _hval⟩
  exact outputAddrs_subset_readWords_kernel_for_mem p hstraight hcorrect hsafeExec
    memUniform0 hsafe hlayout hks hdiff

theorem min_required_words_kernel_for_mem (p : Program) (hstraight : StraightLine p)
    (hcorrect : CorrectOn spec_kernel p MemSafeKernel)
    (hsafeExec : ∀ mem, MemSafeKernel mem → SafeExec p mem) :
    ∀ mem, MemSafeKernel mem → KernelLayout mem → KernelSensitive mem → OutputDiffers mem →
      BATCH_SIZE ≤ readWordCount p mem := by
  intro mem hsafe hlayout hks hdiff
  have hsubset :
      outputAddrs mem ⊆ (readWords p mem).toFinset :=
    outputAddrs_subset_readWords_kernel_for_mem p hstraight hcorrect hsafeExec mem hsafe hlayout hks hdiff
  have hcard := outputAddrs_card mem
  have hcard_le : (outputAddrs mem).card ≤ (readWords p mem).toFinset.card := by
    simpa using (Finset.card_le_card hsubset)
  have hlen : (readWords p mem).toFinset.card ≤ (readWords p mem).length := by
    simpa using (List.toFinset_card_le (l := readWords p mem))
  have : BATCH_SIZE ≤ (readWords p mem).length := by
    have : (outputAddrs mem).card ≤ (readWords p mem).length :=
      le_trans hcard_le hlen
    simpa [hcard] using this
  simpa [readWordCount] using this

theorem min_required_words_kernel (p : Program) (hstraight : StraightLine p)
    (hcorrect : CorrectOn spec_kernel p MemSafeKernel)
    (hsafeExec : ∀ mem, MemSafeKernel mem → SafeExec p mem) :
    BATCH_SIZE ≤ readWordCount p memUniform0 := by
  have hunif : UniformZeroKernel memUniform0 := uniformZeroKernel_memUniform0
  have hks : KernelSensitive memUniform0 := kernelSensitive_uniform_zero memUniform0 hunif
  have hdiff : OutputDiffers memUniform0 := outputDiffers_uniform_zero memUniform0 hunif
  rcases hunif with ⟨hsafe, _hrounds, _hnodes, _hbatch, _hheight, hlayout, _hdisjoint, _hforest, _hidx, _hval⟩
  exact min_required_words_kernel_for_mem p hstraight hcorrect hsafeExec
    memUniform0 hsafe hlayout hks hdiff
theorem min_required_words_kernel_for_mem_machine (p : Program)
    (hstraight : StraightLine p)
    (hcorrect : CorrectOnMachine spec_kernel p MemSafeKernel)
    (hsafeExec : ∀ mem, MemSafeKernel mem → SafeExec p mem) :
    ∀ mem, MemSafeKernel mem → KernelLayout mem → KernelSensitive mem → OutputDiffers mem →
      BATCH_SIZE ≤ readWordCountMachine p mem := by
  intro mem hsafe hlayout hks hdiff
  have hsubset : outputAddrs mem ⊆ (readWordsMachine p mem).toFinset := by
    intro a ha
    classical
    rcases Finset.mem_image.1 ha with ⟨i, _hi, rfl⟩
    have hmem :
        (memAt mem PTR_INP_VAL + i) ∈ readWordsMachine p mem :=
      must_read_kernel_values_for_mem_machine p hstraight hcorrect hsafeExec mem hsafe hlayout hks hdiff i
    simpa using hmem
  have hcard := outputAddrs_card mem
  have hcard_le : (outputAddrs mem).card ≤ (readWordsMachine p mem).toFinset.card := by
    simpa using (Finset.card_le_card hsubset)
  have hlen : (readWordsMachine p mem).toFinset.card ≤ (readWordsMachine p mem).length := by
    simpa using (List.toFinset_card_le (l := readWordsMachine p mem))
  have : BATCH_SIZE ≤ (readWordsMachine p mem).length := by
    have : (outputAddrs mem).card ≤ (readWordsMachine p mem).length :=
      le_trans hcard_le hlen
    simpa [hcard] using this
  simpa [readWordCountMachine] using this

theorem min_required_words_adversaryK_machine (p : Program)
    (hstraight : StraightLine p)
    (hcorrect : CorrectOnMachine spec_kernel p MemSafeKernel)
    (hsafeExec : ∀ mem, MemSafeKernel mem → SafeExec p mem) :
    ∀ mem, MemSafeKernel mem → WritesOutput p mem → ∀ k, AdversaryK mem k →
      k * BATCH_SIZE * memAt mem 0 ≤ readWordCountMachine p mem := by
  intro mem hsafe hwrites k hk
  classical
  rcases hk with ⟨L, hL, hlen⟩
  rcases hL with ⟨hLnodup, hLsafe, hLsens⟩
  have hsubset : L.toFinset ⊆ (readWordsMachine p mem).toFinset := by
    intro a ha
    have haL : a ∈ L := by
      simpa [List.mem_toFinset] using ha
    have haddr : AddrSafe mem a := hLsafe a haL
    have hsens :
        (∃ i : Fin BATCH_SIZE,
          spec_kernel (memUpdate mem a (memAt mem a + 1)) i ≠ spec_kernel mem i) :=
      hLsens a haL
    have hread : a ∈ readWordsMachine p mem :=
      must_read_addr_machine p hstraight hcorrect hsafeExec mem hsafe hwrites a haddr hsens
    simpa [List.mem_toFinset] using hread
  have hcard_le : L.toFinset.card ≤ (readWordsMachine p mem).toFinset.card :=
    Finset.card_le_card hsubset
  have hlen_words : (readWordsMachine p mem).toFinset.card ≤ (readWordsMachine p mem).length := by
    simpa using (List.toFinset_card_le (l := readWordsMachine p mem))
  have hlen_L : L.length ≤ (readWordsMachine p mem).length := by
    have hcard_L : L.toFinset.card = L.length := List.toFinset_card_of_nodup hLnodup
    have : L.toFinset.card ≤ (readWordsMachine p mem).length :=
      le_trans hcard_le hlen_words
    simpa [hcard_L] using this
  have hgoal : k * BATCH_SIZE * memAt mem 0 ≤ (readWordsMachine p mem).length := by
    simpa [hlen] using hlen_L
  simpa [readWordCountMachine] using hgoal
theorem min_required_words_adversaryK_machine_fuel (p : Program) (fuel : Nat)
    (hfull : fuel = p.program.length)
    (hstraight : StraightLine p)
    (hcorrect : CorrectOnMachineFuel spec_kernel p MemSafeKernel fuel)
    (hsafeExec : ∀ mem, MemSafeKernel mem → SafeExec p mem) :
    ∀ mem, MemSafeKernel mem → WritesOutput p mem → ∀ k, AdversaryK mem k →
      k * BATCH_SIZE * memAt mem 0 ≤ readWordCountMachineFuel p fuel mem := by
  intro mem hsafe hwrites k hk
  subst hfull
  have hcorrectM : CorrectOnMachine spec_kernel p MemSafeKernel := by
    intro m hm
    have := hcorrect m hm
    simpa [CorrectOnMachine, CorrectOnMachineFuel, runMachine, runMachineFuel, runMemMachine,
      runMemMachineFuel, runMachineTrace, runMachineTraceFuel] using this
  have hcount : k * BATCH_SIZE * memAt mem 0 ≤ readWordCountMachine p mem :=
    min_required_words_adversaryK_machine p hstraight hcorrectM hsafeExec mem hsafe hwrites k hk
  simpa [readWordCountMachine, readWordCountMachineFuel, readWordsMachine, readWordsMachineFuel,
    readOpsMachine, readOpsMachineFuel, runMachineTrace, runMachineTraceFuel] using hcount

theorem min_required_words_kernel_for_mem_machine_fuel (p : Program) (fuel : Nat)
    (hfull : fuel = p.program.length)
    (hstraight : StraightLine p)
    (hcorrect : CorrectOnMachineFuel spec_kernel p MemSafeKernel fuel)
    (hsafeExec : ∀ mem, MemSafeKernel mem → SafeExec p mem) :
    ∀ mem, MemSafeKernel mem → KernelLayout mem → KernelSensitive mem → OutputDiffers mem →
      BATCH_SIZE ≤ readWordCountMachineFuel p fuel mem := by
  intro mem hsafe hlayout hks hdiff
  subst hfull
  have hcorrectM : CorrectOnMachine spec_kernel p MemSafeKernel := by
    intro m hm
    have := hcorrect m hm
    simpa [CorrectOnMachine, CorrectOnMachineFuel, runMachine, runMachineFuel, runMemMachine,
      runMemMachineFuel, runMachineTrace, runMachineTraceFuel] using this
  have hcount : BATCH_SIZE ≤ readWordCountMachine p mem :=
    min_required_words_kernel_for_mem_machine p hstraight hcorrectM hsafeExec mem hsafe hlayout hks hdiff
  simpa [readWordCountMachine, readWordCountMachineFuel, readWordsMachine, readWordsMachineFuel,
    readOpsMachine, readOpsMachineFuel, runMachineTrace, runMachineTraceFuel] using hcount


end ProofGlobalLowerBound
