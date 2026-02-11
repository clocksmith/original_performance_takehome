import proofs.global_lower_bound.LowerBound.Adversary

namespace ProofGlobalLowerBound
open ProofCommon
open ProofMachine
open ProofISA

/-!
Helper lemmas for the `memBig` structured-adversary witness (`RoundDistinctNodes memBig 1`).

This file is intentionally small and fast to compile: it provides basic facts about the
"bump one forest node" memory update, without attempting to prove end-to-end sensitivity.
-/

/-- `memBig`, but with the single forest word at `(round r, lane i)` incremented by 1. -/
def memBigForestBump (r : Fin ROUNDS) (i : Fin BATCH_SIZE) : Memory :=
  let addr := BIG_FOREST_BASE + idxAtR r i
  memUpdate memBig addr (memAt memBig addr + 1)

def treeBump (r : Fin ROUNDS) (i : Fin BATCH_SIZE) : Nat → Nat :=
  fun k => memAt (memBigForestBump r i) (BIG_FOREST_BASE + k)

lemma memAt_memUpdate (mem : Memory) (addr val a : Nat) :
    memAt (memUpdate mem addr val) a = (if a = addr then val else memAt mem a) := by
  simp [memUpdate, memAt]

lemma treeBump_eq (r : Fin ROUNDS) (i : Fin BATCH_SIZE) (k : Nat) (hk : k < N_NODES_BIG) :
    treeBump r i k = if k = idxAtR r i then 1 else 0 := by
  classical
  unfold treeBump memBigForestBump
  set bumpK : Nat := idxAtR r i
  set addr : Nat := BIG_FOREST_BASE + bumpK
  have h0 : memAt memBig (BIG_FOREST_BASE + k) = 0 := memBig_tree k hk
  by_cases h : k = bumpK
  · subst h
    have hk' : bumpK < N_NODES_BIG := idxAtR_lt r i
    have haddr0 : memAt memBig addr = 0 := by
      -- `addr = BIG_FOREST_BASE + bumpK` by definition.
      simpa [addr] using (memBig_tree bumpK hk')
    -- Update hits exactly `addr`, so `memAt` reads back the written value.
    calc
      memAt (memUpdate memBig addr (memAt memBig addr + 1)) addr
          = memAt memBig addr + 1 := by
              simp [memAt_memUpdate]
      _ = 1 := by simp [haddr0]
      _ = if bumpK = bumpK then 1 else 0 := by simp
  · have hne : BIG_FOREST_BASE + k ≠ addr := by
      intro hEq
      apply h
      exact Nat.add_left_cancel hEq
    have hsame :
        memAt (memUpdate memBig addr (memAt memBig addr + 1)) (BIG_FOREST_BASE + k) =
          memAt memBig (BIG_FOREST_BASE + k) := by
      -- use `memAt_memUpdate` + `hne` rather than unfolding `memBig`
      simp [memAt_memUpdate, hne]
    -- RHS is `0` since `k` is an in-range forest node on `memBig`.
    simp [hsame, h0, bumpK, addr, h]

lemma memBigForestBump_header_eq (r : Fin ROUNDS) (i : Fin BATCH_SIZE) {k : Nat}
    (hk : k < HEADER_SIZE) :
    memAt (memBigForestBump r i) k = memAt memBig k := by
  unfold memBigForestBump
  set addr : Nat := BIG_FOREST_BASE + idxAtR r i
  have haddr : HEADER_SIZE ≤ addr := by
    -- BIG_FOREST_BASE = HEADER_SIZE.
    simpa [addr, BIG_FOREST_BASE] using (Nat.le_add_right HEADER_SIZE (idxAtR r i))
  simpa [addr] using (memUpdate_header_eq memBig (addr := addr) (val := memAt memBig addr + 1) hk haddr)

lemma memBigForestBump_rounds (r : Fin ROUNDS) (i : Fin BATCH_SIZE) :
    memAt (memBigForestBump r i) 0 = ROUNDS := by
  simpa [memBig_rounds] using (memBigForestBump_header_eq (r := r) (i := i) (k := 0) (by decide))

lemma memBigForestBump_ptrForest (r : Fin ROUNDS) (i : Fin BATCH_SIZE) :
    memAt (memBigForestBump r i) PTR_FOREST = BIG_FOREST_BASE := by
  have h := memBigForestBump_header_eq (r := r) (i := i) (k := PTR_FOREST) (by decide)
  simpa [(memBig_ptrs).1] using h

lemma memBigForestBump_ptrIdx (r : Fin ROUNDS) (i : Fin BATCH_SIZE) :
    memAt (memBigForestBump r i) PTR_INP_IDX = BIG_IDX_BASE := by
  have h := memBigForestBump_header_eq (r := r) (i := i) (k := PTR_INP_IDX) (by decide)
  simpa [(memBig_ptrs).2.1] using h

lemma memBigForestBump_ptrVal (r : Fin ROUNDS) (i : Fin BATCH_SIZE) :
    memAt (memBigForestBump r i) PTR_INP_VAL = BIG_VAL_BASE := by
  have h := memBigForestBump_header_eq (r := r) (i := i) (k := PTR_INP_VAL) (by decide)
  simpa [(memBig_ptrs).2.2] using h

end ProofGlobalLowerBound
