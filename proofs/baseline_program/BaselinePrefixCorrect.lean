import Mathlib
import proofs.baseline_program.BaselinePrefixSymbolic
import proofs.baseline_program.BaselineBlocks

open ProofISA
open ProofMachine
open ProofGlobalLowerBound

/-! ## Baseline prefix invariants

These lemmas describe the scratch contents after executing `baselinePrefix`
symbolically (via `prefixScratch`). They will be used as assumptions for the
block correctness proof.
-/

section
  variable (mem : Memory)

  lemma prefixScratch_ptr_forest : prefixScratch mem 7 = memAt mem PTR_FOREST := by
    simp [PTR_FOREST]

  lemma prefixScratch_ptr_idx : prefixScratch mem 8 = memAt mem PTR_INP_IDX := by
    simp [PTR_INP_IDX]

  lemma prefixScratch_ptr_val : prefixScratch mem 9 = memAt mem PTR_INP_VAL := by
    simp [PTR_INP_VAL]

  lemma prefixScratch_nNodes : prefixScratch mem 4 = memAt mem 1 := by
    simp

  lemma prefixScratch_const0 : prefixScratch mem 10 = 0 := by
    simp

  lemma prefixScratch_const1 : prefixScratch mem 11 = 1 := by
    simp

  lemma prefixScratch_const2 : prefixScratch mem 12 = 2 := by
    simp

  lemma prefixScratch_hash_const_0 : prefixScratch mem 17 = 0x7ED55D16 := by
    simp

  lemma prefixScratch_hash_const_1 : prefixScratch mem 19 = 0xC761C23C := by
    simp

  lemma prefixScratch_hash_const_2 : prefixScratch mem 21 = 0x165667B1 := by
    simp

  lemma prefixScratch_hash_const_3 : prefixScratch mem 23 = 0xD3A2646C := by
    simp

  lemma prefixScratch_hash_const_4 : prefixScratch mem 25 = 0xFD7046C5 := by
    simp

  lemma prefixScratch_hash_const_5 : prefixScratch mem 27 = 0xB55A4F09 := by
    simp

  lemma prefixScratch_hash_shift_0 : prefixScratch mem 18 = 12 := by
    simp

  lemma prefixScratch_hash_shift_1 : prefixScratch mem 20 = 19 := by
    simp

  lemma prefixScratch_hash_shift_2 : prefixScratch mem 22 = 5 := by
    simp

  lemma prefixScratch_hash_shift_3 : prefixScratch mem 24 = 9 := by
    simp

  lemma prefixScratch_hash_shift_4 : prefixScratch mem 26 = 3 := by
    simp

  lemma prefixScratch_hash_shift_5 : prefixScratch mem 28 = 16 := by
    simp

  lemma prefixScratch_blockConstReg (i : Fin BATCH_SIZE) :
      prefixScratch mem (blockConstReg i) = i := by
    -- Case split over all lanes; simp discharges each case using the
    -- auto-generated prefixScratch_const_* lemmas.
    fin_cases i <;> simp [blockConstReg, blockConstRegs]
end
