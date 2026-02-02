import Mathlib
import proofs.baseline_program.BlockFullCorrect
import proofs.baseline_program.BaselinePrefixCorrect

open ProofISA
open ProofMachine
open ProofGlobalLowerBound

lemma exec_blockTemplate_eq_blockSpec
    (mem : Memory) (i : Fin BATCH_SIZE)
    (hsize : mem.size < MOD32)
    (hidxMem : memAt mem PTR_INP_IDX + BATCH_SIZE ≤ mem.size)
    (hvalMem : memAt mem PTR_INP_VAL + BATCH_SIZE ≤ mem.size)
    (hforestMem : memAt mem PTR_FOREST + memAt mem 1 ≤ mem.size)
    (hidxBound : memAt mem (memAt mem PTR_INP_IDX + i) < memAt mem 1) :
    execInstrs (blockTemplate (blockConstReg i)) mem (coreOf (prefixScratch mem)) =
      ({ (coreOf (prefixScratch mem)) with scratch :=
          (blockSym (prefixScratch mem) mem (blockConstReg i)).1 },
        blockSpec mem i) := by
  -- bounds for exec bridge
  have hc : blockConstReg i < SCRATCH_SIZE := by
    -- all lane-const regs are in [10,275]
    native_decide
  have hmod : (prefixScratch mem) 12 ≠ 0 := by
    simp [prefixScratch_const2]
  -- index address bound
  have hidx : aluEval AluOp.add ((prefixScratch mem) 8) ((prefixScratch mem) (blockConstReg i)) < mem.size := by
    have haddr_idx : memAt mem PTR_INP_IDX + i < MOD32 := by
      have hi : i < BATCH_SIZE := by exact i.isLt
      have hle : memAt mem PTR_INP_IDX + i ≤ memAt mem PTR_INP_IDX + BATCH_SIZE := by
        exact Nat.add_le_add_left (Nat.le_of_lt hi) _
      exact lt_of_le_of_lt (Nat.le_trans hle hidxMem) hsize
    have hadd :
        aluEval AluOp.add ((prefixScratch mem) 8) ((prefixScratch mem) (blockConstReg i)) =
          memAt mem PTR_INP_IDX + i := by
      simp [prefixScratch_ptr_idx, prefixScratch_blockConstReg, aluEval_add_eq_of_lt haddr_idx]
    -- show idxPtr + i < mem.size
    have hi : i < BATCH_SIZE := by exact i.isLt
    have hle : memAt mem PTR_INP_IDX + i ≤ memAt mem PTR_INP_IDX + BATCH_SIZE := by
      exact Nat.add_le_add_left (Nat.le_of_lt hi) _
    have hlt : memAt mem PTR_INP_IDX + i < mem.size := by
      exact lt_of_le_of_lt (Nat.le_trans hle hidxMem) (lt_of_le_of_lt (Nat.le_refl _) (lt_of_le_of_lt (Nat.le_refl _) hsize))
    simpa [hadd] using hlt
  -- val address bound
  have hval : aluEval AluOp.add ((prefixScratch mem) 9) ((prefixScratch mem) (blockConstReg i)) < mem.size := by
    have haddr_val : memAt mem PTR_INP_VAL + i < MOD32 := by
      have hi : i < BATCH_SIZE := by exact i.isLt
      have hle : memAt mem PTR_INP_VAL + i ≤ memAt mem PTR_INP_VAL + BATCH_SIZE := by
        exact Nat.add_le_add_left (Nat.le_of_lt hi) _
      exact lt_of_le_of_lt (Nat.le_trans hle hvalMem) hsize
    have hadd :
        aluEval AluOp.add ((prefixScratch mem) 9) ((prefixScratch mem) (blockConstReg i)) =
          memAt mem PTR_INP_VAL + i := by
      simp [prefixScratch_ptr_val, prefixScratch_blockConstReg, aluEval_add_eq_of_lt haddr_val]
    have hi : i < BATCH_SIZE := by exact i.isLt
    have hle : memAt mem PTR_INP_VAL + i ≤ memAt mem PTR_INP_VAL + BATCH_SIZE := by
      exact Nat.add_le_add_left (Nat.le_of_lt hi) _
    have hlt : memAt mem PTR_INP_VAL + i < mem.size := by
      exact lt_of_le_of_lt (Nat.le_trans hle hvalMem) (lt_of_le_of_lt (Nat.le_refl _) (lt_of_le_of_lt (Nat.le_refl _) hsize))
    simpa [hadd] using hlt
  -- node address bound
  have hnode : aluEval AluOp.add ((prefixScratch mem) 7)
      (memAt mem (aluEval AluOp.add ((prefixScratch mem) 8) ((prefixScratch mem) (blockConstReg i)))) < mem.size := by
    have haddr_idx : memAt mem PTR_INP_IDX + i < MOD32 := by
      have hi : i < BATCH_SIZE := by exact i.isLt
      have hle : memAt mem PTR_INP_IDX + i ≤ memAt mem PTR_INP_IDX + BATCH_SIZE := by
        exact Nat.add_le_add_left (Nat.le_of_lt hi) _
      exact lt_of_le_of_lt (Nat.le_trans hle hidxMem) hsize
    have hadd :
        aluEval AluOp.add ((prefixScratch mem) 8) ((prefixScratch mem) (blockConstReg i)) =
          memAt mem PTR_INP_IDX + i := by
      simp [prefixScratch_ptr_idx, prefixScratch_blockConstReg, aluEval_add_eq_of_lt haddr_idx]
    have hidx0 : memAt mem (memAt mem PTR_INP_IDX + i) < memAt mem 1 := hidxBound
    have hforest : memAt mem PTR_FOREST + memAt mem (memAt mem PTR_INP_IDX + i) < mem.size := by
      have hle : memAt mem PTR_FOREST + memAt mem (memAt mem PTR_INP_IDX + i) ≤
          memAt mem PTR_FOREST + memAt mem 1 := by
        exact Nat.add_le_add_left (Nat.le_of_lt hidx0) _
      exact lt_of_le_of_lt (Nat.le_trans hle hforestMem) (lt_of_le_of_lt (Nat.le_refl _) (lt_of_le_of_lt (Nat.le_refl _) hsize))
    have haddr_forest : memAt mem PTR_FOREST + memAt mem (memAt mem PTR_INP_IDX + i) < MOD32 := by
      exact lt_of_le_of_lt (Nat.le_of_lt hforest) hsize
    have hadd2 :
        aluEval AluOp.add ((prefixScratch mem) 7)
          (memAt mem (aluEval AluOp.add ((prefixScratch mem) 8) ((prefixScratch mem) (blockConstReg i)))) =
            memAt mem PTR_FOREST + memAt mem (memAt mem PTR_INP_IDX + i) := by
      simp [prefixScratch_ptr_forest, hadd, aluEval_add_eq_of_lt haddr_forest]
    simpa [hadd2] using hforest

  have hstep := execInstrs_blockTemplate_eq_blockSym mem (prefixScratch mem) (blockConstReg i)
    hc hidx hval hnode hmod
  have hmem := blockSym_mem_eq_blockSpec_prefix mem i hsize hidxMem hvalMem hforestMem hidxBound
  simpa [hmem] using hstep

