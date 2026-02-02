import Mathlib
import proofs.baseline_program.BlockCorrect
import proofs.baseline_program.BlockSpecCorrect
import proofs.baseline_program.BaselinePrefixCorrect
import proofs.baseline_program.BaselineCorrect

open ProofISA
open ProofMachine
open ProofGlobalLowerBound

lemma mod32_eq_of_lt {x : Nat} (h : x < MOD32) : mod32 x = x := by
  simp [mod32, Nat.mod_eq_of_lt h]

lemma aluEval_add_eq_of_lt {a b : Nat} (h : a + b < MOD32) :
    aluEval AluOp.add a b = a + b := by
  simp [aluEval, mod32_eq_of_lt h]

lemma aluEval_mul_eq_of_lt {a b : Nat} (h : a * b < MOD32) :
    aluEval AluOp.mul a b = a * b := by
  simp [aluEval, mod32_eq_of_lt h]

lemma blockSym_mem_eq_blockSpec_prefix
    (mem : Memory) (i : Fin BATCH_SIZE)
    (hsize : mem.size < MOD32)
    (hidxMem : memAt mem PTR_INP_IDX + BATCH_SIZE ≤ mem.size)
    (hvalMem : memAt mem PTR_INP_VAL + BATCH_SIZE ≤ mem.size)
    (hforestMem : memAt mem PTR_FOREST + memAt mem 1 ≤ mem.size)
    (hidxBound : memAt mem (memAt mem PTR_INP_IDX + i) < memAt mem 1) :
    (blockSym (prefixScratch mem) mem (blockConstReg i)).2 = blockSpec mem i := by
  -- establish pointer and constant facts from the prefix
  have hforest : prefixScratch mem 7 = memAt mem PTR_FOREST := by
    simpa using (prefixScratch_ptr_forest (mem:=mem))
  have hidxPtr : prefixScratch mem 8 = memAt mem PTR_INP_IDX := by
    simpa using (prefixScratch_ptr_idx (mem:=mem))
  have hvalPtr : prefixScratch mem 9 = memAt mem PTR_INP_VAL := by
    simpa using (prefixScratch_ptr_val (mem:=mem))
  have hnNodes : prefixScratch mem 4 = memAt mem 1 := by
    simpa using (prefixScratch_nNodes (mem:=mem))
  have hzero : prefixScratch mem 10 = 0 := by
    simpa using (prefixScratch_const0 (mem:=mem))
  have hone : prefixScratch mem 11 = 1 := by
    simpa using (prefixScratch_const1 (mem:=mem))
  have htwo : prefixScratch mem 12 = 2 := by
    simpa using (prefixScratch_const2 (mem:=mem))
  have hci : prefixScratch mem (blockConstReg i) = i := by
    simpa using (prefixScratch_blockConstReg (mem:=mem) i)

  -- address calculations stay within 32-bit range
  have haddr_idx : memAt mem PTR_INP_IDX + i < MOD32 := by
    have hi : i < BATCH_SIZE := by exact i.isLt
    have hle : memAt mem PTR_INP_IDX + i ≤ memAt mem PTR_INP_IDX + BATCH_SIZE := by
      exact Nat.add_le_add_left (Nat.le_of_lt hi) _
    exact lt_of_le_of_lt (Nat.le_trans hle hidxMem) hsize

  have haddr_val : memAt mem PTR_INP_VAL + i < MOD32 := by
    have hi : i < BATCH_SIZE := by exact i.isLt
    have hle : memAt mem PTR_INP_VAL + i ≤ memAt mem PTR_INP_VAL + BATCH_SIZE := by
      exact Nat.add_le_add_left (Nat.le_of_lt hi) _
    exact lt_of_le_of_lt (Nat.le_trans hle hvalMem) hsize

  -- shorthand for the initial scratch state
  set s := prefixScratch mem
  -- reduce blockSym memory update and rewrite via the spec
  -- The proof relies on rewriting the scratch values using the prefix lemmas.
  -- We also use hash6_eq_myhash to align the hash computation.
  simp [blockSym, blockSpec, step, hash6_eq_myhash, s,
        hforest, hidxPtr, hvalPtr, hnNodes, hzero, hone, htwo, hci,
        aluEval_add_eq_of_lt haddr_idx, aluEval_add_eq_of_lt haddr_val,
        write] at *
