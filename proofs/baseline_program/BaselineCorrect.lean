import proofs.baseline_program.BaselineStructure
import proofs.baseline_program.BlockSymbolic
import proofs.global_lower_bound.LowerBound

open ProofISA
open ProofMachine
open ProofGlobalLowerBound

/-! ## Baseline scalar kernel correctness scaffold

This file defines the *spec-level* block/round semantics that the baseline
program should implement. Proofs will relate `baselineProgram` execution to
these definitions.
-/

def blockInstrs (i : Fin BATCH_SIZE) : List Instruction :=
  baselineBlocks.get i

lemma blockInstrs_eq_template (i : Fin BATCH_SIZE) :
    blockInstrs i = blockTemplate (blockConstReg i) := by
  simp [blockInstrs, baselineBlocks, blockConstReg]

lemma blockInstrs_eq_template_add (i : Fin BATCH_SIZE) :
    blockInstrs i = blockTemplate (10 + i) := by
  simp [blockInstrs_eq_template, blockConstReg_eq]

def roundInstrs : List Instruction := baselineRound

def bodyInstrs : List Instruction := baselineBody

lemma baselineProgram_program :
    baselineProgram.program = baselinePrefix ++ baselineBody := by
  rfl

def blockSpec (mem : Memory) (i : Fin BATCH_SIZE) : Memory :=
  let nNodes := memAt mem 1
  let forestPtr := memAt mem PTR_FOREST
  let idxPtr := memAt mem PTR_INP_IDX
  let valPtr := memAt mem PTR_INP_VAL
  let tree := fun j => memAt mem (forestPtr + j)
  let idx0 := memAt mem (idxPtr + i)
  let val0 := memAt mem (valPtr + i)
  let (idx1, val1) := step tree nNodes idx0 val0
  let mem' := memUpdate mem (idxPtr + i) idx1
  memUpdate mem' (valPtr + i) val1

def roundSpec : Nat → Memory → Memory
  | 0, mem => mem
  | n+1, mem =>
      let mem' := (List.range BATCH_SIZE).foldl
        (fun m k =>
          match (Fin.ofNat? k) with
          | some i => blockSpec m i
          | none => m) mem
      roundSpec n mem'

def kernelSpec (mem : Memory) : Memory :=
  roundSpec (memAt mem 0) mem
