import proofs.baseline_program.BaselineHelpers
import proofs.baseline_program.BaselinePrefix
import proofs.baseline_program.BaselineBlocks

open ProofISA
open ProofMachine
open ProofGlobalLowerBound

def baselineRound : List Instruction := List.join baselineBlocks
def baselineBody : List Instruction := List.join (List.replicate ROUNDS baselineRound)
def baselineProgram : Program :=
  { program := baselinePrefix ++ baselineBody }

lemma baselineBlocks_length : baselineBlocks.length = BATCH_SIZE := by
  native_decide

lemma baselineBlock_length (i : Fin BATCH_SIZE) :
    (baselineBlocks.get i).length = 36 := by
  native_decide

lemma baselineRound_length : baselineRound.length = BATCH_SIZE * 36 := by
  native_decide

lemma baselineBody_length : baselineBody.length = ROUNDS * (BATCH_SIZE * 36) := by
  native_decide

lemma baselineProgram_length :
    baselineProgram.program.length = baselinePrefix.length + ROUNDS * (BATCH_SIZE * 36) := by
  native_decide

lemma baselineProgram_wellFormed : List.All instrWellFormed baselineProgram.program := by
  native_decide

lemma baselineProgram_pcBounded : PcBoundedProgram baselineProgram := by
  native_decide

lemma baselineProgram_class : ProgramClass baselineProgram := by
  exact baselineProgram_pcBounded
