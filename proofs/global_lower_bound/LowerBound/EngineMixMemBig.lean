import proofs.global_lower_bound.LowerBound.EngineMixKernel
import proofs.global_lower_bound.LowerBound.LowerBounds

namespace ProofGlobalLowerBound
open ProofCommon
open ProofMachine
open ProofISA

/-!
`memBig` instantiation for the engine-mix kernel interface.

This module reconstructs the concrete `272` cycle lower bound through the new
`EngineMixKernel` composition path (required load ops -> engine LB -> cycles).
-/

lemma minLoadOps_readWordCountMachine_memBig_le_loadOpCountMachine
    (p : Program) :
    minLoadOps (readWordCountMachine p memBig) ≤ loadOpCountMachine p memBig := by
  have h :=
    loadOps_lower_bound_machineFuel (p := p) (fuel := p.program.length) (mem := memBig)
  simpa [readWordCountMachine, readWordCountMachineFuel, readWordsMachine, readWordsMachineFuel,
    readOpsMachine, readOpsMachineFuel, runMachineTrace, runMachineTraceFuel,
    loadOpCountMachine, loadOpCountMachineFuel] using h

lemma minLoadOps_kernelPlus_le_loadOpCountMachine_memBig_of_correctMachine
    (p : Program) (hstraight : StraightLine p)
    (hcorrect : CorrectOnMachine spec_kernel p MemSafeKernel)
    (hsafeExec : ∀ mem, MemSafeKernel mem → SafeExec p mem) :
    minLoadOps (BATCH_SIZE * (ROUNDS + 1)) ≤ loadOpCountMachine p memBig := by
  have hsubset : memBigAllAddrs ⊆ (readWordsMachine p memBig).toFinset :=
    memBigAllAddrs_subset_readWordsMachine_of_correctMachine p hstraight hcorrect hsafeExec
  have hwords : BATCH_SIZE * (ROUNDS + 1) ≤ readWordCountMachine p memBig :=
    min_required_words_kernel_machine_memBig_all p hsubset
  have hmin :
      minLoadOps (BATCH_SIZE * (ROUNDS + 1)) ≤
        minLoadOps (readWordCountMachine p memBig) :=
    minLoadOps_mono hwords
  have hops :
      minLoadOps (readWordCountMachine p memBig) ≤
        loadOpCountMachine p memBig :=
    minLoadOps_readWordCountMachine_memBig_le_loadOpCountMachine p
  exact le_trans hmin hops

lemma engineLowerBound_requiredLoadOnly_kernelPlus_eq_272 :
    engineLowerBound (requiredLoadOnly (minLoadOps (BATCH_SIZE * (ROUNDS + 1)))) = 272 := by
  native_decide

theorem global_engine_cycle_lower_bound_kernel_machine_memBig_272
    (p : Program) (hstraight : StraightLine p)
    (hcorrect : CorrectOnMachine spec_kernel p MemSafeKernel)
    (hsafeExec : ∀ mem, MemSafeKernel mem → SafeExec p mem) :
    272 ≤ cycleCountMachine p memBig := by
  have hreq :
      minLoadOps (BATCH_SIZE * (ROUNDS + 1)) ≤ loadOpCountMachine p memBig :=
    minLoadOps_kernelPlus_le_loadOpCountMachine_memBig_of_correctMachine
      p hstraight hcorrect hsafeExec
  have hengine :
      engineLowerBound (requiredLoadOnly (minLoadOps (BATCH_SIZE * (ROUNDS + 1)))) ≤
        cycleCountMachine p memBig :=
    global_engine_load_lower_bound_kernel_machine_of_requiredLoadOps
      (spec := spec_kernel) (memOk := MemSafeKernel)
      (p := p) hcorrect hstraight hsafeExec
      memBig memBig_safe (minLoadOps (BATCH_SIZE * (ROUNDS + 1))) hreq
  simpa [engineLowerBound_requiredLoadOnly_kernelPlus_eq_272] using hengine

end ProofGlobalLowerBound
