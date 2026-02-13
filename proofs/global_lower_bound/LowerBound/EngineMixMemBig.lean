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

lemma minLoadOps_readWordCountMachine_le_loadOpCountMachine
    (p : Program) (mem : Memory) :
    minLoadOps (readWordCountMachine p mem) ≤ loadOpCountMachine p mem := by
  have h :=
    loadOps_lower_bound_machineFuel (p := p) (fuel := p.program.length) (mem := mem)
  simpa [readWordCountMachine, readWordCountMachineFuel, readWordsMachine, readWordsMachineFuel,
    readOpsMachine, readOpsMachineFuel, runMachineTrace, runMachineTraceFuel,
    loadOpCountMachine, loadOpCountMachineFuel] using h

theorem global_engine_cycle_lower_bound_kernel_machine_of_subset_card
    (p : Program) (hstraight : StraightLine p)
    (hcorrect : CorrectOnMachine spec_kernel p MemSafeKernel)
    (hsafeExec : ∀ mem, MemSafeKernel mem → SafeExec p mem)
    (mem : Memory) (hmem : MemSafeKernel mem)
    (s : Finset Nat) (hsubset : s ⊆ (readWordsMachine p mem).toFinset) :
    engineLowerBound (requiredLoadOnly (minLoadOps s.card)) ≤ cycleCountMachine p mem := by
  have hwords : s.card ≤ readWordCountMachine p mem :=
    finset_card_le_readWordCountMachine_of_subset p mem s hsubset
  have hmin :
      minLoadOps s.card ≤
        minLoadOps (readWordCountMachine p mem) :=
    minLoadOps_mono hwords
  have hops :
      minLoadOps (readWordCountMachine p mem) ≤
        loadOpCountMachine p mem := by
    simpa using minLoadOps_readWordCountMachine_le_loadOpCountMachine p mem
  have hreq : minLoadOps s.card ≤ loadOpCountMachine p mem := le_trans hmin hops
  exact global_engine_load_lower_bound_kernel_machine_of_requiredLoadOps
    (spec := spec_kernel) (memOk := MemSafeKernel)
    (p := p) hcorrect hstraight hsafeExec
    mem hmem (minLoadOps s.card) hreq

lemma engineLowerBound_requiredLoadOnly_kernelPlus_eq_272 :
    engineLowerBound (requiredLoadOnly (minLoadOps (BATCH_SIZE * (ROUNDS + 1)))) = 272 := by
  native_decide

theorem global_engine_cycle_lower_bound_kernel_machine_of_subset_card_272
    (p : Program) (hstraight : StraightLine p)
    (hcorrect : CorrectOnMachine spec_kernel p MemSafeKernel)
    (hsafeExec : ∀ mem, MemSafeKernel mem → SafeExec p mem)
    (mem : Memory) (hmem : MemSafeKernel mem)
    (s : Finset Nat) (hsubset : s ⊆ (readWordsMachine p mem).toFinset)
    (hcard : s.card = BATCH_SIZE * (ROUNDS + 1)) :
    272 ≤ cycleCountMachine p mem := by
  have hengine :
      engineLowerBound (requiredLoadOnly (minLoadOps s.card)) ≤ cycleCountMachine p mem :=
    global_engine_cycle_lower_bound_kernel_machine_of_subset_card
      p hstraight hcorrect hsafeExec mem hmem s hsubset
  have hengine' :
      engineLowerBound (requiredLoadOnly (minLoadOps (BATCH_SIZE * (ROUNDS + 1)))) ≤
        cycleCountMachine p mem := by
    simpa [hcard] using hengine
  simpa [engineLowerBound_requiredLoadOnly_kernelPlus_eq_272] using hengine'

theorem global_engine_cycle_lower_bound_kernel_machine_adversaryList_values_disjoint_272
    (p : Program) (hstraight : StraightLine p)
    (hcorrect : CorrectOnMachine spec_kernel p MemSafeKernel)
    (hsafeExec : ∀ mem, MemSafeKernel mem → SafeExec p mem) :
    ∀ mem, MemSafeKernel mem → KernelLayout mem → KernelSensitive mem → OutputDiffers mem →
      ∀ L, AdversaryList mem L → L.length = BATCH_SIZE * ROUNDS →
        Disjoint L.toFinset (outputAddrs mem) →
        272 ≤ cycleCountMachine p mem := by
  intro mem hsafe hlayout hks hdiff L hL hlen hdisj
  rcases hL with ⟨hLnodup, hLsafe, hLsens⟩
  have hcorrect' : CorrectOn spec_kernel p MemSafeKernel :=
    CorrectOnMachine_to_CorrectOn spec_kernel p MemSafeKernel hcorrect
      (fun m _hm => MachineTraceAgrees_of_StraightLine p hstraight m)
  have hwrites : WritesOutput p mem :=
    writesOutput_of_correct_outputDiffers p hcorrect' mem hsafe hdiff
  have hsubsetRound : L.toFinset ⊆ (readWordsMachine p mem).toFinset := by
    intro a ha
    have haL : a ∈ L := by
      simpa [List.mem_toFinset] using ha
    have haddr : AddrSafe mem a := hLsafe a haL
    have hsens :
        ∃ i : Fin BATCH_SIZE,
          spec_kernel (memUpdate mem a (memAt mem a + 1)) i ≠ spec_kernel mem i :=
      hLsens a haL
    have hread : a ∈ readWordsMachine p mem :=
      must_read_addr_machine p hstraight hcorrect hsafeExec mem hsafe hwrites a haddr hsens
    simpa [List.mem_toFinset] using hread
  have hsubsetVals : outputAddrs mem ⊆ (readWordsMachine p mem).toFinset := by
    intro a ha
    rcases Finset.mem_image.1 ha with ⟨i, _hi, rfl⟩
    have hread :
        (memAt mem PTR_INP_VAL + i) ∈ readWordsMachine p mem :=
      must_read_kernel_values_for_mem_machine p hstraight hcorrect hsafeExec
        mem hsafe hlayout hks hdiff i
    simpa [List.mem_toFinset] using hread
  have hsubsetUnion :
      (L.toFinset ∪ outputAddrs mem) ⊆ (readWordsMachine p mem).toFinset := by
    intro a ha
    rcases Finset.mem_union.1 ha with hround | hval
    · exact hsubsetRound hround
    · exact hsubsetVals hval
  have hcardUnion : (L.toFinset ∪ outputAddrs mem).card = BATCH_SIZE * (ROUNDS + 1) := by
    have hcardU :
        (L.toFinset ∪ outputAddrs mem).card = L.toFinset.card + (outputAddrs mem).card := by
      simpa using (Finset.card_union_of_disjoint hdisj)
    have hcardL : L.toFinset.card = L.length := List.toFinset_card_of_nodup hLnodup
    have hcardVals : (outputAddrs mem).card = BATCH_SIZE := outputAddrs_card mem
    calc
      (L.toFinset ∪ outputAddrs mem).card
          = L.toFinset.card + (outputAddrs mem).card := hcardU
      _ = L.length + BATCH_SIZE := by simp [hcardL, hcardVals]
      _ = BATCH_SIZE * ROUNDS + BATCH_SIZE := by simp [hlen]
      _ = BATCH_SIZE * (ROUNDS + 1) := by
            simp [Nat.mul_add, Nat.mul_one, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
  exact global_engine_cycle_lower_bound_kernel_machine_of_subset_card_272
    p hstraight hcorrect hsafeExec mem hsafe (L.toFinset ∪ outputAddrs mem) hsubsetUnion hcardUnion

theorem global_engine_cycle_lower_bound_kernel_machine_roundDistinct_values_disjoint_272
    (p : Program) (hstraight : StraightLine p)
    (hcorrect : CorrectOnMachine spec_kernel p MemSafeKernel)
    (hsafeExec : ∀ mem, MemSafeKernel mem → SafeExec p mem) :
    ∀ mem, MemSafeKernel mem → KernelLayout mem → KernelSensitive mem → OutputDiffers mem →
      memAt mem 0 = ROUNDS → RoundDistinctNodes mem 1 →
      (∀ L, AdversaryList mem L → L.length = BATCH_SIZE * ROUNDS →
        Disjoint L.toFinset (outputAddrs mem)) →
      272 ≤ cycleCountMachine p mem := by
  intro mem hsafe hlayout hks hdiff hrounds hrd hdisjoint
  have hk : AdversaryK mem 1 := adversaryK_of_roundDistinct mem 1 hrd
  rcases hk with ⟨L, hL, hlenK⟩
  have hlen : L.length = BATCH_SIZE * ROUNDS := by
    simpa [hrounds, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hlenK
  have hdisj : Disjoint L.toFinset (outputAddrs mem) := hdisjoint L hL hlen
  exact global_engine_cycle_lower_bound_kernel_machine_adversaryList_values_disjoint_272
    p hstraight hcorrect hsafeExec mem hsafe hlayout hks hdiff L hL hlen hdisj

theorem global_engine_cycle_lower_bound_kernel_machine_memBig_272
    (p : Program) (hstraight : StraightLine p)
    (hcorrect : CorrectOnMachine spec_kernel p MemSafeKernel)
    (hsafeExec : ∀ mem, MemSafeKernel mem → SafeExec p mem) :
    272 ≤ cycleCountMachine p memBig := by
  have hsubset : memBigAllAddrs ⊆ (readWordsMachine p memBig).toFinset :=
    memBigAllAddrs_subset_readWordsMachine_of_correctMachine p hstraight hcorrect hsafeExec
  exact global_engine_cycle_lower_bound_kernel_machine_of_subset_card_272
    p hstraight hcorrect hsafeExec memBig memBig_safe
    memBigAllAddrs hsubset memBigAllAddrs_card

theorem global_engine_cycle_lower_bound_kernel_machine_exists_memBig_272
    (p : Program) (hstraight : StraightLine p)
    (hcorrect : CorrectOnMachine spec_kernel p MemSafeKernel)
    (hsafeExec : ∀ mem, MemSafeKernel mem → SafeExec p mem) :
    ∃ mem, 272 ≤ cycleCountMachine p mem := by
  exact ⟨memBig, global_engine_cycle_lower_bound_kernel_machine_memBig_272 p hstraight hcorrect hsafeExec⟩

end ProofGlobalLowerBound
