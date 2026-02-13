import proofs.global_lower_bound.LowerBound.MachineTraceEq
import proofs.global_lower_bound.LowerBound.Adversary
import proofs.global_lower_bound.LowerBound.MemBigRoundDistinct
import proofs.global_lower_bound.LowerBound.CycleLB

namespace ProofGlobalLowerBound
open ProofCommon
open ProofMachine
open ProofISA

/-- Lower bound on cycles implied by the load engine capacity. -/
def loadLowerCycles (words : Nat) : Nat := ceilDiv (minLoadOps words) LOAD_CAP

lemma loadLowerCycles_mono {a b : Nat} (h : a ≤ b) :
    loadLowerCycles a ≤ loadLowerCycles b := by
  exact ceilDiv_mono (minLoadOps_mono h)

/-- Global lower bound (currently load-only). -/
def globalLowerBound : Nat := loadLowerCycles MIN_REQUIRED_WORDS

def globalLowerBoundKernel : Nat := loadLowerCycles MIN_REQUIRED_WORDS_KERNEL

lemma globalLowerBound_eq_16 : globalLowerBound = 16 := by
  native_decide

lemma globalLowerBoundKernel_eq_16 : globalLowerBoundKernel = 16 := by
  native_decide

def globalLowerBoundKernelK (k : Nat) : Nat :=
  loadLowerCycles (k * BATCH_SIZE * ROUNDS)

lemma globalLowerBoundKernelK_eq_256 : globalLowerBoundKernelK 1 = 256 := by
  native_decide

lemma globalLowerBoundKernelK_eq_512 : globalLowerBoundKernelK 2 = 512 := by
  native_decide

def globalLowerBoundKernelPlus : Nat :=
  loadLowerCycles (BATCH_SIZE * (ROUNDS + 1))

lemma globalLowerBoundKernelPlus_eq_272 : globalLowerBoundKernelPlus = 272 := by
  native_decide

def computeLowerBoundKernel : Nat := 1

def globalLowerBoundKernelFinal : Nat :=
  max globalLowerBoundKernel computeLowerBoundKernel

lemma globalLowerBoundKernelFinal_eq_16 : globalLowerBoundKernelFinal = 16 := by
  -- globalLowerBoundKernel = 16 and computeLowerBoundKernel = 1
  simp [globalLowerBoundKernelFinal, computeLowerBoundKernel, globalLowerBoundKernel_eq_16]

theorem global_load_lower_bound_kernel (p : Program) (hstraight : StraightLine p)
    (hcorrect : CorrectOn spec_kernel p MemSafeKernel)
    (hsafeExec : ∀ mem, MemSafeKernel mem → SafeExec p mem) :
    ∀ mem, MemSafeKernel mem → KernelLayout mem → KernelSensitive mem → OutputDiffers mem →
      globalLowerBoundKernel ≤ loadLowerCycles (readWordCount p mem) := by
  intro mem hsafe hlayout hks hdiff
  have hmin : MIN_REQUIRED_WORDS_KERNEL ≤ readWordCount p mem := by
    simpa [MIN_REQUIRED_WORDS_KERNEL] using
      min_required_words_kernel_for_mem p hstraight hcorrect hsafeExec mem hsafe hlayout hks hdiff
  exact loadLowerCycles_mono hmin

theorem global_load_lower_bound_kernel_machine (p : Program) (hstraight : StraightLine p)
    (hcorrect : CorrectOnMachine spec_kernel p MemSafeKernel)
    (hsafeExec : ∀ mem, MemSafeKernel mem → SafeExec p mem) :
    ∀ mem, MemSafeKernel mem → KernelLayout mem → KernelSensitive mem → OutputDiffers mem →
      globalLowerBoundKernel ≤ loadLowerCycles (readWordCountMachine p mem) := by
  intro mem hsafe hlayout hks hdiff
  have hmin : MIN_REQUIRED_WORDS_KERNEL ≤ readWordCountMachine p mem := by
    simpa [MIN_REQUIRED_WORDS_KERNEL] using
      min_required_words_kernel_for_mem_machine p hstraight hcorrect hsafeExec mem hsafe hlayout hks hdiff
  exact loadLowerCycles_mono hmin

theorem global_load_lower_bound_kernel_machine_final (p : Program) (hstraight : StraightLine p)
    (hcorrect : CorrectOnMachine spec_kernel p MemSafeKernel)
    (hsafeExec : ∀ mem, MemSafeKernel mem → SafeExec p mem) :
    ∀ mem, MemSafeKernel mem → KernelLayout mem → KernelSensitive mem → OutputDiffers mem →
      globalLowerBoundKernelFinal ≤ loadLowerCycles (readWordCountMachine p mem) := by
  intro mem hsafe hlayout hks hdiff
  have hload : globalLowerBoundKernel ≤ loadLowerCycles (readWordCountMachine p mem) :=
    global_load_lower_bound_kernel_machine p hstraight hcorrect hsafeExec mem hsafe hlayout hks hdiff
  have hcomp : computeLowerBoundKernel ≤ globalLowerBoundKernel := by
    -- computeLowerBoundKernel = 1, globalLowerBoundKernel = 16
    simp [computeLowerBoundKernel, globalLowerBoundKernel_eq_16]
  have hcomp' : computeLowerBoundKernel ≤ loadLowerCycles (readWordCountMachine p mem) :=
    le_trans hcomp hload
  exact (max_le_iff.mpr ⟨hload, hcomp'⟩)

theorem global_load_lower_bound_kernel_exists (p : Program) (hstraight : StraightLine p)
    (hcorrect : CorrectOn spec_kernel p MemSafeKernel)
    (hsafeExec : ∀ mem, MemSafeKernel mem → SafeExec p mem) :
    ∃ mem, globalLowerBoundKernel ≤ loadLowerCycles (readWordCount p mem) := by
  refine ⟨memUniform0, ?_⟩
  have hunif : UniformZeroKernel memUniform0 := uniformZeroKernel_memUniform0
  rcases hunif with
    ⟨hsafe, hrounds, hnodes, hbatch, hheight, hlayout, hdisjoint, hforest, hidx, hval⟩
  have hks : KernelSensitive memUniform0 :=
    kernelSensitive_uniform_zero memUniform0
      ⟨hsafe, hrounds, hnodes, hbatch, hheight, hlayout, hdisjoint, hforest, hidx, hval⟩
  have hdiff : OutputDiffers memUniform0 :=
    outputDiffers_uniform_zero memUniform0
      ⟨hsafe, hrounds, hnodes, hbatch, hheight, hlayout, hdisjoint, hforest, hidx, hval⟩
  exact global_load_lower_bound_kernel p hstraight hcorrect hsafeExec memUniform0 hsafe hlayout hks hdiff
theorem global_load_lower_bound_kernel_machine_final_valid (p : Program) (hstraight : StraightLine p)
    (hcorrect : CorrectOnMachine spec_kernel p MemSafeKernel)
    (hsafeExec : ∀ mem, MemSafeKernel mem → SafeExec p mem) :
    ∀ mem, ValidInput mem →
      globalLowerBoundKernelFinal ≤ loadLowerCycles (readWordCountMachine p mem) := by
  intro mem hvalid
  rcases hvalid with ⟨hsafe, hlayout, hks, hdiff⟩
  exact global_load_lower_bound_kernel_machine_final p hstraight hcorrect hsafeExec mem hsafe hlayout hks hdiff

theorem global_load_lower_bound_kernel_machine_final_valid_16 (p : Program) (hstraight : StraightLine p)
    (hcorrect : CorrectOnMachine spec_kernel p MemSafeKernel)
    (hsafeExec : ∀ mem, MemSafeKernel mem → SafeExec p mem) :
    ∀ mem, ValidInput mem →
      16 ≤ loadLowerCycles (readWordCountMachine p mem) := by
  intro mem hvalid
  have h := global_load_lower_bound_kernel_machine_final_valid p hstraight hcorrect hsafeExec mem hvalid
  simpa [globalLowerBoundKernelFinal_eq_16] using h

theorem global_cycle_lower_bound_kernel_machine_final_valid_16 (p : Program) (hstraight : StraightLine p)
    (hcorrect : CorrectOnMachine spec_kernel p MemSafeKernel)
    (hsafeExec : ∀ mem, MemSafeKernel mem → SafeExec p mem) :
    ∀ mem, ValidInput mem → 16 ≤ cycleCountMachine p mem := by
  intro mem hvalid
  have h16 :
      16 ≤ loadLowerCycles (readWordCountMachine p mem) :=
    global_load_lower_bound_kernel_machine_final_valid_16 p hstraight hcorrect hsafeExec mem hvalid
  rcases hvalid with ⟨hsafe, _hlayout, _hks, _hdiff⟩
  have habort :
      (runMachineFinalFuel p p.program.length mem).aborted = false :=
    runMachineFinalFuel_aborted_false_of_StraightLine_safeExec (p := p) (hstraight := hstraight)
      mem (hsafeExec mem hsafe)
  have hcycles :
      loadLowerCycles (readWordCountMachine p mem) ≤ cycleCountMachine p mem := by
    have h :=
      loadLowerCycles_readWordCountMachineFuel_le_cycleCountMachineFuel
        (p := p) (fuel := p.program.length) (mem := mem) (hnoAbort := habort)
    -- rewrite `fuel=p.program.length` wrappers
    simpa [loadLowerCycles, cycleCountMachine, cycleCountMachineFuel,
      readWordCountMachine, readWordCountMachineFuel, readWordsMachine, readWordsMachineFuel,
      readOpsMachine, readOpsMachineFuel, runMachineTrace, runMachineTraceFuel] using h
  exact le_trans h16 hcycles

theorem global_load_lower_bound_kernel_machine_uniformzero (p : Program) (hstraight : StraightLine p)
    (hcorrect : CorrectOnMachine spec_kernel p MemSafeKernel)
    (hsafeExec : ∀ mem, MemSafeKernel mem → SafeExec p mem) :
    ∀ mem, UniformZeroKernel mem →
      globalLowerBoundKernel ≤ loadLowerCycles (readWordCountMachine p mem) := by
  intro mem hunif
  have hsafe : MemSafeKernel mem := hunif.1
  rcases hunif with ⟨_, hrounds, hnodes, hbatch, hheight, hlayout, hdisjoint, hforest, hidx, hval⟩
  have hks : KernelSensitive mem := kernelSensitive_uniform_zero mem
    ⟨hsafe, hrounds, hnodes, hbatch, hheight, hlayout, hdisjoint, hforest, hidx, hval⟩
  have hdiff : OutputDiffers mem := outputDiffers_uniform_zero mem
    ⟨hsafe, hrounds, hnodes, hbatch, hheight, hlayout, hdisjoint, hforest, hidx, hval⟩
  exact global_load_lower_bound_kernel_machine p hstraight hcorrect hsafeExec mem hsafe hlayout hks hdiff

theorem global_load_lower_bound_kernel_machine_uniformzero_final
    (p : Program) (hstraight : StraightLine p)
    (hcorrect : CorrectOnMachine spec_kernel p MemSafeKernel)
    (hsafeExec : ∀ mem, MemSafeKernel mem → SafeExec p mem) :
    ∀ mem, UniformZeroKernel mem →
      globalLowerBoundKernelFinal ≤ loadLowerCycles (readWordCountMachine p mem) := by
  intro mem hunif
  have hload : globalLowerBoundKernel ≤ loadLowerCycles (readWordCountMachine p mem) :=
    global_load_lower_bound_kernel_machine_uniformzero p hstraight hcorrect hsafeExec mem hunif
  have hcomp : computeLowerBoundKernel ≤ globalLowerBoundKernel := by
    simp [computeLowerBoundKernel, globalLowerBoundKernel_eq_16]
  have hcomp' : computeLowerBoundKernel ≤ loadLowerCycles (readWordCountMachine p mem) :=
    le_trans hcomp hload
  exact (max_le_iff.mpr ⟨hload, hcomp'⟩)

theorem global_load_lower_bound_kernel_machine_adversaryK (p : Program) (hstraight : StraightLine p)
    (hcorrect : CorrectOnMachine spec_kernel p MemSafeKernel)
    (hsafeExec : ∀ mem, MemSafeKernel mem → SafeExec p mem) :
    ∀ mem, MemSafeKernel mem → WritesOutput p mem → memAt mem 0 = ROUNDS → ∀ k, AdversaryK mem k →
      globalLowerBoundKernelK k ≤ loadLowerCycles (readWordCountMachine p mem) := by
  intro mem hsafe hwrites hrounds k hk
  have hmin :
      k * BATCH_SIZE * ROUNDS ≤ readWordCountMachine p mem := by
    have hcount :=
      min_required_words_adversaryK_machine p hstraight hcorrect hsafeExec mem hsafe hwrites k hk
    simpa [hrounds] using hcount
  have hmono := loadLowerCycles_mono hmin
  simpa [globalLowerBoundKernelK] using hmono

theorem global_load_lower_bound_kernel_machine_roundDistinct_256
    (p : Program) (hstraight : StraightLine p)
    (hcorrect : CorrectOnMachine spec_kernel p MemSafeKernel)
    (hsafeExec : ∀ mem, MemSafeKernel mem → SafeExec p mem) :
    ∀ mem, MemSafeKernel mem → WritesOutput p mem → memAt mem 0 = ROUNDS → RoundDistinctNodes mem 1 →
      256 ≤ loadLowerCycles (readWordCountMachine p mem) := by
  intro mem hsafe hwrites hrounds hrd
  have hk : AdversaryK mem 1 := adversaryK_of_roundDistinct mem 1 hrd
  have h :=
    global_load_lower_bound_kernel_machine_adversaryK p hstraight hcorrect hsafeExec
      mem hsafe hwrites hrounds 1 hk
  simpa [globalLowerBoundKernelK_eq_256] using h

theorem global_load_lower_bound_kernel_machine_roundDistinct_512
    (p : Program) (hstraight : StraightLine p)
    (hcorrect : CorrectOnMachine spec_kernel p MemSafeKernel)
    (hsafeExec : ∀ mem, MemSafeKernel mem → SafeExec p mem) :
    ∀ mem, MemSafeKernel mem → WritesOutput p mem → memAt mem 0 = ROUNDS → RoundDistinctNodes mem 2 →
      512 ≤ loadLowerCycles (readWordCountMachine p mem) := by
  intro mem hsafe hwrites hrounds hrd
  have hk : AdversaryK mem 2 := adversaryK_of_roundDistinct mem 2 hrd
  have h :=
    global_load_lower_bound_kernel_machine_adversaryK p hstraight hcorrect hsafeExec
      mem hsafe hwrites hrounds 2 hk
  simpa [globalLowerBoundKernelK_eq_512] using h

/-!
### Cycle-level versions of the structured-adversary bounds

These are immediate now that we have:
1. `loadLowerCycles (readWordCountMachine ...) ≤ cycleCountMachine ...` for straight-line + `SafeExec`.
2. The load-level bounds above (256/512/etc).
-/

lemma loadLowerCycles_readWordCountMachine_le_cycleCountMachine_of_StraightLine_safeExec
    (p : Program) (hstraight : StraightLine p) (mem : Memory) (hsafe : SafeExec p mem) :
    loadLowerCycles (readWordCountMachine p mem) ≤ cycleCountMachine p mem := by
  have habort :
      (runMachineFinalFuel p p.program.length mem).aborted = false :=
    runMachineFinalFuel_aborted_false_of_StraightLine_safeExec (p := p) (hstraight := hstraight) mem hsafe
  have h :=
    loadLowerCycles_readWordCountMachineFuel_le_cycleCountMachineFuel
      (p := p) (fuel := p.program.length) (mem := mem) (hnoAbort := habort)
  -- rewrite `fuel=p.program.length` wrappers
  simpa [loadLowerCycles, cycleCountMachine, cycleCountMachineFuel,
    readWordCountMachine, readWordCountMachineFuel, readWordsMachine, readWordsMachineFuel,
    readOpsMachine, readOpsMachineFuel, runMachineTrace, runMachineTraceFuel] using h

lemma finset_card_le_readWordCountMachine_of_subset
    (p : Program) (mem : Memory) (s : Finset Nat)
    (hsubset : s ⊆ (readWordsMachine p mem).toFinset) :
    s.card ≤ readWordCountMachine p mem := by
  have hcard :
      s.card ≤ (readWordsMachine p mem).toFinset.card := by
    exact Finset.card_le_card hsubset
  have hlen :
      (readWordsMachine p mem).toFinset.card ≤ (readWordsMachine p mem).length := by
    simpa using (List.toFinset_card_le (l := readWordsMachine p mem))
  have hcard_len : s.card ≤ (readWordsMachine p mem).length := le_trans hcard hlen
  simpa [readWordCountMachine] using hcard_len

theorem global_load_lower_bound_machine_of_subset_card
    (p : Program) (mem : Memory) (s : Finset Nat)
    (hsubset : s ⊆ (readWordsMachine p mem).toFinset) :
    loadLowerCycles s.card ≤ loadLowerCycles (readWordCountMachine p mem) := by
  exact loadLowerCycles_mono
    (finset_card_le_readWordCountMachine_of_subset p mem s hsubset)

theorem global_load_lower_bound_machine_of_subset_card_272
    (p : Program) (mem : Memory) (s : Finset Nat)
    (hsubset : s ⊆ (readWordsMachine p mem).toFinset)
    (hcard : s.card = BATCH_SIZE * (ROUNDS + 1)) :
    272 ≤ loadLowerCycles (readWordCountMachine p mem) := by
  have hmono :
      loadLowerCycles s.card ≤ loadLowerCycles (readWordCountMachine p mem) :=
    global_load_lower_bound_machine_of_subset_card p mem s hsubset
  have hmono' :
      globalLowerBoundKernelPlus ≤ loadLowerCycles (readWordCountMachine p mem) := by
    simpa [globalLowerBoundKernelPlus, hcard] using hmono
  simpa [globalLowerBoundKernelPlus_eq_272] using hmono'

theorem global_cycle_lower_bound_machine_of_subset_card_272
    (p : Program) (hstraight : StraightLine p) (mem : Memory)
    (hsafe : SafeExec p mem) (s : Finset Nat)
    (hsubset : s ⊆ (readWordsMachine p mem).toFinset)
    (hcard : s.card = BATCH_SIZE * (ROUNDS + 1)) :
    272 ≤ cycleCountMachine p mem := by
  have h272 : 272 ≤ loadLowerCycles (readWordCountMachine p mem) :=
    global_load_lower_bound_machine_of_subset_card_272 p mem s hsubset hcard
  have hcycles :
      loadLowerCycles (readWordCountMachine p mem) ≤ cycleCountMachine p mem :=
    loadLowerCycles_readWordCountMachine_le_cycleCountMachine_of_StraightLine_safeExec
      (p := p) (hstraight := hstraight) (mem := mem) (hsafe := hsafe)
  exact le_trans h272 hcycles

theorem exists_readWordSet_card_272_of_roundDistinct_values_disjoint
    (p : Program) (hstraight : StraightLine p)
    (hcorrect : CorrectOnMachine spec_kernel p MemSafeKernel)
    (hsafeExec : ∀ mem, MemSafeKernel mem → SafeExec p mem) :
    ∀ mem, MemSafeKernel mem → KernelLayout mem → KernelSensitive mem → OutputDiffers mem →
      memAt mem 0 = ROUNDS → RoundDistinctNodes mem 1 →
      (∀ L, AdversaryList mem L → L.length = BATCH_SIZE * ROUNDS →
        Disjoint L.toFinset (outputAddrs mem)) →
      ∃ s : Finset Nat,
        s ⊆ (readWordsMachine p mem).toFinset ∧
        s.card = BATCH_SIZE * (ROUNDS + 1) := by
  intro mem hsafe hlayout hks hdiff hrounds hrd hdisjoint
  have hcorrect' : CorrectOn spec_kernel p MemSafeKernel :=
    CorrectOnMachine_to_CorrectOn spec_kernel p MemSafeKernel hcorrect
      (fun m _hm => MachineTraceAgrees_of_StraightLine p hstraight m)
  have hwrites : WritesOutput p mem :=
    writesOutput_of_correct_outputDiffers p hcorrect' mem hsafe hdiff
  have hk : AdversaryK mem 1 := adversaryK_of_roundDistinct mem 1 hrd
  rcases hk with ⟨L, hL, hlenK⟩
  rcases hL with ⟨hLnodup, hLsafe, hLsens⟩
  have hlen : L.length = BATCH_SIZE * ROUNDS := by
    simpa [hrounds, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hlenK
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
  have hdisj : Disjoint L.toFinset (outputAddrs mem) := hdisjoint L ⟨hLnodup, hLsafe, hLsens⟩ hlen
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
  exact ⟨L.toFinset ∪ outputAddrs mem, hsubsetUnion, hcardUnion⟩

theorem global_load_lower_bound_kernel_machine_adversaryList_values_disjoint_272
    (p : Program) (hstraight : StraightLine p)
    (hcorrect : CorrectOnMachine spec_kernel p MemSafeKernel)
    (hsafeExec : ∀ mem, MemSafeKernel mem → SafeExec p mem) :
    ∀ mem, MemSafeKernel mem → KernelLayout mem → KernelSensitive mem → OutputDiffers mem →
      ∀ L, AdversaryList mem L → L.length = BATCH_SIZE * ROUNDS →
        Disjoint L.toFinset (outputAddrs mem) →
        272 ≤ loadLowerCycles (readWordCountMachine p mem) := by
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
  exact global_load_lower_bound_machine_of_subset_card_272
    p mem (L.toFinset ∪ outputAddrs mem) hsubsetUnion hcardUnion

theorem global_cycle_lower_bound_kernel_machine_adversaryList_values_disjoint_272
    (p : Program) (hstraight : StraightLine p)
    (hcorrect : CorrectOnMachine spec_kernel p MemSafeKernel)
    (hsafeExec : ∀ mem, MemSafeKernel mem → SafeExec p mem) :
    ∀ mem, MemSafeKernel mem → KernelLayout mem → KernelSensitive mem → OutputDiffers mem →
      ∀ L, AdversaryList mem L → L.length = BATCH_SIZE * ROUNDS →
        Disjoint L.toFinset (outputAddrs mem) →
        272 ≤ cycleCountMachine p mem := by
  intro mem hsafe hlayout hks hdiff L hL hlen hdisj
  have hload :
      272 ≤ loadLowerCycles (readWordCountMachine p mem) :=
    global_load_lower_bound_kernel_machine_adversaryList_values_disjoint_272
      p hstraight hcorrect hsafeExec mem hsafe hlayout hks hdiff L hL hlen hdisj
  have hcycles :
      loadLowerCycles (readWordCountMachine p mem) ≤ cycleCountMachine p mem :=
    loadLowerCycles_readWordCountMachine_le_cycleCountMachine_of_StraightLine_safeExec
      (p := p) (hstraight := hstraight) (mem := mem) (hsafe := hsafeExec mem hsafe)
  exact le_trans hload hcycles

theorem global_load_lower_bound_kernel_machine_roundDistinct_values_disjoint_272
    (p : Program) (hstraight : StraightLine p)
    (hcorrect : CorrectOnMachine spec_kernel p MemSafeKernel)
    (hsafeExec : ∀ mem, MemSafeKernel mem → SafeExec p mem) :
    ∀ mem, MemSafeKernel mem → KernelLayout mem → KernelSensitive mem → OutputDiffers mem →
      memAt mem 0 = ROUNDS → RoundDistinctNodes mem 1 →
      (∀ L, AdversaryList mem L → L.length = BATCH_SIZE * ROUNDS →
        Disjoint L.toFinset (outputAddrs mem)) →
      272 ≤ loadLowerCycles (readWordCountMachine p mem) := by
  intro mem hsafe hlayout hks hdiff hrounds hrd hdisjoint
  have hk : AdversaryK mem 1 := adversaryK_of_roundDistinct mem 1 hrd
  rcases hk with ⟨L, hL, hlenK⟩
  have hlen : L.length = BATCH_SIZE * ROUNDS := by
    simpa [hrounds, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hlenK
  have hdisj : Disjoint L.toFinset (outputAddrs mem) := hdisjoint L hL hlen
  exact global_load_lower_bound_kernel_machine_adversaryList_values_disjoint_272
    p hstraight hcorrect hsafeExec mem hsafe hlayout hks hdiff L hL hlen hdisj

theorem global_cycle_lower_bound_kernel_machine_roundDistinct_values_disjoint_272
    (p : Program) (hstraight : StraightLine p)
    (hcorrect : CorrectOnMachine spec_kernel p MemSafeKernel)
    (hsafeExec : ∀ mem, MemSafeKernel mem → SafeExec p mem) :
    ∀ mem, MemSafeKernel mem → KernelLayout mem → KernelSensitive mem → OutputDiffers mem →
      memAt mem 0 = ROUNDS → RoundDistinctNodes mem 1 →
      (∀ L, AdversaryList mem L → L.length = BATCH_SIZE * ROUNDS →
        Disjoint L.toFinset (outputAddrs mem)) →
      272 ≤ cycleCountMachine p mem := by
  intro mem hsafe hlayout hks hdiff hrounds hrd hdisjoint
  have hload :
      272 ≤ loadLowerCycles (readWordCountMachine p mem) :=
    global_load_lower_bound_kernel_machine_roundDistinct_values_disjoint_272
      p hstraight hcorrect hsafeExec mem hsafe hlayout hks hdiff hrounds hrd hdisjoint
  have hcycles :
      loadLowerCycles (readWordCountMachine p mem) ≤ cycleCountMachine p mem :=
    loadLowerCycles_readWordCountMachine_le_cycleCountMachine_of_StraightLine_safeExec
      (p := p) (hstraight := hstraight) (mem := mem) (hsafe := hsafeExec mem hsafe)
  exact le_trans hload hcycles

theorem global_cycle_lower_bound_kernel_machine_roundDistinct_256
    (p : Program) (hstraight : StraightLine p)
    (hcorrect : CorrectOnMachine spec_kernel p MemSafeKernel)
    (hsafeExec : ∀ mem, MemSafeKernel mem → SafeExec p mem) :
    ∀ mem, MemSafeKernel mem → WritesOutput p mem → memAt mem 0 = ROUNDS → RoundDistinctNodes mem 1 →
      256 ≤ cycleCountMachine p mem := by
  intro mem hsafe hwrites hrounds hrd
  have h256 : 256 ≤ loadLowerCycles (readWordCountMachine p mem) :=
    global_load_lower_bound_kernel_machine_roundDistinct_256 p hstraight hcorrect hsafeExec
      mem hsafe hwrites hrounds hrd
  have hcycles :
      loadLowerCycles (readWordCountMachine p mem) ≤ cycleCountMachine p mem :=
    loadLowerCycles_readWordCountMachine_le_cycleCountMachine_of_StraightLine_safeExec
      (p := p) (hstraight := hstraight) (mem := mem) (hsafe := hsafeExec mem hsafe)
  exact le_trans h256 hcycles

theorem global_cycle_lower_bound_kernel_machine_roundDistinct_512
    (p : Program) (hstraight : StraightLine p)
    (hcorrect : CorrectOnMachine spec_kernel p MemSafeKernel)
    (hsafeExec : ∀ mem, MemSafeKernel mem → SafeExec p mem) :
    ∀ mem, MemSafeKernel mem → WritesOutput p mem → memAt mem 0 = ROUNDS → RoundDistinctNodes mem 2 →
      512 ≤ cycleCountMachine p mem := by
  intro mem hsafe hwrites hrounds hrd
  have h512 : 512 ≤ loadLowerCycles (readWordCountMachine p mem) :=
    global_load_lower_bound_kernel_machine_roundDistinct_512 p hstraight hcorrect hsafeExec
      mem hsafe hwrites hrounds hrd
  have hcycles :
      loadLowerCycles (readWordCountMachine p mem) ≤ cycleCountMachine p mem :=
    loadLowerCycles_readWordCountMachine_le_cycleCountMachine_of_StraightLine_safeExec
      (p := p) (hstraight := hstraight) (mem := mem) (hsafe := hsafeExec mem hsafe)
  exact le_trans h512 hcycles

lemma outputDiffers_memBig : OutputDiffers memBig := by
  intro i
  have hspec : spec_kernel memBig i = iterHash ROUNDS 0 := spec_kernel_memBig i
  have hval : memAt memBig (memAt memBig PTR_INP_VAL + i) = 0 := by
    have hptrV : memAt memBig PTR_INP_VAL = BIG_VAL_BASE := (memBig_ptrs).2.2
    simpa [hptrV] using memBig_val0 i
  simpa [hspec, hval] using iterHash_ne_zero

lemma writesOutput_memBig_of_correctMachine
    (p : Program) (hstraight : StraightLine p)
    (hcorrect : CorrectOnMachine spec_kernel p MemSafeKernel) :
    WritesOutput p memBig := by
  have hcorrect' : CorrectOn spec_kernel p MemSafeKernel :=
    CorrectOnMachine_to_CorrectOn spec_kernel p MemSafeKernel hcorrect
      (fun m _hm => MachineTraceAgrees_of_StraightLine p hstraight m)
  exact writesOutput_of_correct_outputDiffers p hcorrect' memBig memBig_safe outputDiffers_memBig

theorem global_cycle_lower_bound_kernel_machine_memBig_256
    (p : Program) (hstraight : StraightLine p)
    (hcorrect : CorrectOnMachine spec_kernel p MemSafeKernel)
    (hsafeExec : ∀ mem, MemSafeKernel mem → SafeExec p mem) :
    256 ≤ cycleCountMachine p memBig := by
  have hwrites : WritesOutput p memBig :=
    writesOutput_memBig_of_correctMachine p hstraight hcorrect
  exact global_cycle_lower_bound_kernel_machine_roundDistinct_256 p hstraight hcorrect hsafeExec
    memBig memBig_safe hwrites memBig_rounds memBig_roundDistinct_1

def memBigValBump (i : Fin BATCH_SIZE) : Memory :=
  memUpdate memBig (BIG_VAL_BASE + i) (memAt memBig (BIG_VAL_BASE + i) + 1)

theorem spec_kernel_memBigValBump_ne_all :
    ∀ i : Fin BATCH_SIZE,
      spec_kernel (memBigValBump i) i ≠ spec_kernel memBig i := by
  native_decide

theorem spec_kernel_memBigValBump_ne (i : Fin BATCH_SIZE) :
    spec_kernel (memBigValBump i) i ≠ spec_kernel memBig i :=
  spec_kernel_memBigValBump_ne_all i

lemma memBigTreeAddrs_subset_readWordsMachine_of_correctMachine
    (p : Program) (hstraight : StraightLine p)
    (hcorrect : CorrectOnMachine spec_kernel p MemSafeKernel)
    (hsafeExec : ∀ mem, MemSafeKernel mem → SafeExec p mem) :
    memBigTreeAddrs ⊆ (readWordsMachine p memBig).toFinset := by
  have hwrites : WritesOutput p memBig :=
    writesOutput_memBig_of_correctMachine p hstraight hcorrect
  intro a ha
  rcases Finset.mem_image.1 ha with ⟨t, _ht, rfl⟩
  have haddr : AddrSafe memBig (BIG_FOREST_BASE + idxAtR t.1 t.2) :=
    memBig_tree_addr_safe t.1 t.2
  have hsens :
      ∃ i : Fin BATCH_SIZE,
        spec_kernel
            (memUpdate memBig (BIG_FOREST_BASE + idxAtR t.1 t.2)
              (memAt memBig (BIG_FOREST_BASE + idxAtR t.1 t.2) + 1)) i
          ≠ spec_kernel memBig i := by
    refine ⟨t.2, ?_⟩
    simpa [memBigForestBump] using (spec_kernel_memBigForestBump_ne t.1 t.2)
  exact List.mem_toFinset.2 <|
    must_read_addr_machine p hstraight hcorrect hsafeExec
      memBig memBig_safe hwrites (BIG_FOREST_BASE + idxAtR t.1 t.2) haddr hsens

lemma memBigValAddrs_subset_readWordsMachine_of_correctMachine
    (p : Program) (hstraight : StraightLine p)
    (hcorrect : CorrectOnMachine spec_kernel p MemSafeKernel)
    (hsafeExec : ∀ mem, MemSafeKernel mem → SafeExec p mem) :
    memBigValAddrs ⊆ (readWordsMachine p memBig).toFinset := by
  have hwrites : WritesOutput p memBig :=
    writesOutput_memBig_of_correctMachine p hstraight hcorrect
  intro a ha
  rcases Finset.mem_image.1 ha with ⟨i, _hi, rfl⟩
  have haddr : AddrSafe memBig (BIG_VAL_BASE + i) := memBig_val_addr_safe i
  have hsens :
      ∃ j : Fin BATCH_SIZE,
        spec_kernel
            (memUpdate memBig (BIG_VAL_BASE + i)
              (memAt memBig (BIG_VAL_BASE + i) + 1)) j
          ≠ spec_kernel memBig j := by
    refine ⟨i, ?_⟩
    simpa [memBigValBump] using (spec_kernel_memBigValBump_ne i)
  exact List.mem_toFinset.2 <|
    must_read_addr_machine p hstraight hcorrect hsafeExec
      memBig memBig_safe hwrites (BIG_VAL_BASE + i) haddr hsens

lemma memBigAllAddrs_subset_readWordsMachine_of_correctMachine
    (p : Program) (hstraight : StraightLine p)
    (hcorrect : CorrectOnMachine spec_kernel p MemSafeKernel)
    (hsafeExec : ∀ mem, MemSafeKernel mem → SafeExec p mem) :
    memBigAllAddrs ⊆ (readWordsMachine p memBig).toFinset := by
  intro a ha
  rcases Finset.mem_union.1 ha with htree | hval
  · exact memBigTreeAddrs_subset_readWordsMachine_of_correctMachine p hstraight hcorrect hsafeExec htree
  · exact memBigValAddrs_subset_readWordsMachine_of_correctMachine p hstraight hcorrect hsafeExec hval

theorem global_load_lower_bound_kernel_machine_big_272
    (p : Program) (_hcorrect : CorrectOnMachine spec_kernel p MemSafeKernel)
    (hsubset : memBigAllAddrs ⊆ (readWordsMachine p memBig).toFinset) :
    272 ≤ loadLowerCycles (readWordCountMachine p memBig) := by
  exact global_load_lower_bound_machine_of_subset_card_272
    p memBig memBigAllAddrs hsubset memBigAllAddrs_card

theorem global_load_lower_bound_kernel_machine_big_256
    (p : Program) (_hcorrect : CorrectOnMachine spec_kernel p MemSafeKernel)
    (hsubset : memBigAllAddrs ⊆ (readWordsMachine p memBig).toFinset) :
    256 ≤ loadLowerCycles (readWordCountMachine p memBig) := by
  have h272 : 272 ≤ loadLowerCycles (readWordCountMachine p memBig) :=
    global_load_lower_bound_kernel_machine_big_272 p _hcorrect hsubset
  exact le_trans (by decide : 256 ≤ 272) h272

theorem global_cycle_lower_bound_kernel_machine_big_272
    (p : Program) (hstraight : StraightLine p)
    (hcorrect : CorrectOnMachine spec_kernel p MemSafeKernel)
    (hsafeExec : ∀ mem, MemSafeKernel mem → SafeExec p mem)
    (hsubset : memBigAllAddrs ⊆ (readWordsMachine p memBig).toFinset) :
    272 ≤ cycleCountMachine p memBig := by
  exact global_cycle_lower_bound_machine_of_subset_card_272
    p hstraight memBig (hsafeExec memBig memBig_safe)
    memBigAllAddrs hsubset memBigAllAddrs_card

theorem global_cycle_lower_bound_kernel_machine_memBig_272
    (p : Program) (hstraight : StraightLine p)
    (hcorrect : CorrectOnMachine spec_kernel p MemSafeKernel)
    (hsafeExec : ∀ mem, MemSafeKernel mem → SafeExec p mem) :
    272 ≤ cycleCountMachine p memBig := by
  have hsubset : memBigAllAddrs ⊆ (readWordsMachine p memBig).toFinset :=
    memBigAllAddrs_subset_readWordsMachine_of_correctMachine p hstraight hcorrect hsafeExec
  exact global_cycle_lower_bound_kernel_machine_big_272 p hstraight hcorrect hsafeExec hsubset

theorem global_load_lower_bound_kernel_machine_exists_big_256
    (p : Program) (_hcorrect : CorrectOnMachine spec_kernel p MemSafeKernel)
    (hsubset : memBigAllAddrs ⊆ (readWordsMachine p memBig).toFinset) :
    ∃ mem, 256 ≤ loadLowerCycles (readWordCountMachine p mem) := by
  exact ⟨memBig, global_load_lower_bound_kernel_machine_big_256 p _hcorrect hsubset⟩

theorem global_load_lower_bound_kernel_machine_exists_big_272
    (p : Program) (_hcorrect : CorrectOnMachine spec_kernel p MemSafeKernel)
    (hsubset : memBigAllAddrs ⊆ (readWordsMachine p memBig).toFinset) :
    ∃ mem, 272 ≤ loadLowerCycles (readWordCountMachine p mem) := by
  exact ⟨memBig, global_load_lower_bound_kernel_machine_big_272 p _hcorrect hsubset⟩

theorem global_cycle_lower_bound_kernel_machine_exists_big_272
    (p : Program) (hstraight : StraightLine p)
    (_hcorrect : CorrectOnMachine spec_kernel p MemSafeKernel)
    (hsafeExec : ∀ mem, MemSafeKernel mem → SafeExec p mem)
    (hsubset : memBigAllAddrs ⊆ (readWordsMachine p memBig).toFinset) :
    ∃ mem, 272 ≤ cycleCountMachine p mem := by
  exact ⟨memBig, global_cycle_lower_bound_kernel_machine_big_272 p hstraight _hcorrect hsafeExec hsubset⟩
lemma globalLowerBound_eq :
    globalLowerBound = ceilDiv (ceilDiv MIN_REQUIRED_WORDS VLEN) LOAD_CAP := by
  rfl

end ProofGlobalLowerBound
