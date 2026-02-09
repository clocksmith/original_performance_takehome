import proofs.global_lower_bound.LowerBound.MachineTraceEq
import proofs.global_lower_bound.LowerBound.Adversary

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
theorem global_load_lower_bound_kernel_machine_big_272
    (p : Program) (hcorrect : CorrectOnMachine spec_kernel p MemSafeKernel) :
    272 ≤ loadLowerCycles (readWordCountMachine p memBig) := by
  have hmin : BATCH_SIZE * (ROUNDS + 1) ≤ readWordCountMachine p memBig :=
    min_required_words_kernel_machine_memBig_all p hcorrect
  have hmono :
      loadLowerCycles (BATCH_SIZE * (ROUNDS + 1)) ≤
        loadLowerCycles (readWordCountMachine p memBig) :=
    loadLowerCycles_mono hmin
  have hmono' :
      globalLowerBoundKernelPlus ≤ loadLowerCycles (readWordCountMachine p memBig) := by
    simpa [globalLowerBoundKernelPlus] using hmono
  -- `globalLowerBoundKernelPlus = 272`
  simpa [globalLowerBoundKernelPlus_eq_272] using hmono'

theorem global_load_lower_bound_kernel_machine_big_256
    (p : Program) (hcorrect : CorrectOnMachine spec_kernel p MemSafeKernel) :
    256 ≤ loadLowerCycles (readWordCountMachine p memBig) := by
  have h272 : 272 ≤ loadLowerCycles (readWordCountMachine p memBig) :=
    global_load_lower_bound_kernel_machine_big_272 p hcorrect
  exact le_trans (by decide : 256 ≤ 272) h272
theorem global_load_lower_bound_kernel_machine_exists_big_256
    (p : Program) (hcorrect : CorrectOnMachine spec_kernel p MemSafeKernel) :
    ∃ mem, 256 ≤ loadLowerCycles (readWordCountMachine p mem) := by
  exact ⟨memBig, global_load_lower_bound_kernel_machine_big_256 p hcorrect⟩

theorem global_load_lower_bound_kernel_machine_exists_big_272
    (p : Program) (hcorrect : CorrectOnMachine spec_kernel p MemSafeKernel) :
    ∃ mem, 272 ≤ loadLowerCycles (readWordCountMachine p mem) := by
  exact ⟨memBig, global_load_lower_bound_kernel_machine_big_272 p hcorrect⟩
lemma globalLowerBound_eq :
    globalLowerBound = ceilDiv (ceilDiv MIN_REQUIRED_WORDS VLEN) LOAD_CAP := by
  rfl

end ProofGlobalLowerBound
