import proofs.global_lower_bound.LowerBound.Specs
import proofs.global_lower_bound.LowerBound.TraceEq

namespace ProofGlobalLowerBound
open ProofCommon
open ProofMachine
open ProofISA

lemma spec_values_diff (mem : Memory) (i : Fin BATCH_SIZE)
    (hneq : memAt mem PTR_INP_VAL + i ≠ PTR_INP_VAL) :
    spec_values
        (memUpdate mem (memAt mem PTR_INP_VAL + i)
          (memAt mem (memAt mem PTR_INP_VAL + i) + 1)) i
      ≠ spec_values mem i := by
  set addr := memAt mem PTR_INP_VAL + i
  have hptr :
      memAt (memUpdate mem addr (memAt mem addr + 1)) PTR_INP_VAL = memAt mem PTR_INP_VAL := by
    simpa using (memUpdate_ptr_eq mem addr (memAt mem addr + 1) (by simpa [addr] using hneq))
  have hnew :
      spec_values (memUpdate mem addr (memAt mem addr + 1)) i = memAt mem addr + 1 := by
    calc
      spec_values (memUpdate mem addr (memAt mem addr + 1)) i
          =
          memAt (memUpdate mem addr (memAt mem addr + 1))
            (memAt (memUpdate mem addr (memAt mem addr + 1)) PTR_INP_VAL + i) := by
            simp [spec_values, outputOf]
      _ =
          memAt (memUpdate mem addr (memAt mem addr + 1))
            (memAt mem PTR_INP_VAL + i) := by
            simp [hptr]
      _ = memAt (memUpdate mem addr (memAt mem addr + 1)) addr := by
            simp [addr]
      _ = memAt mem addr + 1 := by
            simp [memAt, memUpdate]
  have hold : spec_values mem i = memAt mem addr := by
    simp [spec_values, outputOf, memAt, addr]
  have hdiff : memAt mem addr + 1 ≠ memAt mem addr := by
    simpa [Nat.succ_eq_add_one] using (Nat.succ_ne_self (memAt mem addr))
  simpa [hnew, hold] using hdiff
theorem must_read_values (p : Program)
    (hcorrect : CorrectOn spec_values p MemSafeValues)
    (hsafe : ∀ mem, MemSafeValues mem → SafeExec p mem)
    (hlayout : ∀ mem, MemSafeValues mem → ValuesLayout mem) :
    ∀ mem, MemSafeValues mem → WritesOutput p mem → ∀ i : Fin BATCH_SIZE,
      (memAt mem PTR_INP_VAL + i) ∈ readWords p mem := by
  intro mem hsafe_mem hwrites i
  by_contra hnot
  set addr := memAt mem PTR_INP_VAL + i
  let mem' := memUpdate mem addr (memAt mem addr + 1)
  have hneq : addr ≠ PTR_INP_VAL :=
    ptr_inp_val_ne_input_addr (hlayout mem hsafe_mem) i
  have hptr : memAt mem PTR_INP_VAL = memAt mem' PTR_INP_VAL := by
    symm
    simpa [mem', addr] using (memUpdate_ptr_eq mem addr (memAt mem addr + 1) hneq)
  have hsize : mem.size = mem'.size := by
    simp [mem', memUpdate]
  have hsafe' : MemSafeValues mem' := by
    -- pointer and size preserved
    exact memSafeValues_of_eq_ptr mem mem' hsize hptr hsafe_mem
  have hagree : AgreeOnList (readWords p mem) mem mem' := by
    refine ⟨hsize, ?_⟩
    intro a ha
    have hneq' : a ≠ addr := by
      intro hEq
      apply hnot
      simpa [addr, hEq] using ha
    -- memUpdate does not affect other addresses
    simpa [mem', addr] using (memUpdate_eq_of_ne mem addr (memAt mem addr + 1) a hneq').symm
  have hrun :
      run p mem = run p mem' := by
    exact run_eq_of_agree p mem mem' hptr hagree hwrites
      (hsafe mem hsafe_mem) (hsafe mem' hsafe')
  have hspec : spec_values mem' i ≠ spec_values mem i := by
    -- flipping one output word changes `spec_values` at that lane
    simpa [addr, mem'] using (spec_values_diff mem i (by simpa [addr] using hneq))
  -- correctness links run to spec_values
  have hcorr1 := congrArg (fun f => f i) (hcorrect mem hsafe_mem)
  have hcorr2 := congrArg (fun f => f i) (hcorrect mem' hsafe')
  have hrun_i := congrArg (fun f => f i) hrun
  have : spec_values mem' i = spec_values mem i := by
    calc
      spec_values mem' i = run p mem' i := by symm; exact hcorr2
      _ = run p mem i := by symm; exact hrun_i
      _ = spec_values mem i := hcorr1
  exact hspec this
theorem outputAddrs_subset_readWords (p : Program)
    (hcorrect : CorrectOn spec_values p MemSafeValues)
    (hsafe : ∀ mem, MemSafeValues mem → SafeExec p mem)
    (hlayout : ∀ mem, MemSafeValues mem → ValuesLayout mem)
    (mem : Memory) (hsafe_mem : MemSafeValues mem) (hwrites : WritesOutput p mem) :
    outputAddrs mem ⊆ (readWords p mem).toFinset := by
  intro a ha
  classical
  -- outputAddrs are exactly base + i
  rcases Finset.mem_image.1 ha with ⟨i, hi, rfl⟩
  have hmem :
      (memAt mem PTR_INP_VAL + i) ∈ readWords p mem :=
    must_read_values p hcorrect hsafe hlayout mem hsafe_mem hwrites i
  simpa using hmem

theorem min_required_words_values (p : Program)
    (hcorrect : CorrectOn spec_values p MemSafeValues)
    (hsafe : ∀ mem, MemSafeValues mem → SafeExec p mem)
    (hlayout : ∀ mem, MemSafeValues mem → ValuesLayout mem) :
    ∀ mem, MemSafeValues mem → WritesOutput p mem → BATCH_SIZE ≤ readWordCount p mem := by
  intro mem hsafe_mem hwrites
  have hsubset :=
    outputAddrs_subset_readWords p hcorrect hsafe hlayout mem hsafe_mem hwrites
  have hcard := outputAddrs_card mem
  have hcard_le : (outputAddrs mem).card ≤ (readWords p mem).toFinset.card :=
    by
      simpa using (Finset.card_le_card hsubset)
  have hlen : (readWords p mem).toFinset.card ≤ (readWords p mem).length := by
    simpa using (List.toFinset_card_le (l := readWords p mem))
  have : BATCH_SIZE ≤ (readWords p mem).length := by
    simpa [hcard] using (le_trans hcard_le hlen)
  simpa [readWordCount] using this
end ProofGlobalLowerBound
