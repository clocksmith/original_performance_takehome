import proofs.global_lower_bound.LowerBound.MemBigRoundDistinctHelpers

namespace ProofGlobalLowerBound
open ProofCommon
open ProofMachine
open ProofISA

/-!
`memBig` witness for the structured-adversary predicate `RoundDistinctNodes`.

This is the missing ingredient needed to instantiate the existing
`RoundDistinctNodes mem 1 → 256 ≤ cycleCountMachine ...` theorems.

We keep this Lean-only by discharging per-(round,lane) sensitivity via `native_decide`
over the finite instance (`ROUNDS = 16`, `BATCH_SIZE = 32`).
-/

theorem spec_kernel_memBigForestBump_ne_all :
    ∀ r : Fin ROUNDS, ∀ i : Fin BATCH_SIZE,
      spec_kernel (memBigForestBump r i) i ≠ spec_kernel memBig i := by
  -- Keep the proof term small: decide the closed proposition in one shot.
  native_decide

theorem spec_kernel_memBigForestBump_ne (r : Fin ROUNDS) (i : Fin BATCH_SIZE) :
    spec_kernel (memBigForestBump r i) i ≠ spec_kernel memBig i :=
  spec_kernel_memBigForestBump_ne_all r i

theorem memBig_roundDistinct_1 : RoundDistinctNodes memBig 1 := by
  classical
  refine ⟨(fun r i _ => BIG_FOREST_BASE + idxAtR r i), ?_, ?_, ?_⟩
  · intro r i j
    simpa using memBig_tree_addr_safe r i
  · intro r i j
    refine ⟨i, ?_⟩
    -- `RoundDistinctNodes` uses `memUpdate mem addr (memAt mem addr + 1)`;
    -- that's definitionally `memBigForestBump`.
    simpa [memBigForestBump] using (spec_kernel_memBigForestBump_ne r i)
  · intro a b hab
    rcases a with ⟨ra, ia, ja⟩
    rcases b with ⟨rb, ib, jb⟩
    have hja : ja = 0 := Subsingleton.elim _ _
    have hjb : jb = 0 := Subsingleton.elim _ _
    subst hja; subst hjb
    have : idxAtR ra ia = idxAtR rb ib := Nat.add_left_cancel hab
    have hpair : (ra, ia) = (rb, ib) := idxAtR_inj this
    cases hpair
    rfl

end ProofGlobalLowerBound
