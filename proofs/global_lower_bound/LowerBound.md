Global lower bound (Phase 1 plan)

We’ve moved from an abstract scaffold to a semantics‑anchored model, but we’re still in Phase 1.
The core idea is now real: the program is executed via `ProofMachine.execInstruction`, and both
the final memory (`runMem`) and the per‑load‑slot trace (`readOps`) are derived from that execution.
This prevents trace‑forging and gives a concrete bridge from execution → read trace → load‑op lower
bounds. The remaining gap is correctness: we still need to formalize the program class and the
adversarial argument that forces a minimum number of words to be read for all inputs.

Where we are now

- Program execution is straight‑line over a concrete `List Instruction` using `execInstruction`.
- `readOps` is a per‑load‑slot trace: each load slot contributes a list of addresses; `const` produces
  `[]` but still counts as a load slot.
- `readOps_bound` is derived from the load semantics; `loadOps_lower_bound` is proved from it using
  list length + `ceilDiv`.
- Output is fixed‑size (`Fin BATCH_SIZE → Nat`) and projected via
  `outputOf (mem[6]) (runMem mem)` (matching the values slice pointer in the problem layout).
  This is the **values‑slice spec** (identity projection), not the full kernel semantics.

This already formalizes the arithmetic pipeline: required words → load ops → cycles. We now also
have a full adversarial lemma for the **values‑slice spec** (identity projection from `mem[6]`),
and a distinct‑address counting argument, so **MIN_REQUIRED_WORDS = BATCH_SIZE** is proved.

What’s complete now

1) Program class predicate (Phase 1).
   `StraightLine p` is formalized and forbids control‑flow slots.

2) Concrete output projection.
   The output slice is anchored to `mem[6]` (values pointer) in `spec_values` and `run`.

3) Trace‑equivalence non‑interference.
   Trace‑conditioned non‑interference is proved for straight‑line execution.

4) Adversarial input lemma (global).
   A formal adversarial lemma shows all BATCH_SIZE output addresses appear in the read trace for a
   single run; hence BATCH_SIZE words are required.

5) MIN_REQUIRED_WORDS updated.
   `MIN_REQUIRED_WORDS := BATCH_SIZE`, giving a non‑trivial global load lower bound.

Remaining optional work

- Extend the model to bounded control flow (beyond StraightLine).
- Add a global compute bound and take `max(load, compute)` for a stronger statement.

This yields a fully verifiable global load lower bound for the values‑slice spec, not tied to any
specific caching strategy. We also added a **full‑kernel reference spec** (`spec_kernel`) and now
prove **BATCH_SIZE** addresses must be read for a single adversarial memory (`memUniform0`), giving
the same 16‑cycle load bound for the full kernel under ∃mem.

Formal theorems:
- `global_load_lower_bound` (values‑slice): ∀ mem, `globalLowerBound ≤ loadLowerCycles (readWordCount p mem)`.
- `global_load_lower_bound_kernel` (full kernel, current): ∃ mem, `globalLowerBoundKernel ≤ loadLowerCycles (readWordCount p mem)`.

Formal theorem added:
- `global_load_lower_bound`: for any StraightLine program correct for `spec_values`,
  `globalLowerBound ≤ loadLowerCycles (readWordCount p mem)` for all memories.
