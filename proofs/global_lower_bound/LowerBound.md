Global lower bound (Phase 1, frozen-aligned)

We now model the frozen machine semantics directly. Programs execute via
`ProofMachine.execInstruction`, and both the final memory (`runMem`) and the
per-load-slot trace (`readOps`) are derived from that execution. This prevents
trace forging and gives a concrete bridge from execution → read trace → load-op
lower bounds.

Alignment with frozen_problem.py

- Memory is bounded: `Mem` carries `size`, and `memRead`/`memWrite` return `none`
  on OOB. `execInstruction` fails on invalid loads/stores (matching Python
  index errors).
- Scratch is bounded: `instrScratchBounded` enforces all scratch indices are
  within `SCRATCH_SIZE`.
- Flow jump targets are **immediates** (not scratch). We provide optional PC
  bounds: `flowSlotPcBoundedAt` and `instrPcBoundedAt` check that absolute
  jumps are within `[0, progLen)` and that relative jumps keep `pc+offset` in
  range for a given `pc`. The older `instrPcBounded` is a shorthand at `pc=0`.
- Load semantics match frozen: load/vload/load_offset write raw values, while
  `const` and ALU/VALU operations enforce mod-32 behavior.
- The full-kernel spec (`spec_kernel`) reads header fields (`mem[0..6]`) exactly
  like `reference_kernel2` in `tests/frozen_problem.py`.

Where we are now

- Program execution is straight-line over a concrete `List Instruction`.
- `readOps` is a per-load-slot trace: each load slot contributes a list of
  addresses; `const` produces `[]` but still counts as a load slot.
- `runTraceAux` now halts if `execInstruction` returns `ok=false` (e.g. OOB),
  matching the machine’s stop-on-error behavior.
- `readOps_bound` is derived from load semantics; `loadOps_lower_bound` follows
  from list length + `ceilDiv`.
- Output is fixed-size (`Fin BATCH_SIZE → Nat`) and projected via
  `outputOf (mem[6]) (runMem mem)` (values-slice pointer).
  All correctness theorems now assume a **memory-safety predicate**:
  `MemSafeValues` for values-slice and `MemSafeKernel` for the full kernel.
  `MemSafeKernel` also requires `mem[2] = BATCH_SIZE` since the output arity is
  fixed to `BATCH_SIZE` in this model.

We also provide a **trace-aware run** based on `stepMachine` and PC control flow:
`runMachineTrace` executes the machine for `program.length` steps, collects the
per-load-slot trace, and returns `runMemMachine` / `readOpsMachine`. This is the
PC-faithful counterpart to the straight-line `runTrace` used in the Phase 1
proofs.

PC-trace bridge (current)

We introduced `MachineTraceAgrees p mem := runMachineTrace p mem = runTrace p mem`,
but the PC-trace bounds now avoid this bridge entirely: they are proved directly
against `runMachineTrace` and `readWordsMachine`. The straight-line bridge lemma
(`MachineTraceAgrees_of_StraightLine`) is still available as a compatibility
tool, but the main theorems no longer depend on it.

Fuel and PC-bounded control flow

We also provide fuel-indexed semantics (`runMachineTraceFuel`, `readWordsMachineFuel`,
`CorrectOnMachineFuel`). This supports bounded control-flow reasoning: you can
state correctness and lower bounds relative to a concrete max-steps budget. A
program-class predicate `PcBoundedProgram` (using `instrPcBoundedAt`) is now
defined, and PC-bounded variants of the fuel theorems are provided
(`*_fuel_pcbounded`) to make the control-flow assumptions explicit.

Values-slice bound (∀ mem, MemSafeValues mem)

We have a full adversarial lemma for the values-slice spec, plus a distinct-
address counting argument, so **MIN_REQUIRED_WORDS = BATCH_SIZE** is proved.
This yields a uniform (all-memories) load lower bound:

- `global_load_lower_bound_machine`:
  for any program correct for `spec_values` on safe memories (machine semantics),
  `globalLowerBound ≤ loadLowerCycles (readWordCountMachine p mem)` for all mem
  with `MemSafeValues mem`.

Full-kernel bound (∀ mem, under sensitivity assumptions)

We added `spec_kernel` (hash + traversal, 16 rounds) using the frozen header
layout. The full-kernel lower bound now holds for **all** memories that satisfy:

- `MemSafeKernel` (header + bounds safety),
- `KernelLayout` (pointers live at/after header), and
- `KernelSensitive` (per-lane output changes if that lane’s input value changes).

Under those assumptions:

- `global_load_lower_bound_kernel_machine`:
  for any program correct for `spec_kernel` on safe memories (machine semantics),
  for all `mem` satisfying the above predicates,
  `globalLowerBoundKernel ≤ loadLowerCycles (readWordCountMachine p mem)`.

We still keep the older **existential** witness bound (useful for regression
tests) based on `memUniform0`:

- `global_load_lower_bound_kernel_exists`:
  ∃ mem (namely `memUniform0`) with the same lower bound.

Concrete adversarial class (proved sensitive)

We now prove `KernelSensitive` for a concrete adversarial input class
`UniformZeroKernel`: a memory with MemSafeKernel, the frozen header, disjoint
layout, zero tree values, and zero idx/val slices. For this class, flipping one
lane’s input value changes that lane’s output, so the universal bound applies
under `UniformZeroKernel` alone.

Program class (PC-bounded)

We define `ProgramClass` to bundle scratch bounds and PC-bounded control flow:
`instrScratchBounded` for each instruction and `instrPcBoundedAt` for each pc.
Theorems `global_load_lower_bound_kernel_machine_pc` and
`global_load_lower_bound_kernel_machine_uniformzero` make these assumptions
explicit for ISA-accurate lower bounds.

Packaged “true lower bound” statement

For the concrete adversarial class `UniformZeroKernel`, the final packaged
statement is:

- `global_load_lower_bound_kernel_machine_uniformzero_final`:
  for any `ProgramClass` program correct on `spec_kernel`, and any
  `UniformZeroKernel` memory,  
  `globalLowerBoundKernelFinal ≤ loadLowerCycles (readWordCountMachine p mem)`.

Compute bound (weak)

We introduce a minimal compute lower bound `computeLowerBoundKernel = 1` and
define `globalLowerBoundKernelFinal = max(globalLowerBoundKernel, computeLowerBoundKernel)`.
Since the proven load lower bound is 16 cycles, the final bound remains 16. This
is formalized in `global_load_lower_bound_kernel_machine_final`.

Remaining optional work

- Stronger conditional bounds via AdversaryK
  We also formalize an adversarial class that supplies a **set of
  k · BATCH_SIZE · ROUNDS addresses**, each of which individually flips some
  output when updated:
  `AdversaryK mem k := ∃ L, AdversaryList mem L ∧ L.length = k * BATCH_SIZE * mem[0]`.
  (`AdversaryList` requires each address to satisfy `AddrSafe mem addr`,
  i.e., `HEADER_SIZE ≤ addr` and `addr < mem.size`.)
  This yields a load lower bound of
  `globalLowerBoundKernelK k = loadLowerCycles (k * BATCH_SIZE * ROUNDS)` for
  any correct program and any `mem` satisfying `MemSafeKernel`, `mem[0]=ROUNDS`,
  and `AdversaryK mem k`. For the concrete adversarial class `UniformZeroKernel`
  this specializes to two conditional bounds:

  - `global_load_lower_bound_kernel_machine_uniformzero_256` (k = 1) ⇒ **256 cycles**
  - `global_load_lower_bound_kernel_machine_uniformzero_512` (k = 2) ⇒ **512 cycles**

  These bounds are **conditional** on `AdversaryK` (i.e., you must still prove
  that the chosen adversary class yields the required number of distinct,
  output‑sensitive addresses in a single run).

  We also define a more structured predicate `RoundDistinctNodes mem k`, which
  supplies an injective mapping from `(round, lane, copy)` to addresses and a
  per‑address sensitivity witness. We prove
  `RoundDistinctNodes → AdversaryK`, yielding:

  - `global_load_lower_bound_kernel_machine_roundDistinct_256`
  - `global_load_lower_bound_kernel_machine_roundDistinct_512`

  We also provide a composition theorem that combines:
  - `RoundDistinctNodes mem 1` (round/lane-sensitive addresses),
  - value-sensitivity assumptions (`KernelLayout`, `KernelSensitive`,
    `OutputDiffers`), and
  - an explicit disjointness condition between the adversary list and
    `outputAddrs mem`,
  to obtain the stronger `272` bound:

  - `exists_readWordSet_card_272_of_roundDistinct_values_disjoint`
  - `global_load_lower_bound_kernel_machine_adversaryList_values_disjoint_272`
  - `global_cycle_lower_bound_kernel_machine_adversaryList_values_disjoint_272`
  - `global_load_lower_bound_kernel_machine_roundDistinct_values_disjoint_272`
  - `global_cycle_lower_bound_kernel_machine_roundDistinct_values_disjoint_272`

- Concrete large-tree adversary (unconditional 256/272 bounds)
  We also define a specific large-tree memory `memBig` with:
  - huge `nNodes` and memory size,
  - odd-spaced initial indices (`bigIdx`),
  - zero tree values and zero input values.

  We prove `RoundDistinctNodes memBig 1` by constructing an injective
  `(round, lane)` → address map and a per‑address sensitivity witness. This
  yields a **formal, unconditional 256‑cycle lower bound** for the full machine
  ISA on that concrete adversarial memory:

  - `global_load_lower_bound_kernel_machine_big_256`
  - `global_load_lower_bound_kernel_machine_exists_big_256` (explicit ∃mem wrapper)

  We also combine tree‑node sensitivity with value‑slice sensitivity to show
  `BATCH_SIZE * (ROUNDS + 1)` distinct addresses must be read on `memBig`,
  giving a **formal, unconditional 272‑cycle lower bound**:

  - `global_load_lower_bound_machine_of_subset_card_272`
    (generic bridge: any finite set `s` with `s ⊆ readWordsMachine` and
    `s.card = BATCH_SIZE * (ROUNDS + 1)` yields the same 272 load bound)
  - `global_load_lower_bound_kernel_machine_big_272`
  - `global_load_lower_bound_kernel_machine_exists_big_272` (explicit ∃mem wrapper)
  - `global_cycle_lower_bound_kernel_machine_big_272`
  - `global_cycle_lower_bound_kernel_machine_exists_big_272` (explicit ∃mem wrapper)

  Engine-mix composition is now wired to the same generic subset-card bridge:
  - `global_engine_cycle_lower_bound_kernel_machine_of_subset_card`
  - `global_engine_cycle_lower_bound_kernel_machine_of_subset_card_272`
  - `global_engine_cycle_lower_bound_kernel_machine_adversaryList_values_disjoint_272`
  - `global_engine_cycle_lower_bound_kernel_machine_roundDistinct_values_disjoint_272`
  - `global_engine_cycle_lower_bound_kernel_machine_memBig_272`
  - `global_engine_cycle_lower_bound_kernel_machine_exists_memBig_272`

- Definition of “valid inputs”
  When this document says “global for all inputs,” it means:
  `MemSafeKernel mem ∧ KernelLayout mem ∧ KernelSensitive mem`.
  These predicates ensure the layout is well‑formed, memory is in‑bounds, and
  each output lane is actually sensitive to its corresponding input value.
  Theorems that quantify over “all inputs” are scoped to this class unless
  explicitly stated otherwise.

- End‑to‑end minimum lower bound (formal)
  We expose a single wrapper theorem over this “valid input” class:
  - `global_load_lower_bound_kernel_machine_final_valid`

  It implies the explicit numeric bound:
  - `global_load_lower_bound_kernel_machine_final_valid_16`

  For full ISA (PC‑bounded, fuel‑indexed) semantics, we also provide:

  - `global_load_lower_bound_kernel_machine_big_256_fuel`

- Strengthen PC-bounded control-flow predicates (`instrPcBoundedAt`) into a
  global program class and use it to refine the machine-trace proofs.
- Relax `KernelSensitive` by proving it from a concrete, global adversarial
  construction (or characterizing when it holds).
- Add a compute lower bound and take `max(load, compute)` for a stronger result.
