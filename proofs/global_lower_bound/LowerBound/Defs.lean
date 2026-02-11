import Mathlib
import proofs.common.Base
import proofs.common.Machine

namespace ProofGlobalLowerBound
open ProofCommon
open ProofMachine
open ProofISA

/--
Global lower-bound scaffold (Phase 1).

We keep the formal core arithmetic-only and leave semantic obligations as TODOs
in the accompanying markdown.
- `MIN_REQUIRED_WORDS` is a placeholder for the number of memory words that any
  correct program must read (to be proved via non-interference + adversarial
  input).
- The bounds below convert that word requirement into load-op and cycle lower
  bounds using ISA caps.
-/

def MIN_REQUIRED_WORDS : Nat := BATCH_SIZE
def MIN_REQUIRED_WORDS_KERNEL : Nat := BATCH_SIZE

/-! ## Program model (Phase 1 scaffold) -/

abbrev Memory : Type := Mem

/-! Output model (Phase 1): only the output values matter, fixed-size. -/
def Output : Type := Fin BATCH_SIZE → Nat

def PTR_INP_VAL : Nat := 6
def PTR_FOREST : Nat := 4
def PTR_INP_IDX : Nat := 5

def memAt (mem : Memory) (addr : Nat) : Nat :=
  mem.data addr

def outputOf (base : Nat) (mem : Memory) : Output :=
  fun i => memAt mem (base + i)

def outputAddrs (mem : Memory) : Finset Nat :=
  (Finset.univ.image (fun i : Fin BATCH_SIZE => memAt mem PTR_INP_VAL + i))

lemma outputAddrs_card (mem : Memory) : (outputAddrs mem).card = BATCH_SIZE := by
  classical
  have hinj : Function.Injective (fun i : Fin BATCH_SIZE => memAt mem PTR_INP_VAL + i) := by
    intro a b h
    apply Fin.ext
    exact Nat.add_left_cancel h
  simpa [outputAddrs] using
    (Finset.card_image_of_injective (s:=Finset.univ) hinj)

def AgreeOnList (xs : List Nat) (m1 m2 : Memory) : Prop :=
  m1.size = m2.size ∧
  ∀ a, a ∈ xs → memAt m1 a = memAt m2 a

def MemEqOn (xs : List Nat) (m1 m2 : Memory) : Prop :=
  ∀ a, a ∈ xs → memAt m1 a = memAt m2 a

@[simp] lemma memWriteMany_nil (m : Memory) : memWriteMany m [] = some m := by
  rfl

@[simp] lemma memWriteMany_cons (m : Memory) (w : Nat × Nat) (ws : List (Nat × Nat)) :
    memWriteMany m (w :: ws) =
      match memWrite m w.1 w.2 with
      | none => none
      | some m' => memWriteMany m' ws := by
  -- unfold foldl once and split on the first write
  cases h : memWrite m w.1 w.2 with
  | none =>
      -- foldl keeps none once acc is none
      have hnone :
          List.foldl
              (fun acc w =>
                match acc with
                | none => none
                | some m' => memWrite m' w.1 w.2)
              none ws = none := by
        induction ws with
        | nil => rfl
        | cons w' ws' ih => simp [List.foldl, ih]
      simpa [memWriteMany, h] using hnone
  | some m' =>
      simp [memWriteMany, h]

lemma memWrite_ok_eq (m1 m2 : Memory) (addr val : Nat) (hsize : m1.size = m2.size) :
    (memWrite m1 addr val).isSome = (memWrite m2 addr val).isSome := by
  by_cases h : addr < m1.size
  · have h' : addr < m2.size := by simpa [hsize] using h
    simp [memWrite, h, h']
  · have h' : ¬ addr < m2.size := by
      intro hlt
      exact h (by simpa [hsize] using hlt)
    simp [memWrite, h, h']

lemma memWrite_preserves_size (m m' : Memory) (addr val : Nat)
    (h : memWrite m addr val = some m') : m'.size = m.size := by
  by_cases hlt : addr < m.size
  · simp [memWrite, hlt] at h
    cases h
    rfl
  · simp [memWrite, hlt] at h

lemma memWrite_eq_of_ne (m m' : Memory) (addr val a : Nat)
    (h : memWrite m addr val = some m') (hne : a ≠ addr) :
    memAt m' a = memAt m a := by
  have hlt : addr < m.size := by
    by_cases hlt : addr < m.size
    · exact hlt
    · simp [memWrite, hlt] at h
  have hm :
      m' = { m with data := fun x => if x = addr then val else m.data x } := by
    simp [memWrite, hlt] at h
    cases h
    rfl
  simp [memAt, hm, hne]

lemma memWrite_eq_of_eq (m m' : Memory) (addr val : Nat)
    (h : memWrite m addr val = some m') :
    memAt m' addr = val := by
  have hlt : addr < m.size := by
    by_cases hlt : addr < m.size
    · exact hlt
    · simp [memWrite, hlt] at h
  have hm :
      m' = { m with data := fun x => if x = addr then val else m.data x } := by
    simp [memWrite, hlt] at h
    cases h
    rfl
  simp [memAt, hm]

lemma memWriteMany_ok_eq (m1 m2 : Memory) (ws : List (Nat × Nat)) (hsize : m1.size = m2.size) :
    (memWriteMany m1 ws).isSome = (memWriteMany m2 ws).isSome := by
  induction ws generalizing m1 m2 with
  | nil =>
      simp [memWriteMany]
  | cons w rest ih =>
      cases h1 : memWrite m1 w.1 w.2 with
      | none =>
          have h0 := memWrite_ok_eq m1 m2 w.1 w.2 hsize
          cases h2 : memWrite m2 w.1 w.2 with
          | none =>
              simp [memWriteMany_cons, h1, h2]
          | some m2' =>
              have : False := by
                have h0' := h0
                simp [h1, h2] at h0'
              cases this
      | some m1' =>
          cases h2 : memWrite m2 w.1 w.2 with
          | none =>
              have h0 := memWrite_ok_eq m1 m2 w.1 w.2 hsize
              have : False := by
                have h0' := h0
                simp [h1, h2] at h0'
              cases this
          | some m2' =>
              have hsize1 : m1'.size = m1.size :=
                memWrite_preserves_size m1 m1' w.1 w.2 h1
              have hsize2 : m2'.size = m2.size :=
                memWrite_preserves_size m2 m2' w.1 w.2 h2
              have hsize' : m1'.size = m2'.size := by
                simpa [hsize1, hsize2] using hsize
              simpa [memWriteMany_cons, h1, h2] using (ih (m1 := m1') (m2 := m2') hsize')

lemma memWriteMany_preserves_size (m m' : Memory) (ws : List (Nat × Nat))
    (h : memWriteMany m ws = some m') : m'.size = m.size := by
  induction ws generalizing m m' with
  | nil =>
      simp [memWriteMany] at h
      simp [h]
  | cons w rest ih =>
      cases h1 : memWrite m w.1 w.2 with
      | none =>
          -- memWriteMany returns none; contradiction
          simp [memWriteMany_cons, h1] at h
      | some m1 =>
          have h' : memWriteMany m1 rest = some m' := by
            simpa [memWriteMany_cons, h1] using h
          have hrest := ih (m := m1) (m' := m') h'
          have hsize1 : m1.size = m.size :=
            memWrite_preserves_size m m1 w.1 w.2 h1
          simpa [hsize1] using hrest

lemma memWriteMany_eq_of_not_written (m m' : Memory) (ws : List (Nat × Nat)) (a : Nat)
    (h : memWriteMany m ws = some m') (hnot : a ∉ ws.map Prod.fst) :
    memAt m' a = memAt m a := by
  induction ws generalizing m m' with
  | nil =>
      simp [memWriteMany] at h
      simp [h, memAt]
  | cons w rest ih =>
      cases h1 : memWrite m w.1 w.2 with
      | none =>
          simp [memWriteMany_cons, h1] at h
      | some m1 =>
          have h' : memWriteMany m1 rest = some m' := by
            simpa [memWriteMany_cons, h1] using h
          have hnot' : a ∉ rest.map Prod.fst := by
            intro hmem
            apply hnot
            simp [hmem]
          have hneq : a ≠ w.1 := by
            intro hEq
            apply hnot
            simp [hEq]
          have hrest := ih (m := m1) (m' := m') h' hnot'
          have hmemWrite : memAt m1 a = memAt m a :=
            memWrite_eq_of_ne m m1 w.1 w.2 a h1 hneq
          simpa [hmemWrite] using hrest

lemma memWriteMany_eq_on (m1 m2 m1' m2' : Memory) (ws : List (Nat × Nat))
    (h1 : memWriteMany m1 ws = some m1') (h2 : memWriteMany m2 ws = some m2') :
    MemEqOn (ws.map Prod.fst) m1' m2' := by
  induction ws generalizing m1 m2 m1' m2' with
  | nil =>
      intro a ha
      cases ha
  | cons w rest ih =>
      cases h1w : memWrite m1 w.1 w.2 with
      | none =>
          have : False := by
            have h1' := h1
            simp [memWriteMany_cons, h1w] at h1'
          cases this
      | some m1a =>
          cases h2w : memWrite m2 w.1 w.2 with
          | none =>
              have : False := by
                have h2' := h2
                simp [memWriteMany_cons, h2w] at h2'
              cases this
          | some m2a =>
              have h1' : memWriteMany m1a rest = some m1' := by
                simpa [memWriteMany_cons, h1w] using h1
              have h2' : memWriteMany m2a rest = some m2' := by
                simpa [memWriteMany_cons, h2w] using h2
              have ih' : MemEqOn (rest.map Prod.fst) m1' m2' := by
                exact ih (m1 := m1a) (m2 := m2a) (m1' := m1') (m2' := m2') h1' h2'
              intro a ha
              have ha' : a = w.1 ∨ a ∈ rest.map Prod.fst := by
                simpa using ha
              cases ha' with
              | inl hEq =>
                  by_cases hRest : a ∈ rest.map Prod.fst
                  · exact ih' a hRest
                  · subst hEq
                    have h1'' : memAt m1' w.1 = memAt m1a w.1 := by
                      have hnot : w.1 ∉ rest.map Prod.fst := by
                        exact hRest
                      exact memWriteMany_eq_of_not_written m1a m1' rest w.1 h1' hnot
                    have h2'' : memAt m2' w.1 = memAt m2a w.1 := by
                      have hnot : w.1 ∉ rest.map Prod.fst := by
                        exact hRest
                      exact memWriteMany_eq_of_not_written m2a m2' rest w.1 h2' hnot
                    have h1val : memAt m1a w.1 = w.2 :=
                      memWrite_eq_of_eq m1 m1a w.1 w.2 h1w
                    have h2val : memAt m2a w.1 = w.2 :=
                      memWrite_eq_of_eq m2 m2a w.1 w.2 h2w
                    calc
                      memAt m1' w.1 = memAt m1a w.1 := h1''
                      _ = w.2 := h1val
                      _ = memAt m2a w.1 := by
                        symm; exact h2val
                      _ = memAt m2' w.1 := by
                        symm; exact h2''
              | inr hRest =>
                  exact ih' a hRest

lemma agreeOnList_after_writes (xs : List Nat) (m1 m2 m1' m2' : Memory)
    (ws : List (Nat × Nat)) (hagree : AgreeOnList xs m1 m2)
    (h1 : memWriteMany m1 ws = some m1') (h2 : memWriteMany m2 ws = some m2') :
    AgreeOnList xs m1' m2' := by
  rcases hagree with ⟨hsize, hagree⟩
  refine ⟨?_, ?_⟩
  · -- sizes preserved by memWriteMany
    have hsz1 := memWriteMany_preserves_size m1 m1' ws h1
    have hsz2 := memWriteMany_preserves_size m2 m2' ws h2
    simpa [hsz1, hsz2] using hsize
  · intro a ha
    by_cases hmem : a ∈ ws.map Prod.fst
    · exact memWriteMany_eq_on m1 m2 m1' m2' ws h1 h2 a hmem
    · have h1' := memWriteMany_eq_of_not_written m1 m1' ws a h1 hmem
      have h2' := memWriteMany_eq_of_not_written m2 m2' ws a h2 hmem
      exact by simpa [h1', h2'] using hagree a ha

def listJoin {α : Type} (xs : List (List α)) : List α :=
  xs.flatMap (fun x => x)

lemma listJoin_append {α : Type} (xs ys : List (List α)) :
    listJoin (xs ++ ys) = listJoin xs ++ listJoin ys := by
  simp [listJoin, List.flatMap_append]

lemma map_fst_flatMap_execStoreSlot_eq_listJoin (slots : List StoreSlot) (s : Nat → Nat) :
    (slots.flatMap (execStoreSlot s)).map Prod.fst =
      listJoin ((slots.map (execStoreSlot s)).map (fun ws => ws.map Prod.fst)) := by
  induction slots with
  | nil =>
      simp [listJoin]
  | cons slot rest ih =>
      -- Expand both sides on the head store-slot and apply IH to the tail.
      simp [listJoin, List.flatMap, ih, List.map_append]
      -- Remaining goal is only about a redundant `id` in the mapped function.
      have hmap :
          List.map ((fun x => x) ∘ (fun ws => List.map Prod.fst ws) ∘ execStoreSlot s) rest =
            List.map (List.map Prod.fst ∘ execStoreSlot s) rest := by
        apply List.map_congr_left
        intro a _ha
        rfl
      simpa [hmap]

/-! ### Load-op arithmetic helpers -/

def minLoadOps (words : Nat) : Nat := ceilDiv words VLEN

structure Program where
  program : List Instruction
  /-- Initial scratch contents. -/
  initScratch : Nat → Nat := fun _ => 0

/-! ### Straight-line program predicate -/

def flowSlotStraight : FlowSlot → Prop
  | .select _ _ _ _ => True
  | .add_imm _ _ _ => True
  | .vselect _ _ _ _ => True
  | .trace_write _ => True
  | .coreid _ => True
  | .halt => False
  | .pause => False
  | .cond_jump _ _ => False
  | .cond_jump_rel _ _ => False
  | .jump _ => False
  | .jump_indirect _ => False

def instrStraight (i : Instruction) : Prop :=
  List.Forall flowSlotStraight i.flow

def StraightLine (p : Program) : Prop :=
  ∀ instr ∈ p.program, instrStraight instr

def PcBoundedProgram (p : Program) : Prop :=
  ∀ i instr, listGet? p.program i = some instr →
    instrPcBoundedAt p.program.length i instr

def ProgramClass (p : Program) : Prop :=
  (∀ i instr, listGet? p.program i = some instr → instrScratchBounded instr) ∧
  PcBoundedProgram p

def initCore (p : Program) : Core :=
  { id := 0, scratch := p.initScratch, trace_buf := [], pc := 0, state := .running }

def initMachine (p : Program) (mem : Memory) : Machine :=
  { cores := [initCore p],
    mem := mem,
    program := p.program,
    cycle := 0,
    enable_pause := false,
    enable_debug := false,
    value_trace := fun _ => 0,
    aborted := false }

def loadAddrs (s : Nat → Nat) (slot : LoadSlot) : List Nat :=
  match slot with
  | .load _ addr => [s addr]
  | .load_offset _ addr offset => [s (addr + offset)]
  | .vload _ addr =>
      let base := s addr
      (List.range VLEN).map (fun i => base + i)
  | .const _ _ => []

def storeAddrs (s : Nat → Nat) (slot : StoreSlot) : List Nat :=
  match slot with
  | .store addr _ => [s addr]
  | .vstore addr _ =>
      let base := s addr
      (List.range VLEN).map (fun i => base + i)

def storeWrites (s : Nat → Nat) (slot : StoreSlot) : List (Nat × Nat) :=
  execStoreSlot s slot

def storeWriteAddrs (s : Nat → Nat) (slot : StoreSlot) : List Nat :=
  (storeWrites s slot).map Prod.fst

noncomputable def execInstructionTrace (mem : Memory) (core : Core) (instr : Instruction) :
    ExecResult × List (List Nat) :=
  let reads := instr.load.map (loadAddrs core.scratch)
  let res := execInstruction false false (fun _ => 0) mem core instr
  (res, reads)

noncomputable def execInstructionTraceMachine (m : Machine) (mem : Memory) (core : Core)
    (instr : Instruction) : ExecResult × List (List Nat) :=
  let reads := instr.load.map (loadAddrs core.scratch)
  let res := execInstruction m.enable_pause m.enable_debug m.value_trace mem core instr
  (res, reads)

noncomputable def runTraceAux : List Instruction → Memory → Core → (Memory × List (List Nat))
  | [], mem, _ => (mem, [])
  | instr :: rest, mem, core =>
      let (res, reads) := execInstructionTrace mem core instr
      if res.ok then
        let (mem', reads') := runTraceAux rest res.mem res.core
        (mem', reads ++ reads')
      else
        (res.mem, reads)

noncomputable def runTraceAuxRW : List Instruction → Memory → Core →
    (Memory × List (List Nat) × List (List (Nat × Nat)))
  | [], mem, _ => (mem, [], [])
  | instr :: rest, mem, core =>
      let writes := instr.store.map (storeWrites core.scratch)
      let (res, reads) := execInstructionTrace mem core instr
      if res.ok then
        let (mem', reads', writes') := runTraceAuxRW rest res.mem res.core
        (mem', reads ++ reads', writes ++ writes')
      else
        (res.mem, reads, writes)

noncomputable def runTrace (p : Program) (mem : Memory) : Memory × List (List Nat) :=
  runTraceAux p.program mem (initCore p)

def SafeExecAux : List Instruction → Memory → Core → Prop
  | [], _, _ => True
  | instr :: rest, mem, core =>
      let (res, _) := execInstructionTrace mem core instr
      res.ok = true ∧ SafeExecAux rest res.mem res.core

def SafeExec (p : Program) (mem : Memory) : Prop :=
  SafeExecAux p.program mem (initCore p)

def anyRunning (m : Machine) : Bool :=
  m.cores.any (fun c => c.state = .running)

noncomputable def stepCoreTrace (m : Machine) (core : Core) :
    Core × Memory × Bool × Bool × List (List Nat) :=
  match core.state with
  | .running =>
      match fetch m.program core.pc with
      | none =>
          ({ core with state := .stopped }, m.mem, false, true, [])
      | some instr =>
          let core1 := { core with pc := core.pc + 1 }
          let (res, reads) := execInstructionTraceMachine m m.mem core1 instr
          let core2 := if res.ok then res.core else { core1 with state := .stopped }
          (core2, res.mem, res.has_non_debug, res.ok, reads)
  | _ =>
      (core, m.mem, false, true, [])

noncomputable def stepCoreTraceReads (m : Machine) (core : Core) : List (List Nat) :=
  (stepCoreTrace m core).2.2.2.2

noncomputable def stepMachineTrace (m : Machine) : Machine × List (List Nat) :=
  if m.aborted then
    (m, [])
  else
    let (cores', mem', anyExec, okAll, reads) :=
      m.cores.foldl
        (fun acc core =>
          let (cs, mem0, flag, ok, rs) := acc
          let (core', mem1, did, ok', rs') := stepCoreTrace { m with mem := mem0 } core
          (cs ++ [core'], mem1, flag || did, ok && ok', rs ++ rs'))
        ([], m.mem, false, true, [])
    if !okAll then
      let cores'' := cores'.map (fun c => { c with state := .stopped })
      ({ m with cores := cores'', mem := mem', aborted := true }, reads)
    else
      let cycle' := if anyExec then m.cycle + 1 else m.cycle
      ({ m with cores := cores', mem := mem', cycle := cycle' }, reads)

noncomputable def runMachineTraceAux : Nat → Machine → (Memory × List (List Nat))
  | 0, m => (m.mem, [])
  | fuel+1, m =>
      if !anyRunning m then
        (m.mem, [])
      else
        let (m', reads) := stepMachineTrace m
        let (mem', reads') := runMachineTraceAux fuel m'
        (mem', reads ++ reads')

/-!
### A "full" runner that preserves the final `Machine` state (including `cycle`)

`runMachineTraceAux` returns only the final memory and the collected read-trace.
For cycle lower bounds we also need access to `Machine.cycle`, so we keep the
final machine here.
-/
noncomputable def runMachineTraceAuxFull : Nat → Machine → (Machine × List (List Nat))
  | 0, m => (m, [])
  | fuel+1, m =>
      if !anyRunning m then
        (m, [])
      else
        let (m', reads) := stepMachineTrace m
        let (mfin, reads') := runMachineTraceAuxFull fuel m'
        (mfin, reads ++ reads')

noncomputable def runMachineFinalFuel (p : Program) (fuel : Nat) (mem : Memory) : Machine :=
  (runMachineTraceAuxFull fuel (initMachine p mem)).1

noncomputable def cycleCountMachineFuel (p : Program) (fuel : Nat) (mem : Memory) : Nat :=
  (runMachineFinalFuel p fuel mem).cycle

noncomputable def cycleCountMachine (p : Program) (mem : Memory) : Nat :=
  cycleCountMachineFuel p p.program.length mem

noncomputable def runMachineTraceFuel (p : Program) (fuel : Nat) (mem : Memory) :
    Memory × List (List Nat) :=
  runMachineTraceAux fuel (initMachine p mem)

noncomputable def runMachineTrace (p : Program) (mem : Memory) : Memory × List (List Nat) :=
  runMachineTraceFuel p p.program.length mem

noncomputable def runMemMachine (p : Program) (mem : Memory) : Memory :=
  (runMachineTrace p mem).1

noncomputable def readOpsMachine (p : Program) (mem : Memory) : List (List Nat) :=
  (runMachineTrace p mem).2

noncomputable def readWordsMachine (p : Program) (mem : Memory) : List Nat :=
  listJoin (readOpsMachine p mem)

noncomputable def readWordCountMachine (p : Program) (mem : Memory) : Nat :=
  (readWordsMachine p mem).length

noncomputable def loadOpCountMachine (p : Program) (mem : Memory) : Nat :=
  (readOpsMachine p mem).length

noncomputable def runMemMachineFuel (p : Program) (fuel : Nat) (mem : Memory) : Memory :=
  (runMachineTraceFuel p fuel mem).1

noncomputable def readOpsMachineFuel (p : Program) (fuel : Nat) (mem : Memory) :
    List (List Nat) :=
  (runMachineTraceFuel p fuel mem).2

noncomputable def readWordsMachineFuel (p : Program) (fuel : Nat) (mem : Memory) : List Nat :=
  listJoin (readOpsMachineFuel p fuel mem)

noncomputable def readWordCountMachineFuel (p : Program) (fuel : Nat) (mem : Memory) : Nat :=
  (readWordsMachineFuel p fuel mem).length

noncomputable def loadOpCountMachineFuel (p : Program) (fuel : Nat) (mem : Memory) : Nat :=
  (readOpsMachineFuel p fuel mem).length

noncomputable def runMem (p : Program) (mem : Memory) : Memory :=
  (runTrace p mem).1

noncomputable def readOps (p : Program) (mem : Memory) : List (List Nat) :=
  (runTrace p mem).2

noncomputable def readWords (p : Program) (mem : Memory) : List Nat :=
  listJoin (readOps p mem)

noncomputable def writeOps (p : Program) (mem : Memory) : List (List (Nat × Nat)) :=
  (runTraceAuxRW p.program mem (initCore p)).2.2

noncomputable def writeWords (p : Program) (mem : Memory) : List Nat :=
  listJoin (writeOps p mem |>.map (fun ws => ws.map Prod.fst))

noncomputable def writePairs (p : Program) (mem : Memory) : List (Nat × Nat) :=
  listJoin (writeOps p mem)

def WritesOutput (p : Program) (mem : Memory) : Prop :=
  outputAddrs mem ⊆ (writeWords p mem).toFinset

lemma runTraceAuxRW_fst_eq (prog : List Instruction) (mem : Memory) (core : Core) :
    (runTraceAuxRW prog mem core).1 = (runTraceAux prog mem core).1 := by
  induction prog generalizing mem core with
  | nil =>
      simp [runTraceAuxRW, runTraceAux]
  | cons instr rest ih =>
      by_cases hok : (execInstructionTrace mem core instr).1.ok
      · simp [runTraceAuxRW, runTraceAux, hok, ih]
      · simp [runTraceAuxRW, runTraceAux, hok]

lemma execInstructionTrace_mem_eq_of_not_written (mem : Memory) (core : Core) (instr : Instruction)
    (addr : Nat)
    (hnot : addr ∉ listJoin (instr.store.map (storeWriteAddrs core.scratch))) :
    memAt (execInstructionTrace mem core instr).1.mem addr = memAt mem addr := by
  unfold execInstructionTrace
  -- not-written for flatMap store_writes
  have hnot' :
      addr ∉ (instr.store.flatMap (execStoreSlot core.scratch)).map Prod.fst := by
    intro hmem
    apply hnot
    rcases List.mem_map.1 hmem with ⟨w, hw, hwaddr⟩
    rcases List.mem_flatMap.1 hw with ⟨slot, hslot, hwslot⟩
    apply List.mem_flatMap.2
    refine ⟨storeWriteAddrs core.scratch slot, ?_, ?_⟩
    · exact List.mem_map.2 ⟨slot, hslot, rfl⟩
    · exact List.mem_map.2 ⟨w, hwslot, by simpa using hwaddr⟩
  by_cases hWF : instrWellFormed instr
  · cases hvalu : execValuSlots core.scratch instr.valu with
    | none =>
        simp [execInstruction, hWF, hvalu]
    | some valu_writes =>
        cases halu : execAluSlots core.scratch instr.alu with
        | none =>
            simp [execInstruction, hWF, hvalu, halu]
        | some alu_writes =>
            let store_writes := instr.store.flatMap (execStoreSlot core.scratch)
            let flow_pair :=
              instr.flow.foldl
                (fun acc slot =>
                  let (c, ws) := acc
                  let (c', ws') := execFlowSlot false c core.scratch slot
                  (c', ws ++ ws'))
                (core, [])
            let ok_false : ExecResult :=
              { core := core, mem := mem, ok := false, debug_ok := true,
                has_non_debug := instrHasNonDebug instr }
            let ok_true (load_writes : List (Nat × Nat)) (mem' : Mem) : ExecResult :=
              let scratch' :=
                writeMany core.scratch (valu_writes ++ alu_writes ++ flow_pair.2 ++ load_writes)
              let core' := { flow_pair.1 with scratch := scratch' }
              { core := core', mem := mem', ok := true, debug_ok := true,
                has_non_debug := instrHasNonDebug instr }
            let load_writes? :=
              instr.load.foldl
                (fun acc slot =>
                  match acc, execLoadSlot core.scratch mem slot with
                  | some ws, some ws' => some (ws ++ ws')
                  | _, _ => none)
                (some [])
            have hload_def :
                load_writes? =
                  instr.load.foldl
                    (fun acc slot =>
                      match acc, execLoadSlot core.scratch mem slot with
                      | some ws, some ws' => some (ws ++ ws')
                      | _, _ => none)
                    (some []) := rfl
            cases hload_eq : load_writes? with
            | none =>
                have hload_eq' :
                    instr.load.foldl
                        (fun acc slot =>
                          match acc, execLoadSlot core.scratch mem slot with
                          | some ws, some ws' => some (ws ++ ws')
                          | _, _ => none)
                        (some []) =
                      none := by
                  simpa [hload_def] using hload_eq
                have hmatch :
                    (match
                        instr.load.foldl
                          (fun acc slot =>
                            match acc, execLoadSlot core.scratch mem slot with
                            | some ws, some ws' => some (ws ++ ws')
                            | _, _ => none)
                          (some []) with
                      | none => ok_false
                      | some load_writes =>
                        match memWriteMany mem store_writes with
                        | none => ok_false
                        | some mem' => ok_true load_writes mem') = ok_false := by
                  simp [hload_eq', ok_false]
                have hres :
                    execInstruction false false (fun _ => 0) mem core instr = ok_false := by
                  unfold execInstruction
                  simp [hWF, hvalu, halu]
                  simpa [ok_false, ok_true, store_writes, flow_pair] using hmatch
                simp [hres, ok_false]
            | some load_writes =>
                have hload_eq' :
                    instr.load.foldl
                        (fun acc slot =>
                          match acc, execLoadSlot core.scratch mem slot with
                          | some ws, some ws' => some (ws ++ ws')
                          | _, _ => none)
                        (some []) =
                      some load_writes := by
                  simpa [hload_def] using hload_eq
                have hnot'' : addr ∉ store_writes.map Prod.fst := by
                  simpa [store_writes] using hnot'
                cases hmw : memWriteMany mem store_writes with
                | none =>
                    have hmatch :
                        (match
                            instr.load.foldl
                              (fun acc slot =>
                                match acc, execLoadSlot core.scratch mem slot with
                                | some ws, some ws' => some (ws ++ ws')
                                | _, _ => none)
                              (some []) with
                          | none => ok_false
                          | some load_writes =>
                            match memWriteMany mem store_writes with
                            | none => ok_false
                            | some mem' => ok_true load_writes mem') = ok_false := by
                      simp [hload_eq', hmw, ok_false]
                    have hres :
                        execInstruction false false (fun _ => 0) mem core instr = ok_false := by
                      unfold execInstruction
                      simp [hWF, hvalu, halu]
                      simpa [ok_false, ok_true, store_writes, flow_pair] using hmatch
                    simp [hres, ok_false]
                | some mem' =>
                    have hmem : memAt mem' addr = memAt mem addr :=
                      memWriteMany_eq_of_not_written mem mem' store_writes addr hmw hnot''
                    have hmatch :
                        (match
                            instr.load.foldl
                              (fun acc slot =>
                                match acc, execLoadSlot core.scratch mem slot with
                                | some ws, some ws' => some (ws ++ ws')
                                | _, _ => none)
                              (some []) with
                          | none => ok_false
                          | some load_writes =>
                            match memWriteMany mem store_writes with
                            | none => ok_false
                            | some mem'' => ok_true load_writes mem'') =
                          ok_true load_writes mem' := by
                      simp [hload_eq', hmw, ok_true]
                    have hres :
                        execInstruction false false (fun _ => 0) mem core instr =
                          ok_true load_writes mem' := by
                      unfold execInstruction
                      simp [hWF, hvalu, halu, ok_true, flow_pair]
                      simpa [ok_false, ok_true, store_writes, flow_pair] using hmatch
                    simpa [execInstructionTrace, hres] using hmem
  ·
    have hdec : decide (instrWellFormed instr) = false := by
      exact (decide_eq_false_iff_not).2 hWF
    -- In the ill-formed case, execInstruction bails out before touching mem.
    simp [execInstruction, hdec]

lemma execInstructionTrace_memWriteMany_of_ok (mem : Memory) (core : Core) (instr : Instruction)
    (hok : (execInstructionTrace mem core instr).1.ok = true) :
    memWriteMany mem (instr.store.flatMap (execStoreSlot core.scratch)) =
      some (execInstructionTrace mem core instr).1.mem := by
  unfold execInstructionTrace at hok ⊢
  by_cases hWF : instrWellFormed instr
  · cases hvalu : execValuSlots core.scratch instr.valu with
    | none =>
        have hk : (false : Bool) = true := by
          simpa [execInstruction, hWF, hvalu] using hok
        cases hk
    | some valu_writes =>
        cases halu : execAluSlots core.scratch instr.alu with
        | none =>
            have hk : (false : Bool) = true := by
              simpa [execInstruction, hWF, hvalu, halu] using hok
            cases hk
        | some alu_writes =>
            -- Mirror the branching structure in `execInstruction` and discharge impossible branches
            -- using the `ok = true` hypothesis.
            let store_writes := instr.store.flatMap (execStoreSlot core.scratch)
            let flow_pair :=
              instr.flow.foldl
                (fun acc slot =>
                  let (c, ws) := acc
                  let (c', ws') := execFlowSlot false c core.scratch slot
                  (c', ws ++ ws'))
                (core, [])
            let ok_false : ExecResult :=
              { core := core, mem := mem, ok := false, debug_ok := true,
                has_non_debug := instrHasNonDebug instr }
            let ok_true (load_writes : List (Nat × Nat)) (mem' : Mem) : ExecResult :=
              let scratch' :=
                writeMany core.scratch (valu_writes ++ alu_writes ++ flow_pair.2 ++ load_writes)
              let core' := { flow_pair.1 with scratch := scratch' }
              { core := core', mem := mem', ok := true, debug_ok := true,
                has_non_debug := instrHasNonDebug instr }
            let load_writes? :=
              instr.load.foldl
                (fun acc slot =>
                  match acc, execLoadSlot core.scratch mem slot with
                  | some ws, some ws' => some (ws ++ ws')
                  | _, _ => none)
                (some [])
            have hload_def :
                load_writes? =
                  instr.load.foldl
                    (fun acc slot =>
                      match acc, execLoadSlot core.scratch mem slot with
                      | some ws, some ws' => some (ws ++ ws')
                      | _, _ => none)
                    (some []) := rfl
            cases hload_eq : load_writes? with
            | none =>
                have hload_eq' :
                    instr.load.foldl
                        (fun acc slot =>
                          match acc, execLoadSlot core.scratch mem slot with
                          | some ws, some ws' => some (ws ++ ws')
                          | _, _ => none)
                        (some []) =
                      none := by
                  simpa [hload_def] using hload_eq
                have hmatch :
                    (match
                        instr.load.foldl
                          (fun acc slot =>
                            match acc, execLoadSlot core.scratch mem slot with
                            | some ws, some ws' => some (ws ++ ws')
                            | _, _ => none)
                          (some []) with
                      | none => ok_false
                      | some load_writes =>
                        match memWriteMany mem store_writes with
                        | none => ok_false
                        | some mem' => ok_true load_writes mem') = ok_false := by
                  simp [hload_eq', ok_false]
                have hres :
                    execInstruction false false (fun _ => 0) mem core instr = ok_false := by
                  unfold execInstruction
                  simp [hWF, hvalu, halu]
                  simpa [ok_false, ok_true, store_writes, flow_pair] using hmatch
                have hk : (false : Bool) = true := by
                  simpa [hres, ok_false] using hok
                cases hk
            | some load_writes =>
                have hload_eq' :
                    instr.load.foldl
                        (fun acc slot =>
                          match acc, execLoadSlot core.scratch mem slot with
                          | some ws, some ws' => some (ws ++ ws')
                          | _, _ => none)
                        (some []) =
                      some load_writes := by
                  simpa [hload_def] using hload_eq
                cases hmw : memWriteMany mem store_writes with
                | none =>
                    have hmatch :
                        (match
                            instr.load.foldl
                              (fun acc slot =>
                                match acc, execLoadSlot core.scratch mem slot with
                                | some ws, some ws' => some (ws ++ ws')
                                | _, _ => none)
                              (some []) with
                          | none => ok_false
                          | some load_writes =>
                            match memWriteMany mem store_writes with
                            | none => ok_false
                            | some mem' => ok_true load_writes mem') = ok_false := by
                      simp [hload_eq', hmw, ok_false]
                    have hres :
                        execInstruction false false (fun _ => 0) mem core instr = ok_false := by
                      unfold execInstruction
                      simp [hWF, hvalu, halu]
                      simpa [ok_false, ok_true, store_writes, flow_pair] using hmatch
                    have hk : (false : Bool) = true := by
                      simpa [hres, ok_false] using hok
                    cases hk
                | some mem' =>
                    have hmatch :
                        (match
                            instr.load.foldl
                              (fun acc slot =>
                                match acc, execLoadSlot core.scratch mem slot with
                                | some ws, some ws' => some (ws ++ ws')
                                | _, _ => none)
                              (some []) with
                          | none => ok_false
                          | some load_writes =>
                            match memWriteMany mem store_writes with
                            | none => ok_false
                            | some mem'' => ok_true load_writes mem'') =
                          ok_true load_writes mem' := by
                      simp [hload_eq', hmw, ok_true]
                    have hres :
                        execInstruction false false (fun _ => 0) mem core instr =
                          ok_true load_writes mem' := by
                      unfold execInstruction
                      simp [hWF, hvalu, halu, ok_true, flow_pair]
                      simpa [ok_false, ok_true, store_writes, flow_pair] using hmatch
                    -- `execInstruction.mem` is exactly the `memWriteMany` result in the ok=true branch.
                    simpa [store_writes, hres, ok_true] using hmw
  · have hk : (false : Bool) = true := by
      simpa [execInstruction, hWF] using hok
    cases hk

lemma runTraceAuxRW_eq_of_not_written :
    ∀ prog mem core addr,
      addr ∉ listJoin ((runTraceAuxRW prog mem core).2.2.map (fun ws => ws.map Prod.fst)) →
      memAt (runTraceAuxRW prog mem core).1 addr = memAt mem addr := by
  intro prog
  induction prog with
  | nil =>
      intro mem core addr hnot
      simp [runTraceAuxRW] at hnot
      simp [runTraceAuxRW]
  | cons instr rest ih =>
      intro mem core addr hnot
      by_cases hok : (execInstructionTrace mem core instr).1.ok
      · -- ok branch: split not-written across current and rest writes
        have hnot' := hnot
        simp [runTraceAuxRW, hok] at hnot'
        -- current writes list
        have hnot_writes :
            addr ∉ listJoin ((instr.store.map (storeWrites core.scratch)).map (fun ws => ws.map Prod.fst)) := by
          intro hmem
          apply hnot'
          have :
              addr ∈
                listJoin ((instr.store.map (storeWrites core.scratch)).map (fun ws => ws.map Prod.fst)) ++
                  listJoin (((runTraceAuxRW rest (execInstructionTrace mem core instr).1.mem
                      (execInstructionTrace mem core instr).1.core).2.2).map (fun ws => ws.map Prod.fst)) := by
            exact List.mem_append.mpr (Or.inl hmem)
          simpa [List.map_append, listJoin_append] using this
        have hnot_rest :
            addr ∉
              listJoin (((runTraceAuxRW rest (execInstructionTrace mem core instr).1.mem
                (execInstructionTrace mem core instr).1.core).2.2).map (fun ws => ws.map Prod.fst)) := by
          intro hmem
          apply hnot'
          have :
              addr ∈
                listJoin ((instr.store.map (storeWrites core.scratch)).map (fun ws => ws.map Prod.fst)) ++
                  listJoin (((runTraceAuxRW rest (execInstructionTrace mem core instr).1.mem
                      (execInstructionTrace mem core instr).1.core).2.2).map (fun ws => ws.map Prod.fst)) := by
            exact List.mem_append.mpr (Or.inr hmem)
          simpa [List.map_append, listJoin_append] using this
        have hmem0 :
            memAt (execInstructionTrace mem core instr).1.mem addr = memAt mem addr := by
          -- align to storeWriteAddrs
          have hnot_sw :
              addr ∉ listJoin (instr.store.map (storeWriteAddrs core.scratch)) := by
            simpa [storeWriteAddrs, storeWrites] using hnot_writes
          exact execInstructionTrace_mem_eq_of_not_written mem core instr addr hnot_sw
        have hmem1 :
            memAt
                (runTraceAuxRW rest (execInstructionTrace mem core instr).1.mem
                  (execInstructionTrace mem core instr).1.core).1 addr =
              memAt (execInstructionTrace mem core instr).1.mem addr :=
          ih _ _ _ hnot_rest
        calc
          memAt (runTraceAuxRW (instr :: rest) mem core).1 addr
              = memAt
                  (runTraceAuxRW rest (execInstructionTrace mem core instr).1.mem
                    (execInstructionTrace mem core instr).1.core).1 addr := by
                  simp [runTraceAuxRW, hok]
          _ = memAt (execInstructionTrace mem core instr).1.mem addr := hmem1
          _ = memAt mem addr := hmem0
      · -- not ok: only current writes matter
        have hnot' := hnot
        simp [runTraceAuxRW, hok] at hnot'
        have hnot_sw :
            addr ∉ listJoin (instr.store.map (storeWriteAddrs core.scratch)) := by
          simpa [storeWriteAddrs, storeWrites] using hnot'
        have hmem0 := execInstructionTrace_mem_eq_of_not_written mem core instr addr hnot_sw
        simpa [runTraceAuxRW, hok] using hmem0

lemma runMem_eq_of_not_written (p : Program) (mem : Memory) (addr : Nat)
    (hnot : addr ∉ writeWords p mem) :
    memAt (runMem p mem) addr = memAt mem addr := by
  -- rewrite in terms of runTraceAuxRW and apply non-interference lemma
  have hnot' :
      addr ∉
        listJoin
          ((runTraceAuxRW p.program mem (initCore p)).2.2.map (fun ws => ws.map Prod.fst)) := by
    simpa [writeWords, writeOps] using hnot
  have hmem :=
    runTraceAuxRW_eq_of_not_written p.program mem (initCore p) addr hnot'
  -- relate runTraceAuxRW and runTraceAux outputs
  have hfst := runTraceAuxRW_fst_eq p.program mem (initCore p)
  -- runMem uses runTraceAux
  simpa [runMem, runTrace, hfst] using hmem

noncomputable def run (p : Program) (mem : Memory) : Output :=
  outputOf (memAt mem PTR_INP_VAL) (runMem p mem)

noncomputable def runMachine (p : Program) (mem : Memory) : Output :=
  outputOf (memAt mem PTR_INP_VAL) (runMemMachine p mem)

noncomputable def runMachineFuel (p : Program) (fuel : Nat) (mem : Memory) : Output :=
  outputOf (memAt mem PTR_INP_VAL) (runMemMachineFuel p fuel mem)

def CorrectOn (spec : Memory → Output) (p : Program) (memOk : Memory → Prop) : Prop :=
  ∀ mem, memOk mem → run p mem = spec mem

def CorrectOnMachine (spec : Memory → Output) (p : Program) (memOk : Memory → Prop) : Prop :=
  ∀ mem, memOk mem → runMachine p mem = spec mem

def CorrectOnMachineFuel (spec : Memory → Output) (p : Program) (memOk : Memory → Prop)
    (fuel : Nat) : Prop :=
  ∀ mem, memOk mem → runMachineFuel p fuel mem = spec mem

def Correct (spec : Memory → Output) (p : Program) : Prop :=
  CorrectOn spec p (fun _ => True)

noncomputable def readWordCount (p : Program) (mem : Memory) : Nat :=
  (readWords p mem).length

noncomputable def loadOpCount (p : Program) (mem : Memory) : Nat :=
  (readOps p mem).length

def HEADER_SIZE : Nat := 7
def FOREST_BASE : Nat := HEADER_SIZE
def IDX_BASE : Nat := FOREST_BASE + N_NODES
def VAL_BASE : Nat := IDX_BASE + BATCH_SIZE
def EXTRA_ROOM : Nat := N_NODES + 2 * BATCH_SIZE + VLEN * 2 + 32
def EXTRA_ROOM_BASE : Nat := VAL_BASE + BATCH_SIZE
def MEM_SIZE : Nat := EXTRA_ROOM_BASE + EXTRA_ROOM

def MemSafeValues (mem : Memory) : Prop :=
  memAt mem PTR_INP_VAL + BATCH_SIZE ≤ mem.size

def ValuesLayout (mem : Memory) : Prop :=
  HEADER_SIZE ≤ memAt mem PTR_INP_VAL

lemma ptr_inp_val_ne_input_addr {mem : Memory} (h : ValuesLayout mem) (i : Fin BATCH_SIZE) :
    memAt mem PTR_INP_VAL + i ≠ PTR_INP_VAL := by
  have hge : HEADER_SIZE ≤ memAt mem PTR_INP_VAL := h
  have hgt : PTR_INP_VAL < memAt mem PTR_INP_VAL := by
    -- PTR_INP_VAL = 6, HEADER_SIZE = 7
    have h6 : PTR_INP_VAL < HEADER_SIZE := by decide
    exact lt_of_lt_of_le h6 hge
  intro hEq
  -- addr = base + i ≥ base, contradict base > PTR_INP_VAL
  have hle : memAt mem PTR_INP_VAL ≤ memAt mem PTR_INP_VAL + i := by
    exact Nat.le_add_right _ _
  have hle' : memAt mem PTR_INP_VAL ≤ PTR_INP_VAL := by
    simpa [hEq] using hle
  exact (not_le_of_gt hgt) hle'

def MemSafeKernel (mem : Memory) : Prop :=
  7 < mem.size ∧
  memAt mem 2 = BATCH_SIZE ∧
  let nNodes := memAt mem 1
  let forestPtr := memAt mem PTR_FOREST
  let idxPtr := memAt mem PTR_INP_IDX
  let valPtr := memAt mem PTR_INP_VAL
  forestPtr + nNodes ≤ mem.size ∧
  idxPtr + BATCH_SIZE ≤ mem.size ∧
  valPtr + BATCH_SIZE ≤ mem.size

def KernelLayout (mem : Memory) : Prop :=
  let forestPtr := memAt mem PTR_FOREST
  let idxPtr := memAt mem PTR_INP_IDX
  let valPtr := memAt mem PTR_INP_VAL
  HEADER_SIZE ≤ forestPtr ∧
  HEADER_SIZE ≤ idxPtr ∧
  HEADER_SIZE ≤ valPtr

lemma valuesLayout_of_kernelLayout (mem : Memory) (hlayout : KernelLayout mem) : ValuesLayout mem := by
  dsimp [KernelLayout, ValuesLayout] at hlayout ⊢
  exact hlayout.2.2

def KernelDisjoint (mem : Memory) : Prop :=
  let nNodes := memAt mem 1
  let forestPtr := memAt mem PTR_FOREST
  let idxPtr := memAt mem PTR_INP_IDX
  let valPtr := memAt mem PTR_INP_VAL
  forestPtr + nNodes ≤ idxPtr ∧
  idxPtr + BATCH_SIZE ≤ valPtr

def AddrSafe (mem : Memory) (addr : Nat) : Prop :=
  HEADER_SIZE ≤ addr ∧ addr < mem.size

lemma memSafeValues_of_eq_ptr (mem mem' : Memory)
    (hsize : mem.size = mem'.size)
    (hptr : memAt mem PTR_INP_VAL = memAt mem' PTR_INP_VAL)
    (hsafe : MemSafeValues mem) : MemSafeValues mem' := by
  dsimp [MemSafeValues] at hsafe
  dsimp [MemSafeValues]
  simpa [hsize, hptr] using hsafe

lemma memSafeKernel_of_eq_header (mem mem' : Memory)
    (hsize : mem.size = mem'.size)
    (h1 : memAt mem 1 = memAt mem' 1)
    (h2 : memAt mem 2 = memAt mem' 2)
    (hforest : memAt mem PTR_FOREST = memAt mem' PTR_FOREST)
    (hidx : memAt mem PTR_INP_IDX = memAt mem' PTR_INP_IDX)
    (hval : memAt mem PTR_INP_VAL = memAt mem' PTR_INP_VAL)
    (hsafe : MemSafeKernel mem) : MemSafeKernel mem' := by
  dsimp [MemSafeKernel] at hsafe
  rcases hsafe with ⟨hsize7, hbatch, hrest⟩
  refine ⟨?_, ?_, ?_⟩
  · simpa [hsize] using hsize7
  · simpa [h2] using hbatch
  · -- rewrite header-derived lets
    simpa [MemSafeKernel, hsize, h1, h2, hforest, hidx, hval] using hrest


end ProofGlobalLowerBound
