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
                simpa [h1, h2] using h0
              cases this
      | some m1' =>
          cases h2 : memWrite m2 w.1 w.2 with
          | none =>
              have h0 := memWrite_ok_eq m1 m2 w.1 w.2 hsize
              have : False := by
                simpa [h1, h2] using h0
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
      simpa [h] using rfl
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
            simpa [memWriteMany_cons, h1w] using h1
          cases this
      | some m1a =>
          cases h2w : memWrite m2 w.1 w.2 with
          | none =>
              have : False := by
                simpa [memWriteMany_cons, h2w] using h2
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
  -- If instrWellFormed fails, mem is unchanged.
  by_cases hform : decide (instrWellFormed instr) = true
  · -- execValuSlots/execAluSlots might fail; if so, mem is unchanged.
    cases hvalu : execValuSlots core.scratch instr.valu with
    | none =>
        simp [execInstruction, hform, hvalu]
    | some valu_writes =>
        cases halu : execAluSlots core.scratch instr.alu with
        | none =>
            simp [execInstruction, hform, hvalu, halu]
        | some alu_writes =>
            cases hload : instr.load.foldl
                (fun acc slot =>
                  match acc, execLoadSlot core.scratch mem slot with
                  | some ws, some ws' => some (ws ++ ws')
                  | _, _ => none)
                (some []) with
            | none =>
                simp [execInstruction, hform, hvalu, halu, hload]
            | some load_writes =>
                cases hmw : memWriteMany mem (instr.store.flatMap (execStoreSlot core.scratch)) with
                | none =>
                    simp [execInstruction, hform, hvalu, halu, hload, hmw]
                | some mem' =>
                    have hnot' : addr ∉ (instr.store.flatMap (execStoreSlot core.scratch)).map Prod.fst := by
                      intro hmem
                      apply hnot
                      rcases List.mem_map.1 hmem with ⟨pair, hpairs, haddr⟩
                      rcases List.mem_flatMap.1 hpairs with ⟨slot, hslot, hpairs'⟩
                      have haddr' : addr ∈ storeWriteAddrs core.scratch slot := by
                        apply List.mem_map.2
                        refine ⟨pair, hpairs', ?_⟩
                        simpa [haddr]
                      apply List.mem_flatMap.2
                      refine ⟨storeWriteAddrs core.scratch slot, ?_, haddr'⟩
                      exact List.mem_map.2 ⟨slot, hslot, rfl⟩
                    have hmem : memAt mem' addr = memAt mem addr :=
                      memWriteMany_eq_of_not_written mem mem' _ addr hmw hnot'
                    simp [execInstruction, hform, hvalu, halu, hload, hmw, hmem]
  · simp [execInstruction, hform]

lemma runTraceAuxRW_eq_of_not_written :
    ∀ prog mem core addr,
      addr ∉ listJoin ((runTraceAuxRW prog mem core).2.2.map (fun ws => ws.map Prod.fst)) →
      memAt (runTraceAuxRW prog mem core).1 addr = memAt mem addr := by
  intro prog mem core addr hnot
  induction prog generalizing mem core with
  | nil =>
      simp [runTraceAuxRW] at hnot ⊢
  | cons instr rest ih =>
      simp [runTraceAuxRW] at hnot ⊢
      -- split on execInstructionTrace ok flag
      by_cases hok : (execInstructionTrace mem core instr).1.ok
      · simp [hok] at hnot ⊢
        have hnot' :
            addr ∉
              listJoin (instr.store.map (storeWriteAddrs core.scratch)) ++
                listJoin
                  ((runTraceAuxRW rest (execInstructionTrace mem core instr).1.mem
                        (execInstructionTrace mem core instr).1.core).2.2.map
                    (fun ws => ws.map Prod.fst)) := by
          simpa [listJoin_append, List.map_append, storeWriteAddrs, storeWrites, listJoin] using hnot
        have hnot_head : addr ∉ listJoin (instr.store.map (storeWriteAddrs core.scratch)) := by
          intro hmem
          apply hnot'
          exact List.mem_append.2 (Or.inl hmem)
        have hmem1 := execInstructionTrace_mem_eq_of_not_written mem core instr addr hnot_head
        -- use IH on rest
        have hnot_tail :
            addr ∉
              listJoin
                ((runTraceAuxRW rest (execInstructionTrace mem core instr).1.mem
                      (execInstructionTrace mem core instr).1.core).2.2.map (fun ws => ws.map Prod.fst)) := by
          intro hmem
          apply hnot'
          exact List.mem_append.2 (Or.inr hmem)
        have hmem2 := ih (mem := (execInstructionTrace mem core instr).1.mem)
          (core := (execInstructionTrace mem core instr).1.core) hnot_tail
        -- combine
        simpa [hmem1] using hmem2
      · -- aborted: mem is res.mem
        simp [hok] at hnot ⊢
        -- store writes not applied; mem equality from execInstructionTrace_mem_eq_of_not_written
        have hnot_head : addr ∉ listJoin (instr.store.map (storeWriteAddrs core.scratch)) := by
          intro hmem
          apply hnot
          simp [hmem]
        have hmem1 := execInstructionTrace_mem_eq_of_not_written mem core instr addr hnot_head
        simpa using hmem1

lemma runMem_eq_of_not_written (p : Program) (mem : Memory) (addr : Nat)
    (hnot : addr ∉ writeWords p mem) :
    memAt (runMem p mem) addr = memAt mem addr := by
  have htrace := runTraceAuxRW_eq_of_not_written (prog := p.program) (mem := mem)
    (core := initCore p) (addr := addr) (by simpa [writeWords, writeOps] using hnot)
  -- runMem uses runTrace; runTraceAuxRW has same mem component
  have hfst := runTraceAuxRW_fst_eq p.program mem (initCore p)
  simp [runMem, runTrace, hfst] at htrace
  exact htrace

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

lemma writes_output_of_correct (p : Program) (mem : Memory)
    (hcorrect : CorrectOn spec_kernel p MemSafeKernel)
    (hvalid : ValidInput mem) :
    WritesOutput p mem := by
  intro a ha
  classical
  rcases hvalid with ⟨hsafe, _hlayout, _hks, hdiff⟩
  -- a is an output address: a = valPtr + i
  rcases Finset.mem_image.mp (by simpa [outputAddrs] using ha) with ⟨i, _hi, hEq⟩
  have hnot : a ∈ writeWords p mem := by
    by_contra hnot
    have hrun : run p mem i = memAt mem (memAt mem PTR_INP_VAL + i) := by
      have hmem : memAt (runMem p mem) (memAt mem PTR_INP_VAL + i) =
          memAt mem (memAt mem PTR_INP_VAL + i) := by
        apply runMem_eq_of_not_written
        simpa [hEq] using hnot
      simp [run, hmem]
    have hspec : spec_kernel mem i = memAt mem (memAt mem PTR_INP_VAL + i) := by
      have hrun' : run p mem = spec_kernel mem := by symm; exact hcorrect mem hsafe
      have := congrArg (fun f => f i) hrun'
      simpa [hrun] using this
    exact (hdiff i) hspec
  exact List.mem_toFinset.mpr hnot

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
    (h0 : memAt mem 0 = memAt mem' 0)
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
    simpa [MemSafeKernel, hsize, h0, h1, h2, hforest, hidx, hval] using hrest

/-! ### Trace-equivalence non-interference (straight-line programs) -/

lemma agreeOnList_append_left {xs ys : List Nat} {m1 m2 : Memory}
    (h : AgreeOnList (xs ++ ys) m1 m2) : AgreeOnList xs m1 m2 := by
  refine ⟨h.1, ?_⟩
  intro a ha
  exact h.2 a (by simp [ha])

lemma agreeOnList_append_right {xs ys : List Nat} {m1 m2 : Memory}
    (h : AgreeOnList (xs ++ ys) m1 m2) : AgreeOnList ys m1 m2 := by
  refine ⟨h.1, ?_⟩
  intro a ha
  exact h.2 a (by simp [ha])

lemma agreeOnList_of_join {ops : List (List Nat)} {m1 m2 : Memory}
    (h : AgreeOnList (listJoin ops) m1 m2) :
    ∀ op ∈ ops, AgreeOnList op m1 m2 := by
  intro op hop
  refine ⟨h.1, ?_⟩
  intro a ha
  apply h.2 a
  -- a ∈ listJoin ops via mem_flatMap
  exact List.mem_flatMap.mpr ⟨op, hop, ha⟩

lemma memRead_eq_of_agree (m1 m2 : Memory) (addr : Nat)
    (hsize : m1.size = m2.size) (hval : memAt m1 addr = memAt m2 addr) :
    memRead m1 addr = memRead m2 addr := by
  by_cases h : addr < m1.size
  · have h' : addr < m2.size := by simpa [hsize] using h
    have hval' : m1.data addr = m2.data addr := by simpa [memAt] using hval
    simp [memRead, h, h', hval', memAt]
  · have h' : ¬ addr < m2.size := by simpa [hsize] using h
    simp [memRead, h, h', memAt]

lemma execLoadSlot_eq_of_agree (s : Nat → Nat) (m1 m2 : Memory) (slot : LoadSlot)
    (h : AgreeOnList (loadAddrs s slot) m1 m2) :
    execLoadSlot s m1 slot = execLoadSlot s m2 slot := by
  cases slot with
  | load dest addr =>
      have h' : memAt m1 (s addr) = memAt m2 (s addr) := h.2 _ (by simp [loadAddrs])
      have hread := memRead_eq_of_agree m1 m2 (s addr) h.1 h'
      simp [execLoadSlot, loadAddrs, hread]
  | load_offset dest addr offset =>
      have h' : memAt m1 (s (addr + offset)) = memAt m2 (s (addr + offset)) := by
        exact h.2 _ (by simp [loadAddrs])
      have hread := memRead_eq_of_agree m1 m2 (s (addr + offset)) h.1 h'
      simp [execLoadSlot, loadAddrs, hread]
  | vload dest addr =>
      let base := s addr
      have hread : ∀ i, i < VLEN → memRead m1 (base + i) = memRead m2 (base + i) := by
        intro i hi
        have hi' : base + i ∈ loadAddrs s (.vload dest addr) := by
          simp [loadAddrs, base, hi]
        have hval : memAt m1 (base + i) = memAt m2 (base + i) := h.2 _ hi'
        exact memRead_eq_of_agree m1 m2 (base + i) h.1 hval
      have hvals :
          (List.range VLEN).map (fun i => memRead m1 (base + i)) =
          (List.range VLEN).map (fun i => memRead m2 (base + i)) := by
        apply List.map_congr_left
        intro i hi
        have hi' : i < VLEN := by simpa using hi
        exact hread i hi'
      have hreads :
          (List.range VLEN).map (fun i => (dest + i, (memRead m1 (base + i)).get!)) =
          (List.range VLEN).map (fun i => (dest + i, (memRead m2 (base + i)).get!)) := by
        apply List.map_congr_left
        intro i hi
        have hi' : i < VLEN := by simpa using hi
        have := hread i hi'
        simp [this]
      simp [execLoadSlot, loadAddrs, base, hvals, hreads]
  | const dest val =>
      simp [execLoadSlot, loadAddrs]

-- NOTE: Non-interference is stated at the output level (not full memory equality).
-- The proof should show that if two memories agree on all addresses read by the program,
-- then the program's output slice is equal. This avoids the false stronger claim that
-- the entire final memory is equal.
-- Non-interference at the output level requires that the program actually writes
-- the output slice; otherwise outputs can differ without any reads.
axiom run_eq_of_agree (p : Program) (mem1 mem2 : Memory)
    (hptr : memAt mem1 PTR_INP_VAL = memAt mem2 PTR_INP_VAL)
    (h : AgreeOnList (readWords p mem1) mem1 mem2)
    (hwrites : WritesOutput p mem1) :
    run p mem1 = run p mem2

/-! ### PC-trace non-interference (single-core machine) -/

def machineEqNoMem (m1 m2 : Machine) : Prop :=
  m1.cores = m2.cores ∧
  m1.program = m2.program ∧
  m1.cycle = m2.cycle ∧
  m1.enable_pause = m2.enable_pause ∧
  m1.enable_debug = m2.enable_debug ∧
  m1.value_trace = m2.value_trace ∧
  m1.aborted = m2.aborted



-- run_eq_of_agree is now axiomatized above to avoid an unsound full-memory-equality claim.

/-! ### Adversarial input lemma for values-slice spec -/

def spec_values (mem : Memory) : Output :=
  outputOf (memAt mem PTR_INP_VAL) mem

/-! ### Full-kernel spec (reference semantics) -/

def HASH_STAGES : List (AluOp × Nat × AluOp × AluOp × Nat) :=
  [ (AluOp.add, 0x7ED55D16, AluOp.add, AluOp.shl, 12),
    (AluOp.xor, 0xC761C23C, AluOp.xor, AluOp.shr, 19),
    (AluOp.add, 0x165667B1, AluOp.add, AluOp.shl, 5),
    (AluOp.add, 0xD3A2646C, AluOp.xor, AluOp.shl, 9),
    (AluOp.add, 0xFD7046C5, AluOp.add, AluOp.shl, 3),
    (AluOp.xor, 0xB55A4F09, AluOp.xor, AluOp.shr, 16) ]

def hashStage (x : Nat) (stage : AluOp × Nat × AluOp × AluOp × Nat) : Nat :=
  let (op1, v1, op2, op3, v3) := stage
  let a := aluEval op1 x v1
  let b := aluEval op3 x v3
  aluEval op2 a b

def myhash (x : Nat) : Nat :=
  HASH_STAGES.foldl hashStage x

lemma aluEval_mod32 (op : AluOp) (a1 a2 : Nat) :
    aluEval op a1 a2 = mod32 (aluEval op a1 a2) := by
  cases op with
  | add => simp [aluEval, mod32, Nat.mod_mod]
  | sub => simp [aluEval, mod32, Nat.mod_mod]
  | mul => simp [aluEval, mod32, Nat.mod_mod]
  | idiv =>
      by_cases h : a2 = 0
      · simp [aluEval, h, mod32]
      · simp [aluEval, h, mod32, Nat.mod_mod]
  | cdiv =>
      by_cases h : a2 = 0
      · simp [aluEval, h, mod32]
      · simp [aluEval, h, mod32, Nat.mod_mod]
  | xor => simp [aluEval, mod32, Nat.mod_mod]
  | band => simp [aluEval, mod32, Nat.mod_mod]
  | bor => simp [aluEval, mod32, Nat.mod_mod]
  | shl => simp [aluEval, mod32, Nat.mod_mod, shl]
  | shr => simp [aluEval, mod32, Nat.mod_mod, shr]
  | mod =>
      by_cases h : a2 = 0
      · simp [aluEval, h, mod32]
      · simp [aluEval, h, mod32, Nat.mod_mod]
  | lt =>
      by_cases h : a1 < a2
      · have h1 : (1:Nat) < MOD32 := by decide
        have hmod : (1:Nat) % MOD32 = (1:Nat) := Nat.mod_eq_of_lt h1
        simpa [h, hmod, aluEval]
      · have h0 : (0:Nat) < MOD32 := by decide
        have hmod : (0:Nat) % MOD32 = (0:Nat) := Nat.mod_eq_of_lt h0
        simpa [h, hmod, aluEval]
  | eq =>
      by_cases h : a1 = a2
      · have h1 : (1:Nat) < MOD32 := by decide
        have hmod : (1:Nat) % MOD32 = (1:Nat) := Nat.mod_eq_of_lt h1
        simpa [h, hmod, aluEval]
      · have h0 : (0:Nat) < MOD32 := by decide
        have hmod : (0:Nat) % MOD32 = (0:Nat) := Nat.mod_eq_of_lt h0
        simpa [h, hmod, aluEval]

lemma hashStage_mod32 (x : Nat) (stage : AluOp × Nat × AluOp × AluOp × Nat) :
    hashStage x stage = mod32 (hashStage x stage) := by
  rcases stage with ⟨op1, v1, op2, op3, v3⟩
  have h := aluEval_mod32 op2 (aluEval op1 x v1) (aluEval op3 x v3)
  simpa [hashStage] using h

lemma foldl_hashStage_mod32 (acc : Nat) (l : List (AluOp × Nat × AluOp × AluOp × Nat))
    (hacc : acc = mod32 acc) :
    List.foldl hashStage acc l = mod32 (List.foldl hashStage acc l) := by
  induction l generalizing acc with
  | nil =>
      simpa using hacc
  | cons stage tail ih =>
      -- foldl on cons
      have hstage : hashStage acc stage = mod32 (hashStage acc stage) :=
        hashStage_mod32 acc stage
      -- apply IH to the new accumulator
      simpa [List.foldl] using
        (ih (acc := hashStage acc stage) hstage)

lemma foldl_hashStage_mod32_nonempty (acc : Nat)
    (l : List (AluOp × Nat × AluOp × AluOp × Nat)) (hne : l ≠ []) :
    List.foldl hashStage acc l = mod32 (List.foldl hashStage acc l) := by
  cases l with
  | nil =>
      cases hne rfl
  | cons stage tail =>
      -- after first stage accumulator is mod32
      have hacc : hashStage acc stage = mod32 (hashStage acc stage) :=
        hashStage_mod32 acc stage
      simpa [List.foldl] using (foldl_hashStage_mod32 (acc := hashStage acc stage) (l := tail) hacc)

lemma myhash_mod32 (x : Nat) : myhash x = mod32 (myhash x) := by
  -- HASH_STAGES is nonempty, so after the first stage the accumulator is mod32
  unfold myhash
  have hne : (HASH_STAGES : List (AluOp × Nat × AluOp × AluOp × Nat)) ≠ [] := by
    decide
  simpa using (foldl_hashStage_mod32_nonempty x HASH_STAGES hne)

lemma mod32_myhash (x : Nat) : mod32 (myhash x) = myhash x := by
  symm
  exact myhash_mod32 x

def step (tree : Nat → Nat) (nNodes idx val : Nat) : Nat × Nat :=
  let node := tree idx
  let val' := myhash (aluEval AluOp.xor val node)
  let idx' := 2 * idx + (if val' % 2 = 0 then 1 else 2)
  let idx'' := if idx' ≥ nNodes then 0 else idx'
  (idx'', val')

opaque iterRounds (tree : Nat → Nat) (nNodes : Nat) (n idx val : Nat) : Nat × Nat

axiom iterRounds_zero (tree : Nat → Nat) (nNodes idx val : Nat) :
    iterRounds tree nNodes 0 idx val = (idx, val)

axiom iterRounds_succ (tree : Nat → Nat) (nNodes n idx val : Nat) :
    iterRounds tree nNodes (n+1) idx val =
      iterRounds tree nNodes n (step tree nNodes idx val).1 (step tree nNodes idx val).2

def spec_kernel (mem : Memory) : Output :=
  let rounds := memAt mem 0
  let nNodes := memAt mem 1
  let forestPtr := memAt mem PTR_FOREST
  let idxPtr := memAt mem PTR_INP_IDX
  let valPtr := memAt mem PTR_INP_VAL
  let tree := fun i => memAt mem (forestPtr + i)
  fun i =>
    let idx0 := memAt mem (idxPtr + i)
    let val0 := memAt mem (valPtr + i)
    let (_, valF) := iterRounds tree nNodes rounds idx0 val0
    valF

def iterHash : Nat → Nat → Nat
  | 0, v => v
  | n+1, v => iterHash n (myhash v)

def zeroTree : Nat → Nat := fun _ => 0

set_option maxRecDepth 1000000

lemma natXor_zero_right (n : Nat) : natXor n 0 = n := by
  simp [natXor, Nat.bitwise_zero_right]

lemma aluEval_xor_zero (val : Nat) : aluEval AluOp.xor val 0 = mod32 val := by
  simp [aluEval, natXor_zero_right, mod32]

lemma step_zeroTree_val (idx val : Nat) :
    (step zeroTree N_NODES idx val).2 = myhash (mod32 val) := by
  unfold step
  dsimp [zeroTree]
  -- reduce to aluEval xor on 0
  apply congrArg
  exact aluEval_xor_zero val

axiom iterRounds_zeroTree_val :
    ∀ n idx val,
      (iterRounds zeroTree N_NODES n idx val).2 = iterHash n (mod32 val)

lemma step_idx_lt (tree : Nat → Nat) (nNodes idx val : Nat) (hnpos : 0 < nNodes) :
    (step tree nNodes idx val).1 < nNodes := by
  dsimp [step]
  set node := tree idx
  set val' := myhash (aluEval AluOp.xor val node)
  set idx' := 2 * idx + (if val' % 2 = 0 then 1 else 2)
  by_cases hge : idx' ≥ nNodes
  · have hpos : 0 < nNodes := hnpos
    simp [hge, hpos]
  · have hlt : idx' < nNodes := lt_of_not_ge hge
    simp [hge, hlt]

axiom iterRounds_zero_tree_val_range (tree : Nat → Nat) (nNodes : Nat)
    (hzero : ∀ i < nNodes, tree i = 0) (hnpos : 0 < nNodes) :
    ∀ n idx val, idx < nNodes →
      (iterRounds tree nNodes n idx val).2 = iterHash n (mod32 val)

axiom spec_kernel_uniform_val (mem : Memory) (i : Fin BATCH_SIZE) (v : Nat)
    (hrounds : memAt mem 0 = ROUNDS)
    (hnodes : memAt mem 1 = N_NODES)
    (hforest : ∀ k, k < N_NODES → memAt mem (memAt mem PTR_FOREST + k) = 0)
    (hidx : memAt mem (memAt mem PTR_INP_IDX + i) = 0)
    (hval : memAt mem (memAt mem PTR_INP_VAL + i) = v) :
    spec_kernel mem i = iterHash ROUNDS v

def memUniform0 : Memory :=
  { data :=
      fun a =>
        if a = 0 then ROUNDS
        else if a = 1 then N_NODES
        else if a = 2 then BATCH_SIZE
        else if a = 3 then HEIGHT
        else if a = PTR_FOREST then FOREST_BASE
        else if a = PTR_INP_IDX then IDX_BASE
        else if a = PTR_INP_VAL then VAL_BASE
        else if FOREST_BASE ≤ a ∧ a < FOREST_BASE + N_NODES then 0
        else if IDX_BASE ≤ a ∧ a < IDX_BASE + BATCH_SIZE then 0
        else if VAL_BASE ≤ a ∧ a < VAL_BASE + BATCH_SIZE then 0
        else 0,
    size := MEM_SIZE }

def memUpdate (mem : Memory) (addr val : Nat) : Memory :=
  { mem with data := fun a => if a = addr then val else mem.data a }

def UniformZeroKernel (mem : Memory) : Prop :=
  MemSafeKernel mem ∧
  memAt mem 0 = ROUNDS ∧
  memAt mem 1 = N_NODES ∧
  memAt mem 2 = BATCH_SIZE ∧
  memAt mem 3 = HEIGHT ∧
  KernelLayout mem ∧
  KernelDisjoint mem ∧
  (∀ k, k < N_NODES → memAt mem (memAt mem PTR_FOREST + k) = 0) ∧
  (∀ i : Fin BATCH_SIZE, memAt mem (memAt mem PTR_INP_IDX + i) = 0) ∧
  (∀ i : Fin BATCH_SIZE, memAt mem (memAt mem PTR_INP_VAL + i) = 0)

def AdversaryList (mem : Memory) (L : List Nat) : Prop :=
  List.Nodup L ∧
  (∀ addr ∈ L, AddrSafe mem addr) ∧
  (∀ addr ∈ L, ∃ i : Fin BATCH_SIZE,
    spec_kernel (memUpdate mem addr (memAt mem addr + 1)) i ≠ spec_kernel mem i)

def AdversaryK (mem : Memory) (k : Nat) : Prop :=
  ∃ L : List Nat, AdversaryList mem L ∧
    L.length = k * BATCH_SIZE * memAt mem 0

/-! ### Structured adversary: distinct addresses per (round, lane, copy) -/

def RoundDistinctNodes (mem : Memory) (k : Nat) : Prop :=
  let rounds := memAt mem 0
  ∃ f : Fin rounds → Fin BATCH_SIZE → Fin k → Nat,
    (∀ r i j, AddrSafe mem (f r i j)) ∧
    (∀ r i j, ∃ lane : Fin BATCH_SIZE,
      spec_kernel (memUpdate mem (f r i j) (memAt mem (f r i j) + 1)) lane ≠
        spec_kernel mem lane) ∧
    Function.Injective (fun t : (Fin rounds × Fin BATCH_SIZE × Fin k) =>
      f t.1 t.2.1 t.2.2)

lemma adversaryK_of_roundDistinct (mem : Memory) (k : Nat)
    (h : RoundDistinctNodes mem k) : AdversaryK mem k := by
  classical
  dsimp [RoundDistinctNodes] at h
  rcases h with ⟨f, hsafe, hsens, hinj⟩
  let rounds := memAt mem 0
  let f' : (Fin rounds × Fin BATCH_SIZE × Fin k) → Nat :=
    fun t => f t.1 t.2.1 t.2.2
  let L : List Nat := (Finset.univ.image f').toList
  refine ⟨L, ?_, ?_⟩
  · refine ⟨?hnodup, ?haddr, ?hsens⟩
    · simpa [L] using (Finset.nodup_toList (s:=Finset.univ.image f'))
    · intro addr haddrL
      have hmem' : addr ∈ (Finset.univ.image f') := by
        have : addr ∈ (Finset.univ.image f').toList := by
          simpa [L] using haddrL
        exact (Finset.mem_toList.mp this)
      rcases Finset.mem_image.mp hmem' with ⟨t, ht, rfl⟩
      exact hsafe t.1 t.2.1 t.2.2
    · intro addr haddrL
      have hmem' : addr ∈ (Finset.univ.image f') := by
        have : addr ∈ (Finset.univ.image f').toList := by
          simpa [L] using haddrL
        exact (Finset.mem_toList.mp this)
      rcases Finset.mem_image.mp hmem' with ⟨t, ht, rfl⟩
      exact hsens t.1 t.2.1 t.2.2
  · have hlen : L.length = (Finset.univ.image f').card := by
      simpa [L] using (Finset.length_toList (s:=Finset.univ.image f'))
    have hcard_univ :
        (Finset.univ : Finset (Fin rounds × Fin BATCH_SIZE × Fin k)).card =
          rounds * BATCH_SIZE * k := by
      simp [Fintype.card_prod, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
    have hcard_image :
        (Finset.univ.image f').card =
          (Finset.univ : Finset (Fin rounds × Fin BATCH_SIZE × Fin k)).card := by
      simpa using (Finset.card_image_of_injective (s:=Finset.univ) hinj)
    have : L.length = rounds * BATCH_SIZE * k := by
      calc
        L.length = (Finset.univ.image f').card := hlen
        _ = (Finset.univ : Finset (Fin rounds × Fin BATCH_SIZE × Fin k)).card := hcard_image
        _ = rounds * BATCH_SIZE * k := hcard_univ
    -- reorder to k * BATCH_SIZE * rounds
    simpa [rounds, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using this

/-! ### Concrete large-tree adversary (for unconditional 256 bound) -/

def BIG_M : Nat := Nat.pow 2 (ROUNDS + 2)

def bigIdxNat (i : Nat) : Nat := (2 * i + 1) * BIG_M

def bigIdx (i : Fin BATCH_SIZE) : Nat := bigIdxNat i

def bSeq (r : Nat) : Nat :=
  if iterHash (r + 1) 0 % 2 = 0 then 1 else 2

def cSeq : Nat → Nat
  | 0 => 0
  | r+1 => 2 * cSeq r + bSeq r

def idxAt (r : Nat) (i : Fin BATCH_SIZE) : Nat :=
  (Nat.pow 2 r) * bigIdx i + cSeq r

def N_NODES_BIG : Nat :=
  (Nat.pow 2 ROUNDS) * (2 * BATCH_SIZE) * BIG_M + BIG_M

def BIG_FOREST_BASE : Nat := HEADER_SIZE
def BIG_IDX_BASE : Nat := BIG_FOREST_BASE + N_NODES_BIG
def BIG_VAL_BASE : Nat := BIG_IDX_BASE + BATCH_SIZE
def MEM_BIG_SIZE : Nat := BIG_VAL_BASE + BATCH_SIZE

def memBig : Memory :=
  { data :=
      fun a =>
        if a = 0 then ROUNDS
        else if a = 1 then N_NODES_BIG
        else if a = 2 then BATCH_SIZE
        else if a = 3 then HEIGHT
        else if a = PTR_FOREST then BIG_FOREST_BASE
        else if a = PTR_INP_IDX then BIG_IDX_BASE
        else if a = PTR_INP_VAL then BIG_VAL_BASE
        else if BIG_FOREST_BASE ≤ a ∧ a < BIG_FOREST_BASE + N_NODES_BIG then 0
        else if BIG_IDX_BASE ≤ a ∧ a < BIG_IDX_BASE + BATCH_SIZE then
          bigIdxNat (a - BIG_IDX_BASE)
        else if BIG_VAL_BASE ≤ a ∧ a < BIG_VAL_BASE + BATCH_SIZE then 0
        else 0,
    size := MEM_BIG_SIZE }

axiom bSeq_le_two (r : Nat) : bSeq r ≤ 2

axiom cSeq_bound : ∀ r, cSeq r < Nat.pow 2 (r + 1)

lemma pow_le_bigM {r : Nat} (hr : r < ROUNDS) :
    Nat.pow 2 (r + 1) ≤ BIG_M := by
  have hle : r + 1 ≤ ROUNDS + 2 := by
    exact Nat.succ_le_succ (Nat.le_trans (Nat.le_of_lt hr) (Nat.le_add_right _ _))
  have : Nat.pow 2 (r + 1) ≤ Nat.pow 2 (ROUNDS + 2) :=
    Nat.pow_le_pow_right (by decide : 0 < 2) hle
  simpa [BIG_M] using this

axiom idxAt_lt_N_NODES_BIG (r : Nat) (i : Fin BATCH_SIZE) (hr : r < ROUNDS) :
    idxAt r i < N_NODES_BIG

def idxAtR (r : Fin ROUNDS) (i : Fin BATCH_SIZE) : Nat := idxAt (r : Nat) i

lemma idxAtR_lt (r : Fin ROUNDS) (i : Fin BATCH_SIZE) :
    idxAtR r i < N_NODES_BIG := by
  exact idxAt_lt_N_NODES_BIG (r := r) (i := i) r.isLt

axiom memBig_safe : MemSafeKernel memBig

axiom memBig_rounds : memAt memBig 0 = ROUNDS

axiom memBig_ptrs :
    memAt memBig PTR_FOREST = BIG_FOREST_BASE ∧
    memAt memBig PTR_INP_IDX = BIG_IDX_BASE ∧
    memAt memBig PTR_INP_VAL = BIG_VAL_BASE

axiom memBig_idx (i : Fin BATCH_SIZE) :
    memAt memBig (BIG_IDX_BASE + i) = bigIdx i

axiom memBig_val (i : Fin BATCH_SIZE) :
    memAt memBig (BIG_VAL_BASE + i) = 0

axiom memBig_tree (k : Nat) (hk : k < N_NODES_BIG) :
    memAt memBig (BIG_FOREST_BASE + k) = 0

def memBigTreeAddrs : Finset Nat :=
  (Finset.univ.image (fun t : Fin ROUNDS × Fin BATCH_SIZE =>
    BIG_FOREST_BASE + idxAtR t.1 t.2))

def memBigValAddrs : Finset Nat :=
  (Finset.univ.image (fun i : Fin BATCH_SIZE => BIG_VAL_BASE + i))

def memBigAllAddrs : Finset Nat :=
  memBigTreeAddrs ∪ memBigValAddrs

lemma memBigTreeAddrs_card :
    memBigTreeAddrs.card = ROUNDS * BATCH_SIZE := by
  native_decide

lemma memBigValAddrs_card :
    memBigValAddrs.card = BATCH_SIZE := by
  native_decide

lemma memBigAddrs_disjoint :
    Disjoint memBigTreeAddrs memBigValAddrs := by
  native_decide

axiom memBigAllAddrs_card :
    memBigAllAddrs.card = BATCH_SIZE * (ROUNDS + 1)

axiom spec_kernel_memBig_flip (r : Fin ROUNDS) (i : Fin BATCH_SIZE) :
    spec_kernel
        (memUpdate memBig (BIG_FOREST_BASE + idxAtR r i)
          (memAt memBig (BIG_FOREST_BASE + idxAtR r i) + 1)) i
      ≠ spec_kernel memBig i

axiom spec_kernel_memBig_val_flip (i : Fin BATCH_SIZE) :
    spec_kernel
        (memUpdate memBig (BIG_VAL_BASE + i)
          (memAt memBig (BIG_VAL_BASE + i) + 1)) i
      ≠ spec_kernel memBig i

axiom roundDistinctNodes_memBig : RoundDistinctNodes memBig 1

axiom memBig_tree_addr_safe (r : Fin ROUNDS) (i : Fin BATCH_SIZE) :
    AddrSafe memBig (BIG_FOREST_BASE + idxAtR r i)

axiom memBig_val_addr_safe (i : Fin BATCH_SIZE) :
    AddrSafe memBig (BIG_VAL_BASE + i)

axiom memBigTreeAddrs_subset_readWords_machine (p : Program)
    (hstraight : StraightLine p)
    (hcorrect : CorrectOnMachine spec_kernel p MemSafeKernel) :
    memBigTreeAddrs ⊆ (readWordsMachine p memBig).toFinset

axiom memBigValAddrs_subset_readWords_machine (p : Program)
    (hstraight : StraightLine p)
    (hcorrect : CorrectOnMachine spec_kernel p MemSafeKernel) :
    memBigValAddrs ⊆ (readWordsMachine p memBig).toFinset

axiom memBigAllAddrs_subset_readWords_machine (p : Program)
    (hcorrect : CorrectOnMachine spec_kernel p MemSafeKernel) :
    memBigAllAddrs ⊆ (readWordsMachine p memBig).toFinset

axiom min_required_words_kernel_machine_memBig_all (p : Program)
    (hcorrect : CorrectOnMachine spec_kernel p MemSafeKernel) :
    BATCH_SIZE * (ROUNDS + 1) ≤ readWordCountMachine p memBig

def KernelSensitive (mem : Memory) : Prop :=
  ∀ i : Fin BATCH_SIZE,
    spec_kernel
        (memUpdate mem (memAt mem PTR_INP_VAL + i)
          (memAt mem (memAt mem PTR_INP_VAL + i) + 1)) i
      ≠ spec_kernel mem i

def OutputDiffers (mem : Memory) : Prop :=
  ∀ i : Fin BATCH_SIZE,
    spec_kernel mem i ≠ memAt mem (memAt mem PTR_INP_VAL + i)

def ValidInput (mem : Memory) : Prop :=
  MemSafeKernel mem ∧ KernelLayout mem ∧ KernelSensitive mem ∧ OutputDiffers mem

lemma memUpdate_header_eq (mem : Memory) {addr val k : Nat}
    (hk : k < HEADER_SIZE) (haddr : HEADER_SIZE ≤ addr) :
    memAt (memUpdate mem addr val) k = memAt mem k := by
  have hlt : k < addr := lt_of_lt_of_le hk haddr
  have hne : k ≠ addr := ne_of_lt hlt
  simp [memUpdate, memAt, hne]

lemma addr_ge_header_of_layout (mem : Memory) (i : Fin BATCH_SIZE)
    (hlayout : KernelLayout mem) : HEADER_SIZE ≤ memAt mem PTR_INP_VAL + i := by
  dsimp [KernelLayout] at hlayout
  rcases hlayout with ⟨_hforest_ge, _hidx_ge, hval_ge⟩
  exact Nat.le_trans hval_ge (Nat.le_add_right _ _)

lemma memSafeKernel_update_val (mem : Memory) (i : Fin BATCH_SIZE)
    (hlayout : KernelLayout mem) (hsafe : MemSafeKernel mem) :
    MemSafeKernel
      (memUpdate mem (memAt mem PTR_INP_VAL + i)
        (memAt mem (memAt mem PTR_INP_VAL + i) + 1)) := by
  dsimp [KernelLayout] at hlayout
  rcases hlayout with ⟨hforest_ge, hidx_ge, hval_ge⟩
  let addr := memAt mem PTR_INP_VAL + i
  let mem' := memUpdate mem addr (memAt mem addr + 1)
  have haddr_ge : HEADER_SIZE ≤ addr := by
    exact Nat.le_trans hval_ge (Nat.le_add_right _ _)
  have hsize : mem.size = mem'.size := rfl
  have h0 : memAt mem 0 = memAt mem' 0 := by
    have hk : (0:Nat) < HEADER_SIZE := by decide
    have h := memUpdate_header_eq (mem:=mem) (addr:=addr) (val:=memAt mem addr + 1) hk haddr_ge
    simpa [mem'] using h.symm
  have h1 : memAt mem 1 = memAt mem' 1 := by
    have hk : (1:Nat) < HEADER_SIZE := by decide
    have h := memUpdate_header_eq (mem:=mem) (addr:=addr) (val:=memAt mem addr + 1) hk haddr_ge
    simpa [mem'] using h.symm
  have h2 : memAt mem 2 = memAt mem' 2 := by
    have hk : (2:Nat) < HEADER_SIZE := by decide
    have h := memUpdate_header_eq (mem:=mem) (addr:=addr) (val:=memAt mem addr + 1) hk haddr_ge
    simpa [mem'] using h.symm
  have hforest : memAt mem PTR_FOREST = memAt mem' PTR_FOREST := by
    have hk : PTR_FOREST < HEADER_SIZE := by decide
    have h := memUpdate_header_eq (mem:=mem) (addr:=addr) (val:=memAt mem addr + 1) hk haddr_ge
    simpa [mem'] using h.symm
  have hidx : memAt mem PTR_INP_IDX = memAt mem' PTR_INP_IDX := by
    have hk : PTR_INP_IDX < HEADER_SIZE := by decide
    have h := memUpdate_header_eq (mem:=mem) (addr:=addr) (val:=memAt mem addr + 1) hk haddr_ge
    simpa [mem'] using h.symm
  have hval : memAt mem PTR_INP_VAL = memAt mem' PTR_INP_VAL := by
    have hk : PTR_INP_VAL < HEADER_SIZE := by decide
    have h := memUpdate_header_eq (mem:=mem) (addr:=addr) (val:=memAt mem addr + 1) hk haddr_ge
    simpa [mem'] using h.symm
  exact memSafeKernel_of_eq_header mem mem' hsize h0 h1 h2 hforest hidx hval hsafe

lemma memSafeKernel_update_addr (mem : Memory) (addr : Nat)
    (hsafe : MemSafeKernel mem) (haddr : AddrSafe mem addr) :
    MemSafeKernel (memUpdate mem addr (memAt mem addr + 1)) := by
  let mem' := memUpdate mem addr (memAt mem addr + 1)
  have haddr_ge : HEADER_SIZE ≤ addr := haddr.1
  have hsize : mem.size = mem'.size := rfl
  have h0 : memAt mem 0 = memAt mem' 0 := by
    have hk : (0:Nat) < HEADER_SIZE := by decide
    have h := memUpdate_header_eq (mem:=mem) (addr:=addr) (val:=memAt mem addr + 1) hk haddr_ge
    simpa [mem'] using h.symm
  have h1 : memAt mem 1 = memAt mem' 1 := by
    have hk : (1:Nat) < HEADER_SIZE := by decide
    have h := memUpdate_header_eq (mem:=mem) (addr:=addr) (val:=memAt mem addr + 1) hk haddr_ge
    simpa [mem'] using h.symm
  have h2 : memAt mem 2 = memAt mem' 2 := by
    have hk : (2:Nat) < HEADER_SIZE := by decide
    have h := memUpdate_header_eq (mem:=mem) (addr:=addr) (val:=memAt mem addr + 1) hk haddr_ge
    simpa [mem'] using h.symm
  have hforest : memAt mem PTR_FOREST = memAt mem' PTR_FOREST := by
    have hk : PTR_FOREST < HEADER_SIZE := by decide
    have h := memUpdate_header_eq (mem:=mem) (addr:=addr) (val:=memAt mem addr + 1) hk haddr_ge
    simpa [mem'] using h.symm
  have hidx : memAt mem PTR_INP_IDX = memAt mem' PTR_INP_IDX := by
    have hk : PTR_INP_IDX < HEADER_SIZE := by decide
    have h := memUpdate_header_eq (mem:=mem) (addr:=addr) (val:=memAt mem addr + 1) hk haddr_ge
    simpa [mem'] using h.symm
  have hval : memAt mem PTR_INP_VAL = memAt mem' PTR_INP_VAL := by
    have hk : PTR_INP_VAL < HEADER_SIZE := by decide
    have h := memUpdate_header_eq (mem:=mem) (addr:=addr) (val:=memAt mem addr + 1) hk haddr_ge
    simpa [mem'] using h.symm
  exact memSafeKernel_of_eq_header mem mem' hsize h0 h1 h2 hforest hidx hval hsafe

def memUniform1 : Memory :=
  memUpdate memUniform0 VAL_BASE 1

def memUniformVal (j : Fin BATCH_SIZE) : Memory :=
  memUpdate memUniform0 (VAL_BASE + j) 1

lemma memUniform0_safe : MemSafeKernel memUniform0 := by
  native_decide

lemma val_base_ge_header : HEADER_SIZE ≤ VAL_BASE := by
  -- VAL_BASE = (HEADER_SIZE + N_NODES) + BATCH_SIZE
  have h1 : HEADER_SIZE ≤ IDX_BASE := by
    -- IDX_BASE = HEADER_SIZE + N_NODES
    simpa [IDX_BASE, FOREST_BASE, HEADER_SIZE] using (Nat.le_add_left HEADER_SIZE N_NODES)
  have h2 : IDX_BASE ≤ VAL_BASE := by
    -- VAL_BASE = IDX_BASE + BATCH_SIZE
    simpa [VAL_BASE] using (Nat.le_add_right IDX_BASE BATCH_SIZE)
  exact Nat.le_trans h1 h2

lemma memUniformVal_header_eq (j : Fin BATCH_SIZE) (k : Nat) (hk : k < HEADER_SIZE) :
    memAt (memUniformVal j) k = memAt memUniform0 k := by
  have hlt : k < VAL_BASE := by
    exact lt_of_lt_of_le hk val_base_ge_header
  have hle : VAL_BASE ≤ VAL_BASE + (j : Nat) := Nat.le_add_right _ _
  have hne : k ≠ VAL_BASE + (j : Nat) := by
    exact ne_of_lt (lt_of_lt_of_le hlt hle)
  simp [memUniformVal, memUpdate, memAt, hne]

lemma memUniformVal_safe (j : Fin BATCH_SIZE) : MemSafeKernel (memUniformVal j) := by
  -- Same header and size as memUniform0, so safety transfers.
  have hsize : memUniform0.size = (memUniformVal j).size := rfl
  have h0 : memAt memUniform0 0 = memAt (memUniformVal j) 0 := by
    symm; exact memUniformVal_header_eq j 0 (by decide)
  have h1 : memAt memUniform0 1 = memAt (memUniformVal j) 1 := by
    symm; exact memUniformVal_header_eq j 1 (by decide)
  have h2 : memAt memUniform0 2 = memAt (memUniformVal j) 2 := by
    symm; exact memUniformVal_header_eq j 2 (by decide)
  have hforest : memAt memUniform0 PTR_FOREST = memAt (memUniformVal j) PTR_FOREST := by
    symm; exact memUniformVal_header_eq j PTR_FOREST (by decide)
  have hidx : memAt memUniform0 PTR_INP_IDX = memAt (memUniformVal j) PTR_INP_IDX := by
    symm; exact memUniformVal_header_eq j PTR_INP_IDX (by decide)
  have hval : memAt memUniform0 PTR_INP_VAL = memAt (memUniformVal j) PTR_INP_VAL := by
    symm; exact memUniformVal_header_eq j PTR_INP_VAL (by decide)
  have hsafe := memSafeKernel_of_eq_header memUniform0 (memUniformVal j)
    hsize h0 h1 h2 hforest hidx hval memUniform0_safe
  simpa using hsafe

lemma memUniform_ptrs :
    memAt memUniform0 PTR_FOREST = FOREST_BASE ∧
    memAt memUniform0 PTR_INP_IDX = IDX_BASE ∧
    memAt memUniform0 PTR_INP_VAL = VAL_BASE := by
  simp [memUniform0, memAt, PTR_FOREST, PTR_INP_IDX, PTR_INP_VAL]

lemma memUniform_idx (i : Nat) :
    memAt memUniform0 (IDX_BASE + i) = 0 := by
  simp [memUniform0, memAt, IDX_BASE, PTR_FOREST, PTR_INP_IDX, PTR_INP_VAL]

lemma memUniform_val (i : Nat) :
    memAt memUniform0 (VAL_BASE + i) = 0 := by
  simp [memUniform0, memAt, VAL_BASE, PTR_FOREST, PTR_INP_IDX, PTR_INP_VAL]

lemma memUniform_forest (i : Nat) :
    memAt memUniform0 (FOREST_BASE + i) = 0 := by
  simp [memUniform0, memAt, FOREST_BASE, PTR_FOREST, PTR_INP_IDX, PTR_INP_VAL]

lemma memUniform_idx_fin (i : Fin BATCH_SIZE) :
    memAt memUniform0 (IDX_BASE + i) = 0 := by
  simpa using memUniform_idx (i := (i : Nat))

lemma memUniform_val_fin (i : Fin BATCH_SIZE) :
    memAt memUniform0 (VAL_BASE + i) = 0 := by
  simpa using memUniform_val (i := (i : Nat))

axiom spec_kernel_uniform0 (i : Fin BATCH_SIZE) :
    spec_kernel memUniform0 i = iterHash ROUNDS 0

lemma spec_kernel_uniform1 (i : Fin BATCH_SIZE) :
    spec_kernel memUniform1 i = iterHash ROUNDS (if i = (0 : Fin BATCH_SIZE) then 1 else 0) := by
  have hptrs := memUniform_ptrs
  rcases hptrs with ⟨hforest, hidx, hval⟩
  have hval0 : memAt memUniform1 (VAL_BASE + i) = if i = (0 : Fin BATCH_SIZE) then 1 else 0 := by
    by_cases hi : i = (0 : Fin BATCH_SIZE)
    · subst hi
      simp [memUniform1, memUpdate, memAt, VAL_BASE, memUniform_val]
    ·
      have hne : (VAL_BASE + (i : Nat)) ≠ VAL_BASE := by
        intro hEq
        have h' : (i : Nat) = 0 := by
          exact Nat.add_left_cancel (by simpa using hEq)
        exact hi (Fin.ext h')
      simp [memUniform1, memUpdate, memAt, VAL_BASE, hi, memUniform_val, hne]
  simp [spec_kernel, memUniform0, memUniform1, memUpdate, memAt, hforest, hidx, hval,
    memUniform_idx_fin, memUniform_forest, iterRounds_zeroTree_val, zeroTree, hval0]

lemma memUniformVal_at (j i : Fin BATCH_SIZE) :
    memAt (memUniformVal j) (VAL_BASE + i) = if i = j then 1 else 0 := by
  by_cases h : i = j
  · subst h
    simp [memUniformVal, memUpdate, memAt, VAL_BASE, memUniform_val]
  ·
    have hne : (VAL_BASE + (i : Nat)) ≠ VAL_BASE + (j : Nat) := by
      intro hEq
      have h' : (i : Nat) = (j : Nat) := Nat.add_left_cancel hEq
      exact h (Fin.ext h')
    simp [memUniformVal, memUpdate, memAt, VAL_BASE, h, memUniform_val, hne]

lemma spec_kernel_uniformVal (j i : Fin BATCH_SIZE) :
    spec_kernel (memUniformVal j) i = iterHash ROUNDS (if i = j then 1 else 0) := by
  have hptrs := memUniform_ptrs
  rcases hptrs with ⟨hforest, hidx, hval⟩
  have hval0 : memAt (memUniformVal j) (VAL_BASE + i) = if i = j then 1 else 0 :=
    memUniformVal_at j i
  simp [spec_kernel, memUniform0, memUniformVal, memUpdate, memAt, hforest, hidx, hval,
    memUniform_idx_fin, memUniform_forest, iterRounds_zeroTree_val, zeroTree, hval0]

lemma iterHash_ne : iterHash ROUNDS 0 ≠ iterHash ROUNDS 1 := by
  native_decide

lemma iterHash_ne_zero : iterHash ROUNDS 0 ≠ 0 := by
  native_decide

lemma spec_kernel_diff_uniform0 :
    spec_kernel memUniform1 (0 : Fin BATCH_SIZE) ≠ spec_kernel memUniform0 (0 : Fin BATCH_SIZE) := by
  simp [spec_kernel_uniform0, spec_kernel_uniform1, iterHash_ne]

lemma spec_kernel_diff_uniformVal (j : Fin BATCH_SIZE) :
    spec_kernel (memUniformVal j) j ≠ spec_kernel memUniform0 j := by
  simp [spec_kernel_uniform0, spec_kernel_uniformVal, iterHash_ne]

lemma kernelSensitive_uniform_zero (mem : Memory)
    (hunif : UniformZeroKernel mem) : KernelSensitive mem := by
  intro i
  rcases hunif with ⟨_hsafe, hrounds, hnodes, _hbatch, _hheight, hlayout, hdisjoint,
    hforest, hidx, hval⟩
  let forestPtr := memAt mem PTR_FOREST
  let idxPtr := memAt mem PTR_INP_IDX
  let valPtr := memAt mem PTR_INP_VAL
  let addr := valPtr + i
  let mem' := memUpdate mem addr (memAt mem addr + 1)
  have hspec0 : spec_kernel mem i = iterHash ROUNDS 0 := by
    have hidx0 : memAt mem (memAt mem PTR_INP_IDX + i) = 0 := hidx i
    have hval0 : memAt mem (memAt mem PTR_INP_VAL + i) = 0 := hval i
    exact spec_kernel_uniform_val mem i 0 hrounds hnodes hforest hidx0 hval0
  dsimp [KernelLayout] at hlayout
  rcases hlayout with ⟨_hforest_ge, _hidx_ge, hval_ge⟩
  have haddr : HEADER_SIZE ≤ addr := addr_ge_header_of_layout mem i hlayout
  have hptr_forest : memAt mem' PTR_FOREST = forestPtr := by
    have hk : PTR_FOREST < HEADER_SIZE := by decide
    have h := memUpdate_header_eq (mem:=mem) (addr:=addr) (val:=memAt mem addr + 1) hk haddr
    simpa [mem', addr, forestPtr] using h
  have hptr_idx : memAt mem' PTR_INP_IDX = idxPtr := by
    have hk : PTR_INP_IDX < HEADER_SIZE := by decide
    have h := memUpdate_header_eq (mem:=mem) (addr:=addr) (val:=memAt mem addr + 1) hk haddr
    simpa [mem', addr, idxPtr] using h
  have hptr_val : memAt mem' PTR_INP_VAL = valPtr := by
    have hk : PTR_INP_VAL < HEADER_SIZE := by decide
    have h := memUpdate_header_eq (mem:=mem) (addr:=addr) (val:=memAt mem addr + 1) hk haddr
    simpa [mem', addr, valPtr] using h
  rcases hdisjoint with ⟨hfi, hiv⟩
  have hidx_le_val : idxPtr ≤ valPtr := by
    exact Nat.le_trans (Nat.le_add_right _ _) hiv
  have hforest' : ∀ k, k < N_NODES → memAt mem' (forestPtr + k) = 0 := by
    intro k hk
    have h1 : forestPtr + k < forestPtr + N_NODES := Nat.add_lt_add_left hk forestPtr
    have h2 : forestPtr + k < idxPtr := lt_of_lt_of_le h1 hfi
    have h3 : forestPtr + k < valPtr := lt_of_lt_of_le h2 hidx_le_val
    have h4 : forestPtr + k < addr := lt_of_lt_of_le h3 (Nat.le_add_right _ _)
    have hne : forestPtr + k ≠ addr := ne_of_lt h4
    simp [mem', memUpdate, memAt, hne, hforest k hk]
  have hidx' : ∀ j : Fin BATCH_SIZE, memAt mem' (idxPtr + j) = 0 := by
    intro j
    have hjlt : idxPtr + (j : Nat) < idxPtr + BATCH_SIZE :=
      Nat.add_lt_add_left j.isLt idxPtr
    have h2 : idxPtr + (j : Nat) < valPtr := lt_of_lt_of_le hjlt hiv
    have h3 : idxPtr + (j : Nat) < addr := lt_of_lt_of_le h2 (Nat.le_add_right _ _)
    have hne : idxPtr + (j : Nat) ≠ addr := ne_of_lt h3
    have hidx0 : memAt mem (idxPtr + j) = 0 := by
      simpa [idxPtr] using hidx j
    simp [mem', memUpdate, memAt, hne, hidx0]
  have hval' : memAt mem' (valPtr + i) = 1 := by
    have hval0 : memAt mem addr = 0 := by
      simpa [addr, valPtr] using hval i
    simp [mem', memUpdate, memAt, addr, hval0]
  have hrounds' : memAt mem' 0 = ROUNDS := by
    have hk : (0:Nat) < HEADER_SIZE := by decide
    have h := memUpdate_header_eq (mem:=mem) (addr:=addr) (val:=memAt mem addr + 1) hk haddr
    simpa [mem', addr] using h
  have hnodes' : memAt mem' 1 = N_NODES := by
    have hk : (1:Nat) < HEADER_SIZE := by decide
    have h := memUpdate_header_eq (mem:=mem) (addr:=addr) (val:=memAt mem addr + 1) hk haddr
    simpa [mem', addr] using h
  have hforest'' : ∀ k, k < N_NODES → memAt mem' (memAt mem' PTR_FOREST + k) = 0 := by
    intro k hk
    simp [hptr_forest, hforest' k hk]
  have hidx'' : memAt mem' (memAt mem' PTR_INP_IDX + i) = 0 := by
    simp [hptr_idx, hidx' i]
  have hval'' : memAt mem' (memAt mem' PTR_INP_VAL + i) = 1 := by
    simp [hptr_val, hval']
  have hspec1 : spec_kernel mem' i = iterHash ROUNDS 1 :=
    spec_kernel_uniform_val mem' i 1 hrounds' hnodes' hforest'' hidx'' hval''
  have hdiff : iterHash ROUNDS 0 ≠ iterHash ROUNDS 1 := iterHash_ne
  intro hEq
  apply hdiff
  have : iterHash ROUNDS 0 = iterHash ROUNDS 1 := by
    calc
      iterHash ROUNDS 0 = spec_kernel mem i := by symm; exact hspec0
      _ = spec_kernel mem' i := hEq.symm
      _ = iterHash ROUNDS 1 := hspec1
  exact this

lemma must_read_kernel_values_for_mem (p : Program) (hstraight : StraightLine p)
    (hcorrect : CorrectOn spec_kernel p MemSafeKernel) :
    ∀ mem, MemSafeKernel mem → KernelLayout mem → KernelSensitive mem → OutputDiffers mem →
      ∀ i : Fin BATCH_SIZE, (memAt mem PTR_INP_VAL + i) ∈ readWords p mem := by
  intro mem hsafe hlayout hks hdiff i
  by_contra hnot
  let addr := memAt mem PTR_INP_VAL + i
  let mem' := memUpdate mem addr (memAt mem addr + 1)
  have hagree : AgreeOnList (readWords p mem) mem mem' := by
    refine ⟨rfl, ?_⟩
    intro a ha
    have hne : a ≠ addr := by
      intro hEq
      apply hnot
      simpa [hEq] using ha
    simp [mem', memUpdate, memAt, hne]
  dsimp [KernelLayout] at hlayout
  rcases hlayout with ⟨hforest_ge, hidx_ge, hval_ge⟩
  have haddr_ge : HEADER_SIZE ≤ addr := Nat.le_trans hval_ge (Nat.le_add_right _ _)
  have hptr : memAt mem PTR_INP_VAL = memAt mem' PTR_INP_VAL := by
    have hk : PTR_INP_VAL < HEADER_SIZE := by decide
    have h := memUpdate_header_eq (mem:=mem) (addr:=addr) (val:=memAt mem addr + 1) hk haddr_ge
    simpa [mem'] using h.symm
  have hwrites : WritesOutput p mem := writes_output_of_correct p mem hcorrect ⟨hsafe, hlayout, hks, hdiff⟩
  have hrun : run p mem = run p mem' := by
    exact run_eq_of_agree p mem mem' hptr hagree hwrites
  have hlayout' : KernelLayout mem := by
    dsimp [KernelLayout]; exact ⟨hforest_ge, hidx_ge, hval_ge⟩
  have hsafe' : MemSafeKernel mem' := by
    have h := memSafeKernel_update_val (mem:=mem) (i:=i) hlayout' hsafe
    simpa [mem', addr] using h
  have hspec :
      spec_kernel mem = spec_kernel mem' := by
    calc
      spec_kernel mem = run p mem := by symm; exact hcorrect mem hsafe
      _ = run p mem' := hrun
      _ = spec_kernel mem' := by exact hcorrect mem' hsafe'
  have hdiff := hks i
  have hspeci : spec_kernel mem i = spec_kernel mem' i := by
    simpa using congrArg (fun f => f i) hspec
  exact hdiff hspeci.symm

lemma outputDiffers_uniform_zero (mem : Memory)
    (hunif : UniformZeroKernel mem) : OutputDiffers mem := by
  intro i
  rcases hunif with ⟨hsafe, hrounds, hnodes, _hbatch, _hheight, _hlayout, _hdisjoint,
    hforest, hidx, hval⟩
  have hspec0 : spec_kernel mem i = iterHash ROUNDS 0 := by
    have hidx0 : memAt mem (memAt mem PTR_INP_IDX + i) = 0 := hidx i
    have hval0 : memAt mem (memAt mem PTR_INP_VAL + i) = 0 := hval i
    exact spec_kernel_uniform_val mem i 0 hrounds hnodes hforest hidx0 hval0
  have hval0' : memAt mem (memAt mem PTR_INP_VAL + i) = 0 := hval i
  have hne : iterHash ROUNDS 0 ≠ 0 := iterHash_ne_zero
  simpa [hspec0, hval0'] using hne

lemma must_read_kernel_values_for_mem_machine (p : Program)
    (hstraight : StraightLine p)
    (hcorrect : CorrectOnMachine spec_kernel p MemSafeKernel) :
    ∀ mem, MemSafeKernel mem → KernelLayout mem → KernelSensitive mem → OutputDiffers mem →
      ∀ i : Fin BATCH_SIZE, (memAt mem PTR_INP_VAL + i) ∈ readWordsMachine p mem := by
  intro mem hsafe hlayout hks hdiff i
  by_contra hnot
  let addr := memAt mem PTR_INP_VAL + i
  let mem' := memUpdate mem addr (memAt mem addr + 1)
  have hagree : AgreeOnList (readWordsMachine p mem) mem mem' := by
    refine ⟨rfl, ?_⟩
    intro a ha
    have hne : a ≠ addr := by
      intro hEq
      apply hnot
      simpa [hEq] using ha
    simp [mem', memUpdate, memAt, hne]
  dsimp [KernelLayout] at hlayout
  rcases hlayout with ⟨hforest_ge, hidx_ge, hval_ge⟩
  have haddr_ge : HEADER_SIZE ≤ addr := Nat.le_trans hval_ge (Nat.le_add_right _ _)
  have hptr : memAt mem PTR_INP_VAL = memAt mem' PTR_INP_VAL := by
    have hk : PTR_INP_VAL < HEADER_SIZE := by decide
    have h := memUpdate_header_eq (mem:=mem) (addr:=addr) (val:=memAt mem addr + 1) hk haddr_ge
    simpa [mem', addr] using h.symm
  have hcorrect' : CorrectOn spec_kernel p MemSafeKernel :=
    CorrectOnMachine_to_CorrectOn spec_kernel p MemSafeKernel hcorrect
      (fun mem hmem => MachineTraceAgrees_of_StraightLine p hstraight mem)
  have hwrites : WritesOutput p mem :=
    writes_output_of_correct p mem hcorrect' ⟨hsafe, hlayout, hks, hdiff⟩
  have hrun : runMachine p mem = runMachine p mem' := by
    exact runMachine_eq_of_agree p mem mem' hstraight hptr hagree hwrites
  have hsafe' : MemSafeKernel mem' := by
    have h := memSafeKernel_update_val (mem:=mem) (i:=i) (by
      dsimp [KernelLayout]; exact ⟨hforest_ge, hidx_ge, hval_ge⟩) hsafe
    simpa [mem', addr] using h
  have hspec :
      spec_kernel mem = spec_kernel mem' := by
    calc
      spec_kernel mem = runMachine p mem := by symm; exact hcorrect mem hsafe
      _ = runMachine p mem' := hrun
      _ = spec_kernel mem' := by exact hcorrect mem' hsafe'
  have hdiff := hks i
  have hspeci : spec_kernel mem i = spec_kernel mem' i := by
    simpa using congrArg (fun f => f i) hspec
  exact hdiff hspeci.symm

lemma must_read_addr_machine (p : Program)
    (hstraight : StraightLine p)
    (hcorrect : CorrectOnMachine spec_kernel p MemSafeKernel) :
    ∀ mem, MemSafeKernel mem → WritesOutput p mem → ∀ addr, AddrSafe mem addr →
      (∃ i : Fin BATCH_SIZE,
        spec_kernel (memUpdate mem addr (memAt mem addr + 1)) i ≠ spec_kernel mem i) →
      addr ∈ readWordsMachine p mem := by
  intro mem hsafe hwrites addr haddr hsens
  by_contra hnot
  let mem' := memUpdate mem addr (memAt mem addr + 1)
  have hagree : AgreeOnList (readWordsMachine p mem) mem mem' := by
    refine ⟨rfl, ?_⟩
    intro a ha
    have hne : a ≠ addr := by
      intro hEq
      apply hnot
      simpa [hEq] using ha
    simp [mem', memUpdate, memAt, hne]
  have hptr : memAt mem PTR_INP_VAL = memAt mem' PTR_INP_VAL := by
    have hk : PTR_INP_VAL < HEADER_SIZE := by decide
    have h := memUpdate_header_eq (mem:=mem) (addr:=addr) (val:=memAt mem addr + 1) hk haddr.1
    simpa [mem'] using h.symm
  have hrun : runMachine p mem = runMachine p mem' := by
    exact runMachine_eq_of_agree p mem mem' hstraight hptr hagree hwrites
  have hsafe' : MemSafeKernel mem' := memSafeKernel_update_addr mem addr hsafe haddr
  rcases hsens with ⟨i, hdiff⟩
  have hspec :
      spec_kernel mem = spec_kernel mem' := by
    calc
      spec_kernel mem = runMachine p mem := by symm; exact hcorrect mem hsafe
      _ = runMachine p mem' := hrun
      _ = spec_kernel mem' := by exact hcorrect mem' hsafe'
  have hspeci : spec_kernel mem i = spec_kernel mem' i := by
    simpa using congrArg (fun f => f i) hspec
  exact hdiff hspeci.symm

lemma must_read_addr_machine_fuel (p : Program) (fuel : Nat)
    (hfull : fuel = p.program.length)
    (hstraight : StraightLine p)
    (hcorrect : CorrectOnMachineFuel spec_kernel p MemSafeKernel fuel) :
    ∀ mem, MemSafeKernel mem → WritesOutput p mem → ∀ addr, AddrSafe mem addr →
      (∃ i : Fin BATCH_SIZE,
        spec_kernel (memUpdate mem addr (memAt mem addr + 1)) i ≠ spec_kernel mem i) →
      addr ∈ readWordsMachineFuel p fuel mem := by
  intro mem hsafe hwrites addr haddr hsens
  by_contra hnot
  let mem' := memUpdate mem addr (memAt mem addr + 1)
  have hagree : AgreeOnList (readWordsMachineFuel p fuel mem) mem mem' := by
    refine ⟨rfl, ?_⟩
    intro a ha
    have hne : a ≠ addr := by
      intro hEq
      apply hnot
      simpa [hEq] using ha
    simp [mem', memUpdate, memAt, hne]
  have hptr : memAt mem PTR_INP_VAL = memAt mem' PTR_INP_VAL := by
    have hk : PTR_INP_VAL < HEADER_SIZE := by decide
    have h := memUpdate_header_eq (mem:=mem) (addr:=addr) (val:=memAt mem addr + 1) hk haddr.1
    simpa [mem'] using h.symm
  have hrun : runMachineFuel p fuel mem = runMachineFuel p fuel mem' := by
    exact runMachineFuel_eq_of_agree p fuel mem mem' hfull hstraight hptr hagree hwrites
  have hsafe' : MemSafeKernel mem' := memSafeKernel_update_addr mem addr hsafe haddr
  rcases hsens with ⟨i, hdiff⟩
  have hspec :
      spec_kernel mem = spec_kernel mem' := by
    calc
      spec_kernel mem = runMachineFuel p fuel mem := by symm; exact hcorrect mem hsafe
      _ = runMachineFuel p fuel mem' := hrun
      _ = spec_kernel mem' := by exact hcorrect mem' hsafe'
  have hspeci : spec_kernel mem i = spec_kernel mem' i := by
    simpa using congrArg (fun f => f i) hspec
  exact hdiff hspeci.symm

lemma must_read_kernel_values_for_mem_machine_fuel (p : Program) (fuel : Nat)
    (hfull : fuel = p.program.length)
    (hstraight : StraightLine p)
    (hcorrect : CorrectOnMachineFuel spec_kernel p MemSafeKernel fuel) :
    ∀ mem, MemSafeKernel mem → KernelLayout mem → KernelSensitive mem → OutputDiffers mem →
      ∀ i : Fin BATCH_SIZE, (memAt mem PTR_INP_VAL + i) ∈ readWordsMachineFuel p fuel mem := by
  intro mem hsafe hlayout hks hdiff i
  by_contra hnot
  let addr := memAt mem PTR_INP_VAL + i
  let mem' := memUpdate mem addr (memAt mem addr + 1)
  have hagree : AgreeOnList (readWordsMachineFuel p fuel mem) mem mem' := by
    refine ⟨rfl, ?_⟩
    intro a ha
    have hne : a ≠ addr := by
      intro hEq
      apply hnot
      simpa [hEq] using ha
    simp [mem', memUpdate, memAt, hne]
  dsimp [KernelLayout] at hlayout
  rcases hlayout with ⟨hforest_ge, hidx_ge, hval_ge⟩
  have haddr_ge : HEADER_SIZE ≤ addr := Nat.le_trans hval_ge (Nat.le_add_right _ _)
  have hptr : memAt mem PTR_INP_VAL = memAt mem' PTR_INP_VAL := by
    have hk : PTR_INP_VAL < HEADER_SIZE := by decide
    have h := memUpdate_header_eq (mem:=mem) (addr:=addr) (val:=memAt mem addr + 1) hk haddr_ge
    simpa [mem', addr] using h.symm
  have hcorrect' : CorrectOnMachine spec_kernel p MemSafeKernel :=
    fun mem hmem => by
      have := hcorrect mem hmem
      simpa [runMachineFuel, runMachine, runMemMachineFuel, runMemMachine, hfull] using this
  have hwrites : WritesOutput p mem :=
    writes_output_of_correct p mem hcorrect' ⟨hsafe, hlayout, hks, hdiff⟩
  have hrun : runMachineFuel p fuel mem = runMachineFuel p fuel mem' := by
    exact runMachineFuel_eq_of_agree p fuel mem mem' hfull hstraight hptr hagree hwrites
  have hsafe' : MemSafeKernel mem' := by
    have h := memSafeKernel_update_val (mem:=mem) (i:=i) (by
      dsimp [KernelLayout]; exact ⟨hforest_ge, hidx_ge, hval_ge⟩) hsafe
    simpa [mem', addr] using h
  have hspec :
      spec_kernel mem = spec_kernel mem' := by
    calc
      spec_kernel mem = runMachineFuel p fuel mem := by symm; exact hcorrect mem hsafe
      _ = runMachineFuel p fuel mem' := hrun
      _ = spec_kernel mem' := by exact hcorrect mem' hsafe'
  have hdiff := hks i
  have hspeci : spec_kernel mem i = spec_kernel mem' i := by
    simpa using congrArg (fun f => f i) hspec
  exact hdiff hspeci.symm

lemma must_read_kernel_values (p : Program) (hstraight : StraightLine p)
    (hcorrect : CorrectOn spec_kernel p MemSafeKernel) :
    ∀ i : Fin BATCH_SIZE,
      (memAt memUniform0 PTR_INP_VAL + i) ∈ readWords p memUniform0 := by
  intro i
  by_contra hnot
  have hagree : AgreeOnList (readWords p memUniform0) memUniform0 (memUniformVal i) := by
    refine ⟨rfl, ?_⟩
    intro a ha
    have hne : a ≠ memAt memUniform0 PTR_INP_VAL + i := by
      intro hEq
      apply hnot
      simpa [hEq] using ha
    simp [memUniformVal, memUpdate, memAt, hne]
  have hptr : memAt memUniform0 PTR_INP_VAL = memAt (memUniformVal i) PTR_INP_VAL := by
    simp [memUniformVal, memUpdate, memAt]
  have hrun :
      run p memUniform0 = run p (memUniformVal i) := by
    exact run_eq_of_agree p memUniform0 (memUniformVal i) hptr hagree
  have hspec :
      spec_kernel memUniform0 = spec_kernel (memUniformVal i) := by
    calc
      spec_kernel memUniform0 = run p memUniform0 := by symm; exact hcorrect _ memUniform0_safe
      _ = run p (memUniformVal i) := hrun
      _ = spec_kernel (memUniformVal i) := by exact hcorrect _ (memUniformVal_safe i)
  have hdiff := spec_kernel_diff_uniformVal i
  exact hdiff (by simpa using congrArg (fun f => f i) hspec)

lemma outputAddrs_subset_readWords_kernel (p : Program) (hstraight : StraightLine p)
    (hcorrect : CorrectOn spec_kernel p MemSafeKernel) :
    outputAddrs memUniform0 ⊆ (readWords p memUniform0).toFinset := by
  classical
  intro a ha
  rcases Finset.mem_image.mp (by simpa [outputAddrs] using ha) with ⟨i, hi, hEq⟩
  have hread : (memAt memUniform0 PTR_INP_VAL + i) ∈ readWords p memUniform0 :=
    must_read_kernel_values p hstraight hcorrect i
  have : a ∈ readWords p memUniform0 := by simpa [hEq] using hread
  exact List.mem_toFinset.mpr this

lemma outputAddrs_subset_readWords_kernel_for_mem (p : Program) (hstraight : StraightLine p)
    (hcorrect : CorrectOn spec_kernel p MemSafeKernel) :
    ∀ mem, MemSafeKernel mem → KernelLayout mem → KernelSensitive mem → OutputDiffers mem →
      outputAddrs mem ⊆ (readWords p mem).toFinset := by
  classical
  intro mem hsafe hlayout hks hdiff
  intro a ha
  rcases Finset.mem_image.mp (by simpa [outputAddrs] using ha) with ⟨i, hi, hEq⟩
  have hread : (memAt mem PTR_INP_VAL + i) ∈ readWords p mem :=
    must_read_kernel_values_for_mem p hstraight hcorrect mem hsafe hlayout hks hdiff i
  have : a ∈ readWords p mem := by simpa [hEq] using hread
  exact List.mem_toFinset.mpr this

lemma min_required_words_kernel (p : Program) (hstraight : StraightLine p)
    (hcorrect : CorrectOn spec_kernel p MemSafeKernel) :
    BATCH_SIZE ≤ readWordCount p memUniform0 := by
  have hsubset : outputAddrs memUniform0 ⊆ (readWords p memUniform0).toFinset :=
    outputAddrs_subset_readWords_kernel p hstraight hcorrect
  have hcard_le : (outputAddrs memUniform0).card ≤ (readWords p memUniform0).toFinset.card :=
    Finset.card_le_card hsubset
  have hlen : (readWords p memUniform0).toFinset.card ≤ (readWords p memUniform0).length :=
    List.toFinset_card_le (l := readWords p memUniform0)
  have hcard : (outputAddrs memUniform0).card = BATCH_SIZE := outputAddrs_card memUniform0
  have : BATCH_SIZE ≤ (readWords p memUniform0).length := by
    exact le_trans (by simpa [hcard] using hcard_le) hlen
  simpa [readWordCount] using this

lemma min_required_words_kernel_for_mem (p : Program) (hstraight : StraightLine p)
    (hcorrect : CorrectOn spec_kernel p MemSafeKernel) :
    ∀ mem, MemSafeKernel mem → KernelLayout mem → KernelSensitive mem → OutputDiffers mem →
      BATCH_SIZE ≤ readWordCount p mem := by
  intro mem hsafe hlayout hks hdiff
  have hsubset : outputAddrs mem ⊆ (readWords p mem).toFinset :=
    outputAddrs_subset_readWords_kernel_for_mem p hstraight hcorrect mem hsafe hlayout hks hdiff
  have hcard_le : (outputAddrs mem).card ≤ (readWords p mem).toFinset.card :=
    Finset.card_le_card hsubset
  have hlen : (readWords p mem).toFinset.card ≤ (readWords p mem).length :=
    List.toFinset_card_le (l := readWords p mem)
  have hcard : (outputAddrs mem).card = BATCH_SIZE := outputAddrs_card mem
  have : BATCH_SIZE ≤ (readWords p mem).length := by
    exact le_trans (by simpa [hcard] using hcard_le) hlen
  simpa [readWordCount] using this

lemma min_required_words_kernel_for_mem_machine (p : Program)
    (hstraight : StraightLine p)
    (hcorrect : CorrectOnMachine spec_kernel p MemSafeKernel) :
    ∀ mem, MemSafeKernel mem → KernelLayout mem → KernelSensitive mem → OutputDiffers mem →
      BATCH_SIZE ≤ readWordCountMachine p mem := by
  intro mem hsafe hlayout hks hdiff
  have hsubset : outputAddrs mem ⊆ (readWordsMachine p mem).toFinset := by
    classical
    intro a ha
    rcases Finset.mem_image.mp (by simpa [outputAddrs] using ha) with ⟨i, hi, hEq⟩
    have hread : (memAt mem PTR_INP_VAL + i) ∈ readWordsMachine p mem :=
      must_read_kernel_values_for_mem_machine p hstraight hcorrect mem hsafe hlayout hks hdiff i
    have : a ∈ readWordsMachine p mem := by simpa [hEq] using hread
    exact List.mem_toFinset.mpr this
  have hcard_le : (outputAddrs mem).card ≤ (readWordsMachine p mem).toFinset.card :=
    Finset.card_le_card hsubset
  have hlen : (readWordsMachine p mem).toFinset.card ≤ (readWordsMachine p mem).length :=
    List.toFinset_card_le (l := readWordsMachine p mem)
  have hcard : (outputAddrs mem).card = BATCH_SIZE := outputAddrs_card mem
  have : BATCH_SIZE ≤ (readWordsMachine p mem).length := by
    exact le_trans (by simpa [hcard] using hcard_le) hlen
  simpa [readWordCountMachine] using this

lemma min_required_words_adversaryK_machine (p : Program)
    (hstraight : StraightLine p)
    (hcorrect : CorrectOnMachine spec_kernel p MemSafeKernel) :
    ∀ mem, MemSafeKernel mem → WritesOutput p mem → ∀ k, AdversaryK mem k →
      k * BATCH_SIZE * memAt mem 0 ≤ readWordCountMachine p mem := by
  intro mem hsafe hwrites k hadv
  rcases hadv with ⟨L, hL, hlen⟩
  rcases hL with ⟨hnodup, haddr, hsens⟩
  have hsubset : L.toFinset ⊆ (readWordsMachine p mem).toFinset := by
    classical
    intro a ha
    have ha' : a ∈ L := by
      exact List.mem_toFinset.mp ha
    have hsafe_addr : AddrSafe mem a := haddr a ha'
    have hsens' : ∃ i : Fin BATCH_SIZE,
        spec_kernel (memUpdate mem a (memAt mem a + 1)) i ≠ spec_kernel mem i := hsens a ha'
    have hread : a ∈ readWordsMachine p mem :=
      must_read_addr_machine p hstraight hcorrect mem hsafe hwrites a hsafe_addr hsens'
    exact List.mem_toFinset.mpr hread
  have hcard_le : L.toFinset.card ≤ (readWordsMachine p mem).toFinset.card :=
    Finset.card_le_card hsubset
  have hlen' : (readWordsMachine p mem).toFinset.card ≤ (readWordsMachine p mem).length :=
    List.toFinset_card_le (l := readWordsMachine p mem)
  have hcard : L.toFinset.card = L.length := by
    simpa using List.toFinset_card_of_nodup hnodup
  have hlen_le : L.length ≤ (readWordsMachine p mem).toFinset.card := by
    simpa [hcard] using hcard_le
  have hprod_le : k * BATCH_SIZE * memAt mem 0 ≤ (readWordsMachine p mem).toFinset.card := by
    simpa [hlen] using hlen_le
  have hfinal : k * BATCH_SIZE * memAt mem 0 ≤ (readWordsMachine p mem).length :=
    le_trans hprod_le hlen'
  simpa [readWordCountMachine] using hfinal

lemma min_required_words_adversaryK_machine_fuel (p : Program) (fuel : Nat)
    (hfull : fuel = p.program.length)
    (hstraight : StraightLine p)
    (hcorrect : CorrectOnMachineFuel spec_kernel p MemSafeKernel fuel) :
    ∀ mem, MemSafeKernel mem → WritesOutput p mem → ∀ k, AdversaryK mem k →
      k * BATCH_SIZE * memAt mem 0 ≤ readWordCountMachineFuel p fuel mem := by
  intro mem hsafe hwrites k hadv
  rcases hadv with ⟨L, hL, hlen⟩
  rcases hL with ⟨hnodup, haddr, hsens⟩
  have hsubset : L.toFinset ⊆ (readWordsMachineFuel p fuel mem).toFinset := by
    classical
    intro a ha
    have ha' : a ∈ L := by
      exact List.mem_toFinset.mp ha
    have hsafe_addr : AddrSafe mem a := haddr a ha'
    have hsens' : ∃ i : Fin BATCH_SIZE,
        spec_kernel (memUpdate mem a (memAt mem a + 1)) i ≠ spec_kernel mem i := hsens a ha'
    have hread : a ∈ readWordsMachineFuel p fuel mem :=
      must_read_addr_machine_fuel p fuel hfull hstraight hcorrect mem hsafe hwrites a hsafe_addr hsens'
    exact List.mem_toFinset.mpr hread
  have hcard_le : L.toFinset.card ≤ (readWordsMachineFuel p fuel mem).toFinset.card :=
    Finset.card_le_card hsubset
  have hlen' : (readWordsMachineFuel p fuel mem).toFinset.card ≤ (readWordsMachineFuel p fuel mem).length :=
    List.toFinset_card_le (l := readWordsMachineFuel p fuel mem)
  have hcard : L.toFinset.card = L.length := by
    simpa using List.toFinset_card_of_nodup hnodup
  have hlen_le : L.length ≤ (readWordsMachineFuel p fuel mem).toFinset.card := by
    simpa [hcard] using hcard_le
  have hprod_le : k * BATCH_SIZE * memAt mem 0 ≤ (readWordsMachineFuel p fuel mem).toFinset.card := by
    simpa [hlen] using hlen_le
  have hfinal : k * BATCH_SIZE * memAt mem 0 ≤ (readWordsMachineFuel p fuel mem).length :=
    le_trans hprod_le hlen'
  simpa [readWordCountMachineFuel] using hfinal

lemma min_required_words_kernel_for_mem_machine_fuel (p : Program) (fuel : Nat)
    (hfull : fuel = p.program.length)
    (hstraight : StraightLine p)
    (hcorrect : CorrectOnMachineFuel spec_kernel p MemSafeKernel fuel) :
    ∀ mem, MemSafeKernel mem → KernelLayout mem → KernelSensitive mem → OutputDiffers mem →
      BATCH_SIZE ≤ readWordCountMachineFuel p fuel mem := by
  intro mem hsafe hlayout hks hdiff
  have hsubset : outputAddrs mem ⊆ (readWordsMachineFuel p fuel mem).toFinset := by
    classical
    intro a ha
    rcases Finset.mem_image.mp (by simpa [outputAddrs] using ha) with ⟨i, hi, hEq⟩
    have hread : (memAt mem PTR_INP_VAL + i) ∈ readWordsMachineFuel p fuel mem :=
      must_read_kernel_values_for_mem_machine_fuel p fuel hfull hstraight hcorrect mem hsafe hlayout hks hdiff i
    have : a ∈ readWordsMachineFuel p fuel mem := by simpa [hEq] using hread
    exact List.mem_toFinset.mpr this
  have hcard_le : (outputAddrs mem).card ≤ (readWordsMachineFuel p fuel mem).toFinset.card :=
    Finset.card_le_card hsubset
  have hlen : (readWordsMachineFuel p fuel mem).toFinset.card ≤ (readWordsMachineFuel p fuel mem).length :=
    List.toFinset_card_le (l := readWordsMachineFuel p fuel mem)
  have hcard : (outputAddrs mem).card = BATCH_SIZE := outputAddrs_card mem
  have : BATCH_SIZE ≤ (readWordsMachineFuel p fuel mem).length := by
    exact le_trans (by simpa [hcard] using hcard_le) hlen
  simpa [readWordCountMachineFuel] using this

lemma spec_values_diff {mem : Memory} {base : Nat} {i : Fin BATCH_SIZE} :
    let addr := base + i
    spec_values (memUpdate mem addr (memAt mem addr + 1)) i ≠ spec_values mem i := by
  intro addr
  simp [spec_values, outputOf, memUpdate, addr]

lemma must_read_values (p : Program) (hstraight : StraightLine p)
    (hcorrect : CorrectOn spec_values p MemSafeValues) :
    ∀ mem, MemSafeValues mem → WritesOutput p mem → ∀ i : Fin BATCH_SIZE,
      (memAt mem PTR_INP_VAL + i) ∈ readWords p mem := by
  intro mem hsafe hwrites i
  by_contra hnot
  have hagree : AgreeOnList (readWords p mem) mem
      (memUpdate mem (memAt mem PTR_INP_VAL + i) (memAt mem (memAt mem PTR_INP_VAL + i) + 1)) := by
    refine ⟨rfl, ?_⟩
    intro a ha
    have hne : a ≠ memAt mem PTR_INP_VAL + i := by
      intro hEq
      apply hnot
      simpa [hEq] using ha
    simp [memUpdate, memAt, hne]
  have hptr : memAt mem PTR_INP_VAL =
      memAt (memUpdate mem (memAt mem PTR_INP_VAL + i) (memAt mem (memAt mem PTR_INP_VAL + i) + 1)) PTR_INP_VAL := by
    simp [memUpdate, memAt]
  have hrun :
      run p mem =
      run p (memUpdate mem (memAt mem PTR_INP_VAL + i) (memAt mem (memAt mem PTR_INP_VAL + i) + 1)) := by
    exact run_eq_of_agree p mem
      (memUpdate mem (memAt mem PTR_INP_VAL + i) (memAt mem (memAt mem PTR_INP_VAL + i) + 1))
      hptr hagree hwrites
  have hspec :
      spec_values mem =
      spec_values (memUpdate mem (memAt mem PTR_INP_VAL + i) (memAt mem (memAt mem PTR_INP_VAL + i) + 1)) := by
    calc
      spec_values mem = run p mem := by symm; exact hcorrect mem hsafe
      _ = run p (memUpdate mem (memAt mem PTR_INP_VAL + i) (memAt mem (memAt mem PTR_INP_VAL + i) + 1)) := hrun
      _ = spec_values (memUpdate mem (memAt mem PTR_INP_VAL + i) (memAt mem (memAt mem PTR_INP_VAL + i) + 1)) := by
        have hptr' : memAt mem PTR_INP_VAL =
            memAt (memUpdate mem (memAt mem PTR_INP_VAL + i)
              (memAt mem (memAt mem PTR_INP_VAL + i) + 1)) PTR_INP_VAL := by
          simp [memUpdate, memAt]
        have hsafe' : MemSafeValues (memUpdate mem (memAt mem PTR_INP_VAL + i)
            (memAt mem (memAt mem PTR_INP_VAL + i) + 1)) :=
          memSafeValues_of_eq_ptr mem _ rfl hptr' hsafe
        exact hcorrect _ hsafe'
  have hdiff := spec_values_diff (mem:=mem) (base:=memAt mem PTR_INP_VAL) (i:=i)
  exact hdiff (by simpa using congrArg (fun f => f i) hspec)

lemma must_read_values_machine (p : Program)
    (hstraight : StraightLine p)
    (hcorrect : CorrectOnMachine spec_values p MemSafeValues) :
    ∀ mem, MemSafeValues mem → WritesOutput p mem → ∀ i : Fin BATCH_SIZE,
      (memAt mem PTR_INP_VAL + i) ∈ readWordsMachine p mem := by
  intro mem hsafe hwrites i
  by_contra hnot
  let addr := memAt mem PTR_INP_VAL + i
  let mem' := memUpdate mem addr (memAt mem addr + 1)
  have hagree : AgreeOnList (readWordsMachine p mem) mem mem' := by
    refine ⟨rfl, ?_⟩
    intro a ha
    have hne : a ≠ addr := by
      intro hEq
      apply hnot
      simpa [hEq] using ha
    simp [mem', memUpdate, memAt, hne]
  have hptr : memAt mem PTR_INP_VAL = memAt mem' PTR_INP_VAL := by
    simp [mem', memUpdate, memAt]
  have hrun : runMachine p mem = runMachine p mem' := by
    exact runMachine_eq_of_agree p mem mem' hstraight hptr hagree hwrites
  have hspec :
      spec_values mem = spec_values mem' := by
    calc
      spec_values mem = runMachine p mem := by symm; exact hcorrect mem hsafe
      _ = runMachine p mem' := hrun
      _ = spec_values mem' := by
        have hptr' : memAt mem PTR_INP_VAL = memAt mem' PTR_INP_VAL := by
          simp [mem', memUpdate, memAt]
        have hsafe' : MemSafeValues mem' :=
          memSafeValues_of_eq_ptr mem mem' rfl hptr' hsafe
        exact hcorrect mem' hsafe'
  have hdiff := spec_values_diff (mem:=mem) (base:=memAt mem PTR_INP_VAL) (i:=i)
  exact hdiff (by simpa using congrArg (fun f => f i) hspec)

lemma must_read_values_machine_fuel (p : Program) (fuel : Nat)
    (hfull : fuel = p.program.length)
    (hstraight : StraightLine p)
    (hcorrect : CorrectOnMachineFuel spec_values p MemSafeValues fuel) :
    ∀ mem, MemSafeValues mem → WritesOutput p mem → ∀ i : Fin BATCH_SIZE,
      (memAt mem PTR_INP_VAL + i) ∈ readWordsMachineFuel p fuel mem := by
  intro mem hsafe hwrites i
  by_contra hnot
  let addr := memAt mem PTR_INP_VAL + i
  let mem' := memUpdate mem addr (memAt mem addr + 1)
  have hagree : AgreeOnList (readWordsMachineFuel p fuel mem) mem mem' := by
    refine ⟨rfl, ?_⟩
    intro a ha
    have hne : a ≠ addr := by
      intro hEq
      apply hnot
      simpa [hEq] using ha
    simp [mem', memUpdate, memAt, hne]
  have hptr : memAt mem PTR_INP_VAL = memAt mem' PTR_INP_VAL := by
    simp [mem', memUpdate, memAt]
  have hrun : runMachineFuel p fuel mem = runMachineFuel p fuel mem' := by
    exact runMachineFuel_eq_of_agree p fuel mem mem' hfull hstraight hptr hagree hwrites
  have hspec :
      spec_values mem = spec_values mem' := by
    calc
      spec_values mem = runMachineFuel p fuel mem := by symm; exact hcorrect mem hsafe
      _ = runMachineFuel p fuel mem' := hrun
      _ = spec_values mem' := by
        have hptr' : memAt mem PTR_INP_VAL = memAt mem' PTR_INP_VAL := by
          simp [mem', memUpdate, memAt]
        have hsafe' : MemSafeValues mem' :=
          memSafeValues_of_eq_ptr mem mem' rfl hptr' hsafe
        exact hcorrect mem' hsafe'
  have hdiff := spec_values_diff (mem:=mem) (base:=memAt mem PTR_INP_VAL) (i:=i)
  exact hdiff (by simpa using congrArg (fun f => f i) hspec)

lemma outputAddrs_subset_readWords (p : Program) (hstraight : StraightLine p)
    (hcorrect : CorrectOn spec_values p MemSafeValues) (mem : Memory)
    (hsafe : MemSafeValues mem) (hwrites : WritesOutput p mem) :
    outputAddrs mem ⊆ (readWords p mem).toFinset := by
  classical
  intro a ha
  rcases Finset.mem_image.mp (by simpa [outputAddrs] using ha) with ⟨i, hi, hEq⟩
  have hread : (memAt mem PTR_INP_VAL + i) ∈ readWords p mem :=
    must_read_values p hstraight hcorrect mem hsafe hwrites i
  have : a ∈ readWords p mem := by simpa [hEq] using hread
  exact List.mem_toFinset.mpr this

lemma min_required_words_values (p : Program) (hstraight : StraightLine p)
    (hcorrect : CorrectOn spec_values p MemSafeValues) :
    ∀ mem, MemSafeValues mem → WritesOutput p mem → BATCH_SIZE ≤ readWordCount p mem := by
  intro mem hsafe hwrites
  have hsubset : outputAddrs mem ⊆ (readWords p mem).toFinset :=
    outputAddrs_subset_readWords p hstraight hcorrect mem hsafe hwrites
  have hcard_le : (outputAddrs mem).card ≤ (readWords p mem).toFinset.card :=
    Finset.card_le_card hsubset
  have hlen : (readWords p mem).toFinset.card ≤ (readWords p mem).length :=
    List.toFinset_card_le (l := readWords p mem)
  have hcard : (outputAddrs mem).card = BATCH_SIZE := outputAddrs_card mem
  have : BATCH_SIZE ≤ (readWords p mem).length := by
    exact le_trans (by simpa [hcard] using hcard_le) hlen
  simpa [readWordCount] using this

lemma min_required_words_values_machine (p : Program)
    (hcorrect : CorrectOnMachine spec_values p MemSafeValues) :
    ∀ mem, MemSafeValues mem → BATCH_SIZE ≤ readWordCountMachine p mem := by
  intro mem hsafe
  have hsubset : outputAddrs mem ⊆ (readWordsMachine p mem).toFinset := by
    classical
    intro a ha
    rcases Finset.mem_image.mp (by simpa [outputAddrs] using ha) with ⟨i, hi, hEq⟩
    have hread : (memAt mem PTR_INP_VAL + i) ∈ readWordsMachine p mem :=
      must_read_values_machine p hcorrect mem hsafe i
    have : a ∈ readWordsMachine p mem := by simpa [hEq] using hread
    exact List.mem_toFinset.mpr this
  have hcard_le : (outputAddrs mem).card ≤ (readWordsMachine p mem).toFinset.card :=
    Finset.card_le_card hsubset
  have hlen : (readWordsMachine p mem).toFinset.card ≤ (readWordsMachine p mem).length :=
    List.toFinset_card_le (l := readWordsMachine p mem)
  have hcard : (outputAddrs mem).card = BATCH_SIZE := outputAddrs_card mem
  have : BATCH_SIZE ≤ (readWordsMachine p mem).length := by
    exact le_trans (by simpa [hcard] using hcard_le) hlen
  simpa [readWordCountMachine] using this

lemma min_required_words_values_machine_fuel (p : Program) (fuel : Nat)
    (hcorrect : CorrectOnMachineFuel spec_values p MemSafeValues fuel) :
    ∀ mem, MemSafeValues mem → BATCH_SIZE ≤ readWordCountMachineFuel p fuel mem := by
  intro mem hsafe
  have hsubset : outputAddrs mem ⊆ (readWordsMachineFuel p fuel mem).toFinset := by
    classical
    intro a ha
    rcases Finset.mem_image.mp (by simpa [outputAddrs] using ha) with ⟨i, hi, hEq⟩
    have hread : (memAt mem PTR_INP_VAL + i) ∈ readWordsMachineFuel p fuel mem :=
      must_read_values_machine_fuel p fuel hfull hstraight hcorrect mem hsafe i
    have : a ∈ readWordsMachineFuel p fuel mem := by simpa [hEq] using hread
    exact List.mem_toFinset.mpr this
  have hcard_le : (outputAddrs mem).card ≤ (readWordsMachineFuel p fuel mem).toFinset.card :=
    Finset.card_le_card hsubset
  have hlen : (readWordsMachineFuel p fuel mem).toFinset.card ≤ (readWordsMachineFuel p fuel mem).length :=
    List.toFinset_card_le (l := readWordsMachineFuel p fuel mem)
  have hcard : (outputAddrs mem).card = BATCH_SIZE := outputAddrs_card mem
  have : BATCH_SIZE ≤ (readWordsMachineFuel p fuel mem).length := by
    exact le_trans (by simpa [hcard] using hcard_le) hlen
  simpa [readWordCountMachineFuel] using this
/-! ### PC-trace bridge for straight-line programs -/

def coreEqNoPc (c1 c2 : Core) : Prop :=
  c1.id = c2.id ∧
  c1.scratch = c2.scratch ∧
  c1.trace_buf = c2.trace_buf ∧
  c1.state = c2.state

lemma coreEqNoPc_refl (c : Core) : coreEqNoPc c c := by
  exact ⟨rfl, rfl, rfl, rfl⟩

lemma listAll_forall {α : Type} {p : α → Prop} {l : List α} (h : List.Forall p l) :
    ∀ a ∈ l, p a := by
  intro a ha
  induction h with
  | nil =>
      cases ha
  | cons hhead htail ih =>
      cases ha with
      | head => exact hhead
      | tail ha' => exact ih ha'

lemma execFlowSlot_eq_of_coreEq (enablePause : Bool) (core1 core2 : Core)
    (s : Nat → Nat) (slot : FlowSlot)
    (hstraight : flowSlotStraight slot) (hcore : coreEqNoPc core1 core2) :
    coreEqNoPc (execFlowSlot enablePause core1 s slot).1
      (execFlowSlot enablePause core2 s slot).1 ∧
    (execFlowSlot enablePause core1 s slot).2 = (execFlowSlot enablePause core2 s slot).2 := by
  cases slot <;> simp [flowSlotStraight] at hstraight
  all_goals
    rcases hcore with ⟨hid, hscratch, htrace, hstate⟩
    simp [execFlowSlot, hid, hscratch, htrace, hstate, coreEqNoPc_refl, coreEqNoPc]

lemma execFlowSlots_eq_of_coreEq (enablePause : Bool) (core1 core2 : Core)
    (s : Nat → Nat) (slots : List FlowSlot)
    (hstraight : ∀ slot ∈ slots, flowSlotStraight slot)
    (hcore : coreEqNoPc core1 core2) :
    coreEqNoPc
        (slots.foldl
          (fun acc slot =>
            let (c, ws) := acc
            let (c', ws') := execFlowSlot enablePause c s slot
            (c', ws ++ ws'))
          (core1, [])).1
        (slots.foldl
          (fun acc slot =>
            let (c, ws) := acc
            let (c', ws') := execFlowSlot enablePause c s slot
            (c', ws ++ ws'))
          (core2, [])).1 ∧
    (slots.foldl
          (fun acc slot =>
            let (c, ws) := acc
            let (c', ws') := execFlowSlot enablePause c s slot
            (c', ws ++ ws'))
          (core1, [])).2
      =
    (slots.foldl
          (fun acc slot =>
            let (c, ws) := acc
            let (c', ws') := execFlowSlot enablePause c s slot
            (c', ws ++ ws'))
          (core2, [])).2 := by
  induction slots with
  | nil =>
      simp [coreEqNoPc_refl, coreEqNoPc]
  | cons slot rest ih =>
      have hslot : flowSlotStraight slot := hstraight slot (by simp)
      have hrest : ∀ s ∈ rest, flowSlotStraight s := by
        intro s hs
        exact hstraight s (by simp [hs])
      have hstep := execFlowSlot_eq_of_coreEq enablePause core1 core2 s slot hslot hcore
      rcases hstep with ⟨hcore', hwrites⟩
      have ih' := ih hrest hcore'
      rcases ih' with ⟨hcore'', hwrites'⟩
      simp [List.foldl, hcore'', hwrites, hwrites']

lemma execInstructionTrace_eq_of_coreEq (mem : Memory) (core1 core2 : Core)
    (instr : Instruction) (hstraight : instrStraight instr)
    (hcore : coreEqNoPc core1 core2) :
    execInstructionTrace mem core1 instr = execInstructionTrace mem core2 instr := by
  rcases hcore with ⟨hid, hscratch, htrace, hstate⟩
  have hreads : instr.load.map (loadAddrs core1.scratch) =
      instr.load.map (loadAddrs core2.scratch) := by
    simp [hscratch]
  have hflow :
      coreEqNoPc
        (instr.flow.foldl
          (fun acc slot =>
            let (c, ws) := acc
            let (c', ws') := execFlowSlot false c core1.scratch slot
            (c', ws ++ ws'))
          (core1, [])).1
        (instr.flow.foldl
          (fun acc slot =>
            let (c, ws) := acc
            let (c', ws') := execFlowSlot false c core2.scratch slot
            (c', ws ++ ws'))
          (core2, [])).1 ∧
      (instr.flow.foldl
          (fun acc slot =>
            let (c, ws) := acc
            let (c', ws') := execFlowSlot false c core1.scratch slot
            (c', ws ++ ws'))
          (core1, [])).2
        =
      (instr.flow.foldl
          (fun acc slot =>
            let (c, ws) := acc
            let (c', ws') := execFlowSlot false c core2.scratch slot
            (c', ws ++ ws'))
          (core2, [])).2 := by
    have hflow' : ∀ slot ∈ instr.flow, flowSlotStraight slot := by
      exact listAll_forall (by simpa using hstraight)
    exact execFlowSlots_eq_of_coreEq false core1 core2 core1.scratch instr.flow hflow' hcore
  rcases hflow with ⟨hcore', hflow_writes⟩
  -- execInstruction is deterministic given scratch/core equality
  simp [execInstructionTrace, execInstruction, hreads, hscratch, hid, htrace, hstate,
    hflow_writes, hcore', coreEqNoPc]

lemma runTraceAux_eq_of_coreEq :
    ∀ prog mem core1 core2,
      (∀ instr ∈ prog, instrStraight instr) →
      coreEqNoPc core1 core2 →
      runTraceAux prog mem core1 = runTraceAux prog mem core2 := by
  intro prog mem core1 core2 hstraight hcore
  induction prog generalizing mem core1 core2 with
  | nil =>
      simp [runTraceAux]
  | cons instr rest ih =>
      have hinstr : instrStraight instr := hstraight instr (by simp)
      have hrest : ∀ i ∈ rest, instrStraight i := by
        intro i hi; exact hstraight i (by simp [hi])
      have hstep := execInstructionTrace_eq_of_coreEq mem core1 core2 instr hinstr hcore
      -- after rewriting, both sides are identical
      simp [runTraceAux, hstep]

def MachineTraceAgrees (p : Program) (mem : Memory) : Prop :=
  runMachineTrace p mem = runTrace p mem

theorem MachineTraceAgrees_of_StraightLine (p : Program) (hstraight : StraightLine p) :
    ∀ mem, MachineTraceAgrees p mem := by
  intro mem
  cases p with
  | mk prog initScratch =>
      -- reduce to a statement about the concrete program list
      simp [MachineTraceAgrees, runMachineTrace, runTrace] at *
      -- show runMachineTraceAux matches runTraceAux on the list
      have hstraight' : ∀ instr ∈ prog, instrStraight instr := hstraight
      -- induction on program list
      induction prog generalizing mem with
      | nil =>
          simp [runMachineTraceAux, runMachineTraceFuel, runTraceAux, initMachine, initCore]
      | cons instr rest ih =>
          -- unfold one machine step and one trace step
          have hinstr : instrStraight instr := hstraight' instr (by simp)
          have hrest : ∀ i ∈ rest, instrStraight i := by
            intro i hi; exact hstraight' i (by simp [hi])
          -- simplify stepMachineTrace on single-core machine
          simp [runMachineTraceAux, initMachine, initCore, anyRunning, stepMachineTrace,
            stepCoreTrace, fetch, runTraceAux] at *
          -- use straight-line invariance to ignore pc differences
          have hcore : coreEqNoPc (initCore ⟨instr :: rest, initScratch⟩)
              ({ initCore ⟨instr :: rest, initScratch⟩ with pc := (initCore ⟨instr :: rest, initScratch⟩).pc + 1 }) := by
            simp [coreEqNoPc, initCore]
          have hstep := execInstructionTrace_eq_of_coreEq mem
            ({ initCore ⟨instr :: rest, initScratch⟩ with pc := (initCore ⟨instr :: rest, initScratch⟩).pc + 1 })
            (initCore ⟨instr :: rest, initScratch⟩) instr hinstr hcore
          -- finish by rewriting and applying IH
          simp [hstep, ih mem hrest]

lemma runMachine_eq_run (p : Program) (mem : Memory)
    (htrace : MachineTraceAgrees p mem) : runMachine p mem = run p mem := by
  simp [MachineTraceAgrees, runMachine, run, runMemMachine, runMem, htrace]

lemma readWordCountMachine_eq (p : Program) (mem : Memory)
    (htrace : MachineTraceAgrees p mem) :
    readWordCountMachine p mem = readWordCount p mem := by
  simp [MachineTraceAgrees, readWordCountMachine, readWordsMachine, readOpsMachine,
    readWordCount, readWords, readOps, htrace]

lemma runMachine_eq_of_agree (p : Program) (mem1 mem2 : Memory)
    (hstraight : StraightLine p)
    (hptr : memAt mem1 PTR_INP_VAL = memAt mem2 PTR_INP_VAL)
    (h : AgreeOnList (readWordsMachine p mem1) mem1 mem2)
    (hwrites : WritesOutput p mem1) :
    runMachine p mem1 = runMachine p mem2 := by
  have htrace1 : MachineTraceAgrees p mem1 := MachineTraceAgrees_of_StraightLine p hstraight mem1
  have htrace2 : MachineTraceAgrees p mem2 := MachineTraceAgrees_of_StraightLine p hstraight mem2
  have hread1 : readWordsMachine p mem1 = readWords p mem1 := by
    simp [MachineTraceAgrees, readWordsMachine, readOpsMachine, readWords, readOps, htrace1]
  have hagree' : AgreeOnList (readWords p mem1) mem1 mem2 := by
    simpa [hread1] using h
  have hrun : run p mem1 = run p mem2 := run_eq_of_agree p mem1 mem2 hptr hagree' hwrites
  have hrun1 : runMachine p mem1 = run p mem1 := runMachine_eq_run p mem1 htrace1
  have hrun2 : runMachine p mem2 = run p mem2 := runMachine_eq_run p mem2 htrace2
  calc
    runMachine p mem1 = run p mem1 := hrun1
    _ = run p mem2 := hrun
    _ = runMachine p mem2 := by symm; exact hrun2

lemma runMachineFuel_eq_of_agree (p : Program) (fuel : Nat) (mem1 mem2 : Memory)
    (hfull : fuel = p.program.length)
    (hstraight : StraightLine p)
    (hptr : memAt mem1 PTR_INP_VAL = memAt mem2 PTR_INP_VAL)
    (h : AgreeOnList (readWordsMachineFuel p fuel mem1) mem1 mem2)
    (hwrites : WritesOutput p mem1) :
    runMachineFuel p fuel mem1 = runMachineFuel p fuel mem2 := by
  have hread : readWordsMachineFuel p fuel mem1 = readWordsMachine p mem1 := by
    simp [readWordsMachineFuel, readOpsMachineFuel, runMachineTraceFuel, hfull, runMachineTrace,
      readWordsMachine, readOpsMachine]
  have hagree' : AgreeOnList (readWordsMachine p mem1) mem1 mem2 := by
    simpa [hread] using h
  have hrun := runMachine_eq_of_agree p mem1 mem2 hstraight hptr hagree' hwrites
  simp [runMachineFuel, runMachine, runMemMachineFuel, runMemMachine, hfull, hrun]

lemma CorrectOnMachine_to_CorrectOn (spec : Memory → Output) (p : Program) (memOk : Memory → Prop)
    (hcorrect : CorrectOnMachine spec p memOk)
    (htrace : ∀ mem, memOk mem → MachineTraceAgrees p mem) :
    CorrectOn spec p memOk := by
  intro mem hmem
  have htr := htrace mem hmem
  have hrun : runMachine p mem = run p mem := runMachine_eq_run p mem htr
  simpa [hrun] using hcorrect mem hmem

/-! ### Derived load-op lower bound from readOps_bound -/

lemma loadAddrs_length_le (s : Nat → Nat) (slot : LoadSlot) :
    (loadAddrs s slot).length ≤ VLEN := by
  cases slot <;> simp [loadAddrs, VLEN]

lemma readOps_bound_aux :
    ∀ prog mem core, ∀ op ∈ (runTraceAux prog mem core).2, op.length ≤ VLEN := by
  intro prog mem core
  induction prog with
  | nil =>
      intro op hmem
      simp at hmem
  | cons instr rest ih =>
      intro op hop
      simp [runTraceAux] at hop
      rcases hop with hop | hop
      · -- op is from current instruction
        rcases hop with ⟨slot, hslot, rfl⟩
        exact loadAddrs_length_le _ _
      · -- op is from remaining program
        exact ih _ _ _ op hop

lemma readOps_bound (p : Program) (mem : Memory) :
    ∀ op ∈ readOps p mem, op.length ≤ VLEN := by
  simpa [readOps, runTrace] using (readOps_bound_aux p.program mem (initCore p))

lemma length_join_le (ops : List (List Nat))
    (h : ∀ op ∈ ops, op.length ≤ VLEN) :
    (listJoin ops).length ≤ VLEN * ops.length := by
  induction ops with
  | nil =>
      simp
  | cons op ops ih =>
      have hop : op.length ≤ VLEN := h op (by simp)
      have hrest : ∀ o ∈ ops, o.length ≤ VLEN := by
        intro o ho
        exact h o (by simp [ho])
      have ih' := ih hrest
      calc
        (listJoin (op :: ops)).length = op.length + (listJoin ops).length := by simp
        _ ≤ VLEN + VLEN * ops.length := by
          exact Nat.add_le_add hop ih'
        _ = VLEN * (ops.length + 1) := by
          simp [Nat.mul_add, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
        _ = VLEN * (List.length (op :: ops)) := by simp

lemma ceilDiv_le_of_mul_le {n k d : Nat} (hd : 0 < d) (h : n ≤ d * k) :
    ceilDiv n d ≤ k := by
  unfold ceilDiv
  have h' : n + d - 1 ≤ d * k + (d - 1) := by
    exact Nat.add_le_add_right h (d - 1)
  -- `Nat.div_le_iff_le_mul_add_pred` : a / d ≤ k ↔ a ≤ d*k + (d-1)
  have hdiv : (n + d - 1) / d ≤ k :=
    (Nat.div_le_iff_le_mul_add_pred hd).2 h'
  exact hdiv

lemma loadOps_lower_bound (p : Program) (mem : Memory) :
    minLoadOps (readWordCount p mem) ≤ loadOpCount p mem := by
  have hlen : (readWords p mem).length ≤ VLEN * (loadOpCount p mem) := by
    have := length_join_le (readOps p mem) (readOps_bound p mem)
    simpa [readWords, loadOpCount] using this
  exact ceilDiv_le_of_mul_le (by decide : 0 < VLEN) hlen

lemma ceilDiv_mono {a b d : Nat} (h : a ≤ b) :
    ceilDiv a d ≤ ceilDiv b d := by
  unfold ceilDiv
  have h' : a + d - 1 ≤ b + d - 1 := by
    exact Nat.add_le_add_right h (d - 1)
  exact Nat.div_le_div_right h' d

lemma minLoadOps_mono {a b : Nat} (h : a ≤ b) :
    minLoadOps a ≤ minLoadOps b := by
  exact ceilDiv_mono h

lemma loadLowerCycles_mono {a b : Nat} (h : a ≤ b) :
    loadLowerCycles a ≤ loadLowerCycles b := by
  exact ceilDiv_mono (minLoadOps_mono h)

/-- Lower bound on cycles implied by the load engine capacity. -/
def loadLowerCycles (words : Nat) : Nat := ceilDiv (minLoadOps words) LOAD_CAP

/-- Global lower bound (currently load-only). -/
def globalLowerBound : Nat := loadLowerCycles MIN_REQUIRED_WORDS

def globalLowerBoundKernel : Nat := loadLowerCycles MIN_REQUIRED_WORDS_KERNEL

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
  simpa [globalLowerBoundKernelFinal, computeLowerBoundKernel, globalLowerBoundKernel_eq_16]

theorem global_load_lower_bound_kernel_machine_final (p : Program)
    (hcorrect : CorrectOnMachine spec_kernel p MemSafeKernel) :
    ∀ mem, MemSafeKernel mem → KernelLayout mem → KernelSensitive mem → OutputDiffers mem →
      globalLowerBoundKernelFinal ≤ loadLowerCycles (readWordCountMachine p mem) := by
  intro mem hsafe hlayout hks hdiff
  have hload : globalLowerBoundKernel ≤ loadLowerCycles (readWordCountMachine p mem) :=
    global_load_lower_bound_kernel_machine p hcorrect mem hsafe hlayout hks hdiff
  have hcomp : computeLowerBoundKernel ≤ globalLowerBoundKernel := by
    simpa [computeLowerBoundKernel, globalLowerBoundKernel_eq_16]
  have hcomp' : computeLowerBoundKernel ≤ loadLowerCycles (readWordCountMachine p mem) :=
    le_trans hcomp hload
  exact (max_le_iff.mpr ⟨hload, hcomp'⟩)

theorem global_load_lower_bound_kernel_machine_final_valid (p : Program)
    (hcorrect : CorrectOnMachine spec_kernel p MemSafeKernel) :
    ∀ mem, ValidInput mem →
      globalLowerBoundKernelFinal ≤ loadLowerCycles (readWordCountMachine p mem) := by
  intro mem hvalid
  rcases hvalid with ⟨hsafe, hlayout, hks, hdiff⟩
  exact global_load_lower_bound_kernel_machine_final p hcorrect mem hsafe hlayout hks hdiff

theorem global_load_lower_bound_kernel_machine_final_valid_16 (p : Program)
    (hcorrect : CorrectOnMachine spec_kernel p MemSafeKernel) :
    ∀ mem, ValidInput mem →
      16 ≤ loadLowerCycles (readWordCountMachine p mem) := by
  intro mem hvalid
  have h := global_load_lower_bound_kernel_machine_final_valid p hcorrect mem hvalid
  simpa [globalLowerBoundKernelFinal_eq_16] using h

theorem global_load_lower_bound_kernel_machine_final_fuel (p : Program) (fuel : Nat)
    (hcorrect : CorrectOnMachineFuel spec_kernel p MemSafeKernel fuel) :
    ∀ mem, MemSafeKernel mem → KernelLayout mem → KernelSensitive mem → OutputDiffers mem →
      globalLowerBoundKernelFinal ≤ loadLowerCycles (readWordCountMachineFuel p fuel mem) := by
  intro mem hsafe hlayout hks hdiff
  have hload : globalLowerBoundKernel ≤ loadLowerCycles (readWordCountMachineFuel p fuel mem) :=
    global_load_lower_bound_kernel_machine_fuel p fuel hcorrect mem hsafe hlayout hks hdiff
  have hcomp : computeLowerBoundKernel ≤ globalLowerBoundKernel := by
    simpa [computeLowerBoundKernel, globalLowerBoundKernel_eq_16]
  have hcomp' : computeLowerBoundKernel ≤ loadLowerCycles (readWordCountMachineFuel p fuel mem) :=
    le_trans hcomp hload
  exact (max_le_iff.mpr ⟨hload, hcomp'⟩)

theorem global_load_lower_bound_kernel_machine_final_fuel_pcbounded (p : Program) (fuel : Nat)
    (hpc : PcBoundedProgram p)
    (hcorrect : CorrectOnMachineFuel spec_kernel p MemSafeKernel fuel) :
    ∀ mem, MemSafeKernel mem → KernelLayout mem → KernelSensitive mem → OutputDiffers mem →
      globalLowerBoundKernelFinal ≤ loadLowerCycles (readWordCountMachineFuel p fuel mem) := by
  -- hpc is included to align the theorem with PC-bounded control flow.
  exact global_load_lower_bound_kernel_machine_final_fuel p fuel hcorrect

theorem global_load_lower_bound_kernel_machine_uniformzero (p : Program)
    (hclass : ProgramClass p)
    (hcorrect : CorrectOnMachine spec_kernel p MemSafeKernel) :
    ∀ mem, UniformZeroKernel mem →
      globalLowerBoundKernel ≤ loadLowerCycles (readWordCountMachine p mem) := by
  intro mem hunif
  have hsafe : MemSafeKernel mem := hunif.1
  rcases hunif with ⟨_, hrounds, hnodes, hbatch, hheight, hlayout, hdisjoint, hforest, hidx, hval⟩
  have hks : KernelSensitive mem := kernelSensitive_uniform_zero mem
    ⟨hsafe, hrounds, hnodes, hbatch, hheight, hlayout, hdisjoint, hforest, hidx, hval⟩
  have hdiff : OutputDiffers mem := outputDiffers_uniform_zero mem
    ⟨hsafe, hrounds, hnodes, hbatch, hheight, hlayout, hdisjoint, hforest, hidx, hval⟩
  exact global_load_lower_bound_kernel_machine_pc p hclass hcorrect mem hsafe hlayout hks hdiff

theorem global_load_lower_bound_kernel_machine_uniformzero_final
    (p : Program) (hclass : ProgramClass p)
    (hcorrect : CorrectOnMachine spec_kernel p MemSafeKernel) :
    ∀ mem, UniformZeroKernel mem →
      globalLowerBoundKernelFinal ≤ loadLowerCycles (readWordCountMachine p mem) := by
  intro mem hunif
  have hload : globalLowerBoundKernel ≤ loadLowerCycles (readWordCountMachine p mem) :=
    global_load_lower_bound_kernel_machine_uniformzero p hclass hcorrect mem hunif
  have hcomp : computeLowerBoundKernel ≤ globalLowerBoundKernel := by
    simpa [computeLowerBoundKernel, globalLowerBoundKernel_eq_16]
  have hcomp' : computeLowerBoundKernel ≤ loadLowerCycles (readWordCountMachine p mem) :=
    le_trans hcomp hload
  exact (max_le_iff.mpr ⟨hload, hcomp'⟩)

theorem global_load_lower_bound_kernel_machine_adversaryK (p : Program)
    (hcorrect : CorrectOnMachine spec_kernel p MemSafeKernel) :
    ∀ mem, MemSafeKernel mem → WritesOutput p mem → memAt mem 0 = ROUNDS → ∀ k, AdversaryK mem k →
      globalLowerBoundKernelK k ≤ loadLowerCycles (readWordCountMachine p mem) := by
  intro mem hsafe hwrites hrounds k hadv
  have hmin : k * BATCH_SIZE * memAt mem 0 ≤ readWordCountMachine p mem :=
    min_required_words_adversaryK_machine p hcorrect mem hsafe hwrites k hadv
  have hmin' : k * BATCH_SIZE * ROUNDS ≤ readWordCountMachine p mem := by
    simpa [hrounds] using hmin
  have hload :
      loadLowerCycles (k * BATCH_SIZE * ROUNDS) ≤ loadLowerCycles (readWordCountMachine p mem) :=
    loadLowerCycles_mono hmin'
  simpa [globalLowerBoundKernelK] using hload

theorem global_load_lower_bound_kernel_machine_adversaryK_fuel (p : Program) (fuel : Nat)
    (hcorrect : CorrectOnMachineFuel spec_kernel p MemSafeKernel fuel) :
    ∀ mem, MemSafeKernel mem → WritesOutput p mem → memAt mem 0 = ROUNDS → ∀ k, AdversaryK mem k →
      globalLowerBoundKernelK k ≤ loadLowerCycles (readWordCountMachineFuel p fuel mem) := by
  intro mem hsafe hwrites hrounds k hadv
  have hmin : k * BATCH_SIZE * memAt mem 0 ≤ readWordCountMachineFuel p fuel mem :=
    min_required_words_adversaryK_machine_fuel p fuel hcorrect mem hsafe hwrites k hadv
  have hmin' : k * BATCH_SIZE * ROUNDS ≤ readWordCountMachineFuel p fuel mem := by
    simpa [hrounds] using hmin
  have hload :
      loadLowerCycles (k * BATCH_SIZE * ROUNDS) ≤
        loadLowerCycles (readWordCountMachineFuel p fuel mem) :=
    loadLowerCycles_mono hmin'
  simpa [globalLowerBoundKernelK] using hload

theorem global_load_lower_bound_kernel_machine_uniformzero_adversaryK
    (p : Program)
    (hcorrect : CorrectOnMachine spec_kernel p MemSafeKernel) :
    ∀ mem, UniformZeroKernel mem → ∀ k, AdversaryK mem k →
      globalLowerBoundKernelK k ≤ loadLowerCycles (readWordCountMachine p mem) := by
  intro mem hunif k hadv
  have hsafe : MemSafeKernel mem := hunif.1
  rcases hunif with ⟨_, hrounds, hnodes, hbatch, hheight, hlayout, hdisjoint, hforest, hidx, hval⟩
  exact global_load_lower_bound_kernel_machine_adversaryK p hcorrect mem hsafe hrounds k hadv

theorem global_load_lower_bound_kernel_machine_uniformzero_256
    (p : Program)
    (hcorrect : CorrectOnMachine spec_kernel p MemSafeKernel) :
    ∀ mem, UniformZeroKernel mem → AdversaryK mem 1 →
      256 ≤ loadLowerCycles (readWordCountMachine p mem) := by
  intro mem hunif hadv
  have h :=
    global_load_lower_bound_kernel_machine_uniformzero_adversaryK p hcorrect mem hunif 1 hadv
  simpa [globalLowerBoundKernelK_eq_256] using h

theorem global_load_lower_bound_kernel_machine_uniformzero_512
    (p : Program)
    (hcorrect : CorrectOnMachine spec_kernel p MemSafeKernel) :
    ∀ mem, UniformZeroKernel mem → AdversaryK mem 2 →
      512 ≤ loadLowerCycles (readWordCountMachine p mem) := by
  intro mem hunif hadv
  have h :=
    global_load_lower_bound_kernel_machine_uniformzero_adversaryK p hcorrect mem hunif 2 hadv
  simpa [globalLowerBoundKernelK_eq_512] using h

theorem global_load_lower_bound_kernel_machine_roundDistinct_256
    (p : Program) (hcorrect : CorrectOnMachine spec_kernel p MemSafeKernel) :
    ∀ mem, MemSafeKernel mem → memAt mem 0 = ROUNDS → RoundDistinctNodes mem 1 →
      256 ≤ loadLowerCycles (readWordCountMachine p mem) := by
  intro mem hsafe hrounds hrd
  have hadv : AdversaryK mem 1 := adversaryK_of_roundDistinct mem 1 hrd
  have h :=
    global_load_lower_bound_kernel_machine_adversaryK p hcorrect mem hsafe hrounds 1 hadv
  simpa [globalLowerBoundKernelK_eq_256] using h

theorem global_load_lower_bound_kernel_machine_roundDistinct_512
    (p : Program) (hcorrect : CorrectOnMachine spec_kernel p MemSafeKernel) :
    ∀ mem, MemSafeKernel mem → memAt mem 0 = ROUNDS → RoundDistinctNodes mem 2 →
      512 ≤ loadLowerCycles (readWordCountMachine p mem) := by
  intro mem hsafe hrounds hrd
  have hadv : AdversaryK mem 2 := adversaryK_of_roundDistinct mem 2 hrd
  have h :=
    global_load_lower_bound_kernel_machine_adversaryK p hcorrect mem hsafe hrounds 2 hadv
  simpa [globalLowerBoundKernelK_eq_512] using h

theorem global_load_lower_bound_kernel_machine_roundDistinct_256_fuel
    (p : Program) (fuel : Nat)
    (hcorrect : CorrectOnMachineFuel spec_kernel p MemSafeKernel fuel) :
    ∀ mem, MemSafeKernel mem → memAt mem 0 = ROUNDS → RoundDistinctNodes mem 1 →
      256 ≤ loadLowerCycles (readWordCountMachineFuel p fuel mem) := by
  intro mem hsafe hrounds hrd
  have hadv : AdversaryK mem 1 := adversaryK_of_roundDistinct mem 1 hrd
  have h :=
    global_load_lower_bound_kernel_machine_adversaryK_fuel p fuel hcorrect mem hsafe hrounds 1 hadv
  simpa [globalLowerBoundKernelK_eq_256] using h

theorem global_load_lower_bound_kernel_machine_roundDistinct_512_fuel
    (p : Program) (fuel : Nat)
    (hcorrect : CorrectOnMachineFuel spec_kernel p MemSafeKernel fuel) :
    ∀ mem, MemSafeKernel mem → memAt mem 0 = ROUNDS → RoundDistinctNodes mem 2 →
      512 ≤ loadLowerCycles (readWordCountMachineFuel p fuel mem) := by
  intro mem hsafe hrounds hrd
  have hadv : AdversaryK mem 2 := adversaryK_of_roundDistinct mem 2 hrd
  have h :=
    global_load_lower_bound_kernel_machine_adversaryK_fuel p fuel hcorrect mem hsafe hrounds 2 hadv
  simpa [globalLowerBoundKernelK_eq_512] using h

theorem global_load_lower_bound_kernel_machine_big_256
    (p : Program) (hcorrect : CorrectOnMachine spec_kernel p MemSafeKernel) :
    256 ≤ loadLowerCycles (readWordCountMachine p memBig) := by
  have hsafe : MemSafeKernel memBig := memBig_safe
  have hrounds : memAt memBig 0 = ROUNDS := memBig_rounds
  have hrd : RoundDistinctNodes memBig 1 := roundDistinctNodes_memBig
  have h :=
    global_load_lower_bound_kernel_machine_roundDistinct_256 p hcorrect memBig hsafe hrounds hrd
  simpa using h

theorem global_load_lower_bound_kernel_machine_exists_big_256
    (p : Program) (hcorrect : CorrectOnMachine spec_kernel p MemSafeKernel) :
    ∃ mem, 256 ≤ loadLowerCycles (readWordCountMachine p mem) := by
  exact ⟨memBig, global_load_lower_bound_kernel_machine_big_256 p hcorrect⟩

theorem global_load_lower_bound_kernel_machine_big_272
    (p : Program) (hcorrect : CorrectOnMachine spec_kernel p MemSafeKernel) :
    272 ≤ loadLowerCycles (readWordCountMachine p memBig) := by
  have hmin : BATCH_SIZE * (ROUNDS + 1) ≤ readWordCountMachine p memBig :=
    min_required_words_kernel_machine_memBig_all p hcorrect
  have hmono :
      loadLowerCycles (BATCH_SIZE * (ROUNDS + 1)) ≤
        loadLowerCycles (readWordCountMachine p memBig) :=
    loadLowerCycles_mono hmin
  have hcalc : loadLowerCycles (BATCH_SIZE * (ROUNDS + 1)) = 272 := by
    simpa [globalLowerBoundKernelPlus] using globalLowerBoundKernelPlus_eq_272
  simpa [hcalc] using hmono

theorem global_load_lower_bound_kernel_machine_exists_big_272
    (p : Program) (hcorrect : CorrectOnMachine spec_kernel p MemSafeKernel) :
    ∃ mem, 272 ≤ loadLowerCycles (readWordCountMachine p mem) := by
  exact ⟨memBig, global_load_lower_bound_kernel_machine_big_272 p hcorrect⟩

theorem global_load_lower_bound_kernel_machine_big_256_fuel
    (p : Program) (fuel : Nat)
    (hpc : PcBoundedProgram p)
    (hcorrect : CorrectOnMachineFuel spec_kernel p MemSafeKernel fuel) :
    256 ≤ loadLowerCycles (readWordCountMachineFuel p fuel memBig) := by
  have hsafe : MemSafeKernel memBig := memBig_safe
  have hrounds : memAt memBig 0 = ROUNDS := memBig_rounds
  have hrd : RoundDistinctNodes memBig 1 := roundDistinctNodes_memBig
  -- hpc is included to align the theorem with PC-bounded control flow.
  have h :=
    global_load_lower_bound_kernel_machine_roundDistinct_256_fuel p fuel hcorrect memBig hsafe hrounds hrd
  simpa using h

lemma globalLowerBound_eq :
    globalLowerBound = ceilDiv (ceilDiv MIN_REQUIRED_WORDS VLEN) LOAD_CAP := by
  rfl

theorem global_load_lower_bound (p : Program) (hstraight : StraightLine p)
    (hcorrect : CorrectOn spec_values p MemSafeValues) :
    ∀ mem, MemSafeValues mem → globalLowerBound ≤ loadLowerCycles (readWordCount p mem) := by
  intro mem hsafe
  have hmin : MIN_REQUIRED_WORDS ≤ readWordCount p mem := by
    simpa [MIN_REQUIRED_WORDS] using min_required_words_values p hstraight hcorrect mem hsafe
  exact loadLowerCycles_mono hmin

theorem global_load_lower_bound_machine (p : Program)
    (hcorrect : CorrectOnMachine spec_values p MemSafeValues) :
    ∀ mem, MemSafeValues mem → globalLowerBound ≤ loadLowerCycles (readWordCountMachine p mem) := by
  intro mem hsafe
  have hmin : MIN_REQUIRED_WORDS ≤ readWordCountMachine p mem := by
    simpa [MIN_REQUIRED_WORDS] using min_required_words_values_machine p hcorrect mem hsafe
  exact loadLowerCycles_mono hmin

theorem global_load_lower_bound_machine_fuel (p : Program) (fuel : Nat)
    (hcorrect : CorrectOnMachineFuel spec_values p MemSafeValues fuel) :
    ∀ mem, MemSafeValues mem → globalLowerBound ≤ loadLowerCycles (readWordCountMachineFuel p fuel mem) := by
  intro mem hsafe
  have hmin : MIN_REQUIRED_WORDS ≤ readWordCountMachineFuel p fuel mem := by
    simpa [MIN_REQUIRED_WORDS] using min_required_words_values_machine_fuel p fuel hcorrect mem hsafe
  exact loadLowerCycles_mono hmin

theorem global_load_lower_bound_kernel (p : Program) (hstraight : StraightLine p)
    (hcorrect : CorrectOn spec_kernel p MemSafeKernel) :
    ∀ mem, MemSafeKernel mem → KernelLayout mem → KernelSensitive mem → OutputDiffers mem →
      globalLowerBoundKernel ≤ loadLowerCycles (readWordCount p mem) := by
  intro mem hsafe hlayout hks hdiff
  have hmin : MIN_REQUIRED_WORDS_KERNEL ≤ readWordCount p mem := by
    simpa [MIN_REQUIRED_WORDS_KERNEL] using
      min_required_words_kernel_for_mem p hstraight hcorrect mem hsafe hlayout hks hdiff
  exact loadLowerCycles_mono hmin

theorem global_load_lower_bound_kernel_machine (p : Program)
    (hcorrect : CorrectOnMachine spec_kernel p MemSafeKernel) :
    ∀ mem, MemSafeKernel mem → KernelLayout mem → KernelSensitive mem → OutputDiffers mem →
      globalLowerBoundKernel ≤ loadLowerCycles (readWordCountMachine p mem) := by
  intro mem hsafe hlayout hks hdiff
  have hmin : MIN_REQUIRED_WORDS_KERNEL ≤ readWordCountMachine p mem := by
    simpa [MIN_REQUIRED_WORDS_KERNEL] using
      min_required_words_kernel_for_mem_machine p hcorrect mem hsafe hlayout hks hdiff
  exact loadLowerCycles_mono hmin

theorem global_load_lower_bound_kernel_machine_pc (p : Program)
    (hclass : ProgramClass p)
    (hcorrect : CorrectOnMachine spec_kernel p MemSafeKernel) :
    ∀ mem, MemSafeKernel mem → KernelLayout mem → KernelSensitive mem → OutputDiffers mem →
      globalLowerBoundKernel ≤ loadLowerCycles (readWordCountMachine p mem) := by
  exact global_load_lower_bound_kernel_machine p hcorrect

theorem global_load_lower_bound_kernel_machine_fuel (p : Program) (fuel : Nat)
    (hcorrect : CorrectOnMachineFuel spec_kernel p MemSafeKernel fuel) :
    ∀ mem, MemSafeKernel mem → KernelLayout mem → KernelSensitive mem → OutputDiffers mem →
      globalLowerBoundKernel ≤ loadLowerCycles (readWordCountMachineFuel p fuel mem) := by
  intro mem hsafe hlayout hks hdiff
  have hmin : MIN_REQUIRED_WORDS_KERNEL ≤ readWordCountMachineFuel p fuel mem := by
    simpa [MIN_REQUIRED_WORDS_KERNEL] using
      min_required_words_kernel_for_mem_machine_fuel p fuel hcorrect mem hsafe hlayout hks hdiff
  exact loadLowerCycles_mono hmin

theorem global_load_lower_bound_kernel_machine_fuel_pcbounded (p : Program) (fuel : Nat)
    (hpc : PcBoundedProgram p)
    (hcorrect : CorrectOnMachineFuel spec_kernel p MemSafeKernel fuel) :
    ∀ mem, MemSafeKernel mem → KernelLayout mem → KernelSensitive mem → OutputDiffers mem →
      globalLowerBoundKernel ≤ loadLowerCycles (readWordCountMachineFuel p fuel mem) := by
  -- hpc is included to align the theorem with PC-bounded control flow.
  exact global_load_lower_bound_kernel_machine_fuel p fuel hcorrect

theorem global_load_lower_bound_kernel_machine_final (p : Program)
    (hcorrect : CorrectOnMachine spec_kernel p MemSafeKernel) :
    ∀ mem, MemSafeKernel mem → KernelLayout mem → KernelSensitive mem → OutputDiffers mem →
      globalLowerBoundKernelFinal ≤ loadLowerCycles (readWordCountMachine p mem) := by
  intro mem hsafe hlayout hks hdiff
  have hload : globalLowerBoundKernel ≤ loadLowerCycles (readWordCountMachine p mem) :=
    global_load_lower_bound_kernel_machine p hcorrect mem hsafe hlayout hks hdiff
  have hcomp : computeLowerBoundKernel ≤ globalLowerBoundKernel := by
    -- computeLowerBoundKernel = 1, globalLowerBoundKernel = 16
    simpa [computeLowerBoundKernel, globalLowerBoundKernel_eq_16]
  have hcomp' : computeLowerBoundKernel ≤ loadLowerCycles (readWordCountMachine p mem) :=
    le_trans hcomp hload
  exact (max_le_iff.mpr ⟨hload, hcomp'⟩)

theorem global_load_lower_bound_kernel_machine_final_pc (p : Program)
    (hclass : ProgramClass p)
    (hcorrect : CorrectOnMachine spec_kernel p MemSafeKernel) :
    ∀ mem, MemSafeKernel mem → KernelLayout mem → KernelSensitive mem →
      globalLowerBoundKernelFinal ≤ loadLowerCycles (readWordCountMachine p mem) := by
  exact global_load_lower_bound_kernel_machine_final p hcorrect

theorem global_load_lower_bound_kernel_exists (p : Program) (hstraight : StraightLine p)
    (hcorrect : CorrectOn spec_kernel p MemSafeKernel) :
    ∃ mem, globalLowerBoundKernel ≤ loadLowerCycles (readWordCount p mem) := by
  refine ⟨memUniform0, ?_⟩
  have hmin : MIN_REQUIRED_WORDS_KERNEL ≤ readWordCount p memUniform0 := by
    simpa [MIN_REQUIRED_WORDS_KERNEL] using
      min_required_words_kernel p hstraight hcorrect memUniform0
  exact loadLowerCycles_mono hmin

end ProofGlobalLowerBound
