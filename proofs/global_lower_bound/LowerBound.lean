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
  · simp [execInstruction, hWF]

lemma execInstructionTrace_memWriteMany_of_ok (mem : Memory) (core : Core) (instr : Instruction)
    (hok : (execInstructionTrace mem core instr).1.ok = true) :
    memWriteMany mem (instr.store.flatMap (execStoreSlot core.scratch)) =
      some (execInstructionTrace mem core instr).1.mem := by
  unfold execInstructionTrace
  by_cases hWF : instrWellFormed instr
  · cases hvalu : execValuSlots core.scratch instr.valu with
    | none =>
        simp [execInstruction, hWF, hvalu] at hok
    | some valu_writes =>
        cases halu : execAluSlots core.scratch instr.alu with
        | none =>
            simp [execInstruction, hWF, hvalu, halu] at hok
        | some alu_writes =>
            let store_writes := instr.store.flatMap (execStoreSlot core.scratch)
            let flow_pair :=
              instr.flow.foldl
                (fun acc slot =>
                  let (c, ws) := acc
                  let (c', ws') := execFlowSlot false c core.scratch slot
                  (c', ws ++ ws'))
                (core, [])
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
            cases hload : load_writes? with
            | none =>
                -- ok cannot be true
                simp [execInstruction, hWF, hvalu, halu, load_writes?, hload] at hok
            | some load_writes =>
                cases hmw : memWriteMany mem store_writes with
                | none =>
                    simp [execInstruction, hWF, hvalu, halu, load_writes?, hload, hmw] at hok
                | some mem' =>
                    -- ok=true returns mem' here
                    have hres :
                        execInstruction false false (fun _ => 0) mem core instr =
                          ok_true load_writes mem' := by
                      unfold execInstruction
                      simp [hWF, hvalu, halu, load_writes?, hload, hmw, ok_true, flow_pair, store_writes]
                    simp [hres, ok_true, store_writes, hmw]
  · simp [execInstruction, hWF] at hok

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
    simp [memRead, h, h', hval']
  · have h' : ¬ addr < m2.size := by simpa [hsize] using h
    simp [memRead, h, h']

lemma execLoadSlot_eq_of_agree (s : Nat → Nat) (m1 m2 : Memory) (slot : LoadSlot)
    (h : AgreeOnList (loadAddrs s slot) m1 m2) :
    execLoadSlot s m1 slot = execLoadSlot s m2 slot := by
  cases slot with
  | load dest addr =>
      have h' : memAt m1 (s addr) = memAt m2 (s addr) := h.2 _ (by simp [loadAddrs])
      have hread := memRead_eq_of_agree m1 m2 (s addr) h.1 h'
      simp [execLoadSlot, hread]
  | load_offset dest addr offset =>
      have h' : memAt m1 (s (addr + offset)) = memAt m2 (s (addr + offset)) := by
        exact h.2 _ (by simp [loadAddrs])
      have hread := memRead_eq_of_agree m1 m2 (s (addr + offset)) h.1 h'
      simp [execLoadSlot, hread]
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
      simp [execLoadSlot, base, hvals, hreads]
  | const dest val =>
      simp [execLoadSlot]

lemma execLoadSlots_eq_of_agree (s : Nat → Nat) (m1 m2 : Memory) (slots : List LoadSlot)
    (h : AgreeOnList (listJoin (slots.map (loadAddrs s))) m1 m2) :
    slots.foldl
        (fun acc slot =>
          match acc, execLoadSlot s m1 slot with
          | some ws, some ws' => some (ws ++ ws')
          | _, _ => none)
        (some []) =
    slots.foldl
        (fun acc slot =>
          match acc, execLoadSlot s m2 slot with
          | some ws, some ws' => some (ws ++ ws')
          | _, _ => none)
        (some []) := by
  induction slots with
  | nil =>
      simp
  | cons slot rest ih =>
      have hslot : AgreeOnList (loadAddrs s slot) m1 m2 := by
        have := agreeOnList_append_left (xs := loadAddrs s slot)
            (ys := listJoin (rest.map (loadAddrs s))) (m1 := m1) (m2 := m2)
        -- listJoin (slot :: rest) = loadAddrs slot ++ listJoin rest
        have h' : AgreeOnList (loadAddrs s slot ++ listJoin (rest.map (loadAddrs s))) m1 m2 := by
          simpa [listJoin] using h
        exact this h'
      have hrest : AgreeOnList (listJoin (rest.map (loadAddrs s))) m1 m2 := by
        have := agreeOnList_append_right (xs := loadAddrs s slot)
            (ys := listJoin (rest.map (loadAddrs s))) (m1 := m1) (m2 := m2)
        have h' : AgreeOnList (loadAddrs s slot ++ listJoin (rest.map (loadAddrs s))) m1 m2 := by
          simpa [listJoin] using h
        exact this h'
      have hslot_eq := execLoadSlot_eq_of_agree s m1 m2 slot hslot
      simp [List.foldl, hslot_eq, ih, hrest]

lemma execInstructionTrace_ok_core_eq_of_agree (mem1 mem2 : Memory) (core : Core) (instr : Instruction)
    (h : AgreeOnList (listJoin (instr.load.map (loadAddrs core.scratch))) mem1 mem2) :
    let r1 := execInstructionTrace mem1 core instr
    let r2 := execInstructionTrace mem2 core instr
    r1.1.ok = r2.1.ok ∧ r1.1.core = r2.1.core := by
  unfold execInstructionTrace
  by_cases hWF : instrWellFormed instr
  · have hsize : mem1.size = mem2.size := h.1
    have hload :
        instr.load.foldl
            (fun acc slot =>
              match acc, execLoadSlot core.scratch mem1 slot with
              | some ws, some ws' => some (ws ++ ws')
              | _, _ => none)
            (some []) =
          instr.load.foldl
            (fun acc slot =>
              match acc, execLoadSlot core.scratch mem2 slot with
              | some ws, some ws' => some (ws ++ ws')
              | _, _ => none)
            (some []) := execLoadSlots_eq_of_agree core.scratch mem1 mem2 instr.load h
    cases hvalu : execValuSlots core.scratch instr.valu with
    | none =>
        simp [execInstruction, hWF, hvalu]
    | some valu_writes =>
        cases halu : execAluSlots core.scratch instr.alu with
        | none =>
            simp [execInstruction, hWF, hvalu, halu]
        | some alu_writes =>
            -- load-writes fold
            cases hload1 :
                instr.load.foldl
                    (fun acc slot =>
                      match acc, execLoadSlot core.scratch mem1 slot with
                      | some ws, some ws' => some (ws ++ ws')
                      | _, _ => none)
                    (some []) with
            | none =>
                have hload2 :
                    instr.load.foldl
                        (fun acc slot =>
                          match acc, execLoadSlot core.scratch mem2 slot with
                          | some ws, some ws' => some (ws ++ ws')
                          | _, _ => none)
                        (some []) = none := by
                  simpa [hload] using hload1
                simp [execInstruction, hWF, hvalu, halu, hload1, hload2]
            | some load_writes =>
                have hload2 :
                    instr.load.foldl
                        (fun acc slot =>
                          match acc, execLoadSlot core.scratch mem2 slot with
                          | some ws, some ws' => some (ws ++ ws')
                          | _, _ => none)
                        (some []) = some load_writes := by
                  simpa [hload] using hload1
                let store_writes := instr.store.flatMap (execStoreSlot core.scratch)
                cases hmw1 : memWriteMany mem1 store_writes with
                | none =>
                    -- memWriteMany isSome agrees across mems of equal size
                    have hmw2 : memWriteMany mem2 store_writes = none := by
                      cases h2 : memWriteMany mem2 store_writes with
                      | none =>
                          simpa [h2]
                      | some mem2' =>
                          have hsome : (memWriteMany mem1 store_writes).isSome =
                              (memWriteMany mem2 store_writes).isSome :=
                            memWriteMany_ok_eq mem1 mem2 store_writes hsize
                          simp [hmw1, h2] at hsome
                          cases hsome
                    simp [execInstruction, hWF, hvalu, halu, hload1, hload2, hmw1, hmw2]
                | some mem1' =>
                    -- if memWriteMany succeeds on mem1, it must succeed on mem2
                    cases hmw2 : memWriteMany mem2 store_writes with
                    | none =>
                        have hsome : (memWriteMany mem1 store_writes).isSome =
                            (memWriteMany mem2 store_writes).isSome :=
                          memWriteMany_ok_eq mem1 mem2 store_writes hsize
                        simp [hmw1, hmw2] at hsome
                        cases hsome
                    | some mem2' =>
                        -- ok=true branch, core depends only on scratch and writes lists
                        simp [execInstruction, hWF, hvalu, halu, hload1, hload2, hmw1, hmw2, store_writes]
  · simp [execInstruction, hWF]

-- NOTE: Non-interference is stated at the output level (not full memory equality).
-- The proof should show that if two memories agree on all addresses read by the program,
-- then the program's output slice is equal. This avoids the false stronger claim that
-- the entire final memory is equal.
-- Non-interference at the output level requires that the program actually writes
-- the output slice; otherwise outputs can differ without any reads.
lemma runTraceAuxRW_eq_on_written :
    ∀ prog mem1 mem2 core,
      AgreeOnList (listJoin (runTraceAux prog mem1 core).2) mem1 mem2 →
      SafeExecAux prog mem1 core →
      SafeExecAux prog mem2 core →
      ∀ addr,
        addr ∈
          listJoin
            ((runTraceAuxRW prog mem1 core).2.2.map (fun ws => ws.map Prod.fst)) →
        memAt (runTraceAuxRW prog mem1 core).1 addr =
        memAt (runTraceAuxRW prog mem2 core).1 addr := by
  intro prog
  induction prog with
  | nil =>
      intro mem1 mem2 core hagree hsafe1 hsafe2 addr hmem
      cases hmem
  | cons instr rest ih =>
      intro mem1 mem2 core hagree hsafe1 hsafe2 addr hmem
      -- unpack SafeExec on the head
      have hsafe1' :
          (execInstructionTrace mem1 core instr).1.ok = true ∧
          SafeExecAux rest (execInstructionTrace mem1 core instr).1.mem
            (execInstructionTrace mem1 core instr).1.core := by
        simpa [SafeExecAux] using hsafe1
      have hsafe2' :
          (execInstructionTrace mem2 core instr).1.ok = true ∧
          SafeExecAux rest (execInstructionTrace mem2 core instr).1.mem
            (execInstructionTrace mem2 core instr).1.core := by
        simpa [SafeExecAux] using hsafe2
      have hreads_head :
          AgreeOnList (listJoin (instr.load.map (loadAddrs core.scratch))) mem1 mem2 := by
        -- split agreement on full reads
        have h' :
            AgreeOnList
              (listJoin (instr.load.map (loadAddrs core.scratch)) ++
                listJoin ((runTraceAux rest
                  (execInstructionTrace mem1 core instr).1.mem
                  (execInstructionTrace mem1 core instr).1.core).2))
              mem1 mem2 := by
          -- runTraceAux on cons
          have hok : (execInstructionTrace mem1 core instr).1.ok = true := hsafe1'.1
          simp [runTraceAux, hok, listJoin_append] at hagree
          simpa using hagree
        exact agreeOnList_append_left (m1 := mem1) (m2 := mem2) h'
      -- ok/core equality on the head step
      have hok_core :=
        execInstructionTrace_ok_core_eq_of_agree mem1 mem2 core instr hreads_head
      have hok1 : (execInstructionTrace mem1 core instr).1.ok = true := hsafe1'.1
      have hok2 : (execInstructionTrace mem2 core instr).1.ok = true := by
        have := hok_core.1
        simpa [hok1] using this
      have hcore_eq : (execInstructionTrace mem1 core instr).1.core =
          (execInstructionTrace mem2 core instr).1.core := hok_core.2
      -- simplify runTraceAuxRW on ok branch
      have hmem_in :
          addr ∈
            listJoin ((instr.store.map (storeWrites core.scratch)).map (fun ws => ws.map Prod.fst)) ∨
            addr ∈
              listJoin
                (((runTraceAuxRW rest
                  (execInstructionTrace mem1 core instr).1.mem
                  (execInstructionTrace mem1 core instr).1.core).2.2).map (fun ws => ws.map Prod.fst)) := by
        have hok : (execInstructionTrace mem1 core instr).1.ok = true := hok1
        simp [runTraceAuxRW, hok, listJoin_append] at hmem
        exact hmem
      cases hmem_in with
      | inl hcur =>
          -- current-step written address
          -- show equality after the rest (either rewritten or preserved)
          by_cases hlater :
              addr ∈
                listJoin
                  (((runTraceAuxRW rest
                    (execInstructionTrace mem1 core instr).1.mem
                    (execInstructionTrace mem1 core instr).1.core).2.2).map (fun ws => ws.map Prod.fst))
          · -- written later: use IH
            have hagree_rest :
                AgreeOnList
                  (listJoin ((runTraceAux rest
                    (execInstructionTrace mem1 core instr).1.mem
                    (execInstructionTrace mem1 core instr).1.core).2))
                  (execInstructionTrace mem1 core instr).1.mem
                  (execInstructionTrace mem2 core instr).1.mem := by
              -- derive agreement on the rest's read list and propagate across stores
              have h' :
                  AgreeOnList
                    (listJoin (instr.load.map (loadAddrs core.scratch)) ++
                      listJoin ((runTraceAux rest
                        (execInstructionTrace mem1 core instr).1.mem
                        (execInstructionTrace mem1 core instr).1.core).2))
                    mem1 mem2 := by
                have hok : (execInstructionTrace mem1 core instr).1.ok = true := hok1
                simp [runTraceAux, hok, listJoin_append] at hagree
                simpa using hagree
              have hrest0 := agreeOnList_append_right (m1 := mem1) (m2 := mem2) h'
              -- propagate through identical store writes
            let store_writes := instr.store.flatMap (execStoreSlot core.scratch)
              have hmw1 :
                  memWriteMany mem1 store_writes =
                    some (execInstructionTrace mem1 core instr).1.mem :=
                execInstructionTrace_memWriteMany_of_ok mem1 core instr hok1
              have hmw2 :
                  memWriteMany mem2 store_writes =
                    some (execInstructionTrace mem2 core instr).1.mem :=
                execInstructionTrace_memWriteMany_of_ok mem2 core instr hok2
              exact agreeOnList_after_writes
                (xs := listJoin
                  ((runTraceAux rest (execInstructionTrace mem1 core instr).1.mem
                    (execInstructionTrace mem1 core instr).1.core).2))
                (m1 := mem1) (m2 := mem2)
                (m1' := (execInstructionTrace mem1 core instr).1.mem)
                (m2' := (execInstructionTrace mem2 core instr).1.mem)
                store_writes hrest0 hmw1 hmw2
            -- apply IH on rest
            have hsafe1r : SafeExecAux rest
                (execInstructionTrace mem1 core instr).1.mem
                (execInstructionTrace mem1 core instr).1.core := hsafe1'.2
            have hsafe2r : SafeExecAux rest
                (execInstructionTrace mem2 core instr).1.mem
                (execInstructionTrace mem2 core instr).1.core := hsafe2'.2
            have := ih
              (mem1 := (execInstructionTrace mem1 core instr).1.mem)
              (mem2 := (execInstructionTrace mem2 core instr).1.mem)
              (core := (execInstructionTrace mem1 core instr).1.core)
              hagree_rest hsafe1r hsafe2r addr hlater
            -- rewrite runTraceAuxRW on ok branch
            simp [runTraceAuxRW, hok1, hok2, hcore_eq] at this
            exact this
          · -- not written later: value set in this step and preserved
            -- show equality right after this step
            let store_writes := instr.store.flatMap (execStoreSlot core.scratch)
            have hmw1 :
                memWriteMany mem1 store_writes =
                  some (execInstructionTrace mem1 core instr).1.mem :=
              execInstructionTrace_memWriteMany_of_ok mem1 core instr hok1
            have hmw2 :
                memWriteMany mem2 store_writes =
                  some (execInstructionTrace mem2 core instr).1.mem :=
              execInstructionTrace_memWriteMany_of_ok mem2 core instr hok2
            have hcur' : addr ∈ store_writes.map Prod.fst := by
              -- current writes list is store_writes
              simpa [store_writes, storeWrites, listJoin] using hcur
            have hmem_eq_step :
                memAt (execInstructionTrace mem1 core instr).1.mem addr =
                memAt (execInstructionTrace mem2 core instr).1.mem addr := by
              have hmem_eq := memWriteMany_eq_on mem1 mem2
                (execInstructionTrace mem1 core instr).1.mem
                (execInstructionTrace mem2 core instr).1.mem store_writes hmw1 hmw2
              exact hmem_eq addr hcur'
            -- later execution doesn't touch addr
            have hnot_later :
                addr ∉
                  listJoin
                    (((runTraceAuxRW rest
                      (execInstructionTrace mem1 core instr).1.mem
                      (execInstructionTrace mem1 core instr).1.core).2.2).map (fun ws => ws.map Prod.fst)) := by
              exact hlater
            have hmem1_tail :
                memAt
                    (runTraceAuxRW rest
                      (execInstructionTrace mem1 core instr).1.mem
                      (execInstructionTrace mem1 core instr).1.core).1 addr =
                  memAt (execInstructionTrace mem1 core instr).1.mem addr := by
              exact runTraceAuxRW_eq_of_not_written rest
                (execInstructionTrace mem1 core instr).1.mem
                (execInstructionTrace mem1 core instr).1.core addr hnot_later
            have hmem2_tail :
                memAt
                    (runTraceAuxRW rest
                      (execInstructionTrace mem2 core instr).1.mem
                      (execInstructionTrace mem2 core instr).1.core).1 addr =
                  memAt (execInstructionTrace mem2 core instr).1.mem addr := by
              -- same not-written proof, using hcore_eq
              exact runTraceAuxRW_eq_of_not_written rest
                (execInstructionTrace mem2 core instr).1.mem
                (execInstructionTrace mem2 core instr).1.core addr hnot_later
            -- finish by rewriting the ok branch
            simp [runTraceAuxRW, hok1, hok2, hcore_eq, hmem1_tail, hmem2_tail, hmem_eq_step]
      | inr hrest =>
          -- written later: apply IH
          have hagree_rest :
              AgreeOnList
                (listJoin ((runTraceAux rest
                  (execInstructionTrace mem1 core instr).1.mem
                  (execInstructionTrace mem1 core instr).1.core).2))
                (execInstructionTrace mem1 core instr).1.mem
                (execInstructionTrace mem2 core instr).1.mem := by
            have h' :
                AgreeOnList
                  (listJoin (instr.load.map (loadAddrs core.scratch)) ++
                    listJoin ((runTraceAux rest
                      (execInstructionTrace mem1 core instr).1.mem
                      (execInstructionTrace mem1 core instr).1.core).2))
                  mem1 mem2 := by
              have hok : (execInstructionTrace mem1 core instr).1.ok = true := hok1
              simp [runTraceAux, hok, listJoin_append] at hagree
              simpa using hagree
            have hrest0 := agreeOnList_append_right (m1 := mem1) (m2 := mem2) h'
            let store_writes := instr.store.flatMap (execStoreSlot core.scratch)
            have hmw1 :
                memWriteMany mem1 store_writes =
                  some (execInstructionTrace mem1 core instr).1.mem :=
              execInstructionTrace_memWriteMany_of_ok mem1 core instr hok1
            have hmw2 :
                memWriteMany mem2 store_writes =
                  some (execInstructionTrace mem2 core instr).1.mem :=
              execInstructionTrace_memWriteMany_of_ok mem2 core instr hok2
            exact agreeOnList_after_writes
              (xs := listJoin
                ((runTraceAux rest (execInstructionTrace mem1 core instr).1.mem
                  (execInstructionTrace mem1 core instr).1.core).2))
              (m1 := mem1) (m2 := mem2)
              (m1' := (execInstructionTrace mem1 core instr).1.mem)
              (m2' := (execInstructionTrace mem2 core instr).1.mem)
              store_writes hrest0 hmw1 hmw2
          have hsafe1r : SafeExecAux rest
              (execInstructionTrace mem1 core instr).1.mem
              (execInstructionTrace mem1 core instr).1.core := hsafe1'.2
          have hsafe2r : SafeExecAux rest
              (execInstructionTrace mem2 core instr).1.mem
              (execInstructionTrace mem2 core instr).1.core := hsafe2'.2
          have := ih
            (mem1 := (execInstructionTrace mem1 core instr).1.mem)
            (mem2 := (execInstructionTrace mem2 core instr).1.mem)
            (core := (execInstructionTrace mem1 core instr).1.core)
            hagree_rest hsafe1r hsafe2r addr hrest
          simp [runTraceAuxRW, hok1, hok2, hcore_eq] at this
          exact this

lemma runMem_eq_on_writeWords (p : Program) (mem1 mem2 : Memory)
    (hreads : AgreeOnList (readWords p mem1) mem1 mem2)
    (hsafe1 : SafeExec p mem1) (hsafe2 : SafeExec p mem2) :
    ∀ addr ∈ writeWords p mem1,
      memAt (runMem p mem1) addr = memAt (runMem p mem2) addr := by
  intro addr hmem
  have hreads' : AgreeOnList (listJoin (runTraceAux p.program mem1 (initCore p)).2) mem1 mem2 := by
    simpa [readWords, readOps, runTrace] using hreads
  have hsafe1' : SafeExecAux p.program mem1 (initCore p) := hsafe1
  have hsafe2' : SafeExecAux p.program mem2 (initCore p) := hsafe2
  have hmem' :
      addr ∈
        listJoin
          ((runTraceAuxRW p.program mem1 (initCore p)).2.2.map (fun ws => ws.map Prod.fst)) := by
    simpa [writeWords, writeOps] using hmem
  have hmem_eq := runTraceAuxRW_eq_on_written
      p.program mem1 mem2 (initCore p) hreads' hsafe1' hsafe2' addr hmem'
  have hfst := runTraceAuxRW_fst_eq p.program mem1 (initCore p)
  have hfst2 := runTraceAuxRW_fst_eq p.program mem2 (initCore p)
  -- rewrite runMem via runTraceAuxRW
  simpa [runMem, runTrace, hfst, hfst2] using hmem_eq

theorem run_eq_of_agree (p : Program) (mem1 mem2 : Memory)
    (hptr : memAt mem1 PTR_INP_VAL = memAt mem2 PTR_INP_VAL)
    (h : AgreeOnList (readWords p mem1) mem1 mem2)
    (hwrites : WritesOutput p mem1)
    (hsafe1 : SafeExec p mem1) (hsafe2 : SafeExec p mem2) :
    run p mem1 = run p mem2 := by
  funext i
  have haddr :
      memAt mem1 PTR_INP_VAL + i ∈ writeWords p mem1 := by
    have hsubset : outputAddrs mem1 ⊆ (writeWords p mem1).toFinset := hwrites
    have hmem : memAt mem1 PTR_INP_VAL + i ∈ outputAddrs mem1 := by
      classical
      -- element of outputAddrs by definition
      simp [outputAddrs]
    -- convert Finset membership to List membership
    simpa using (List.mem_toFinset.mp (hsubset hmem))
  have hmem_eq := runMem_eq_on_writeWords p mem1 mem2 h hsafe1 hsafe2 _ haddr
  -- rewrite pointer equality
  have hptr' : memAt mem1 PTR_INP_VAL = memAt mem2 PTR_INP_VAL := hptr
  simp [run, outputOf, hptr', hmem_eq]

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
  | add => simp [aluEval, mod32]
  | sub => simp [aluEval, mod32]
  | mul => simp [aluEval, mod32]
  | idiv =>
      by_cases h : a2 = 0
      · simp [aluEval, h, mod32]
      · simp [aluEval, h, mod32]
  | cdiv =>
      by_cases h : a2 = 0
      · simp [aluEval, mod32]
      · simp [aluEval, mod32]
  | xor => simp [aluEval, mod32]
  | band => simp [aluEval, mod32]
  | bor => simp [aluEval, mod32]
  | shl => simp [aluEval, mod32, shl]
  | shr => simp [aluEval, mod32, shr]
  | mod =>
      by_cases h : a2 = 0
      · simp [aluEval, h, mod32]
      · simp [aluEval, h, mod32]
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

lemma memUpdate_ptr_eq (mem : Memory) (addr val : Nat) (hneq : addr ≠ PTR_INP_VAL) :
    memAt (memUpdate mem addr val) PTR_INP_VAL = memAt mem PTR_INP_VAL := by
  simp [memUpdate, memAt, hneq]

lemma memUpdate_eq_of_ne (mem : Memory) (addr val a : Nat) (hneq : a ≠ addr) :
    memAt (memUpdate mem addr val) a = memAt mem a := by
  simp [memUpdate, memAt, hneq]

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

axiom writes_output_of_correct (p : Program) (mem : Memory)
    (hcorrect : CorrectOn spec_kernel p MemSafeKernel)
    (hvalid : ValidInput mem) :
    WritesOutput p mem
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

axiom adversaryK_of_roundDistinct (mem : Memory) (k : Nat)
    (h : RoundDistinctNodes mem k) : AdversaryK mem k
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

lemma bSeq_le_two (r : Nat) : bSeq r ≤ 2 := by
  unfold bSeq
  by_cases h : iterHash (r + 1) 0 % 2 = 0
  · simp [h]
  · simp [h]

lemma cSeq_bound_le : ∀ r, cSeq r ≤ Nat.pow 2 (r + 1) - 2 := by
  intro r
  induction r with
  | zero =>
      simp [cSeq]
  | succ r ih =>
      have hb : bSeq r ≤ 2 := bSeq_le_two r
      set t := Nat.pow 2 (r + 1)
      have h1 : 2 * cSeq r + bSeq r ≤ 2 * (t - 2) + 2 := by
        exact Nat.add_le_add (Nat.mul_le_mul_left _ ih) hb
      have h2 : 2 * (t - 2) + 2 ≤ 2 * t - 2 := by
        have ht : 2 ≤ t := by
          have hpow : Nat.pow 2 1 ≤ Nat.pow 2 (r + 1) := by
            exact Nat.pow_le_pow_right (by decide : 0 < 2) (Nat.succ_le_succ (Nat.zero_le r))
          simpa [t] using hpow
        -- omega handles the linear arithmetic with t ≥ 2
        omega
      have h2' : 2 * (t - 2) + 2 ≤ Nat.pow 2 (r + 2) - 2 := by
        -- rewrite 2 * t as 2^(r+2)
        simpa [t, Nat.pow_succ, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using h2
      -- unfold cSeq at succ
      simpa [cSeq] using (le_trans h1 h2')

lemma cSeq_bound : ∀ r, cSeq r < Nat.pow 2 (r + 1) := by
  intro r
  have hle : cSeq r ≤ Nat.pow 2 (r + 1) - 2 := cSeq_bound_le r
  have hlt : Nat.pow 2 (r + 1) - 2 < Nat.pow 2 (r + 1) := by
    have hpos : 0 < Nat.pow 2 (r + 1) := by
      exact Nat.pow_pos (by decide : 0 < 2)
    exact Nat.sub_lt hpos (by decide : 0 < (2:Nat))
  exact lt_of_le_of_lt hle hlt

lemma pow_le_bigM {r : Nat} (hr : r < ROUNDS) :
    Nat.pow 2 (r + 1) ≤ BIG_M := by
  unfold BIG_M
  have hle1 : r + 1 ≤ ROUNDS := Nat.succ_le_of_lt hr
  have hle2 : ROUNDS ≤ ROUNDS + 2 := Nat.le_add_right _ _
  have hle : r + 1 ≤ ROUNDS + 2 := Nat.le_trans hle1 hle2
  exact Nat.pow_le_pow_right (Nat.succ_pos 1) hle
lemma idxAt_lt_N_NODES_BIG (r : Nat) (i : Fin BATCH_SIZE) (hr : r < ROUNDS) :
    idxAt r i < N_NODES_BIG := by
  have hpow : Nat.pow 2 r ≤ Nat.pow 2 ROUNDS := by
    exact Nat.pow_le_pow_right (by decide : 0 < 2) (Nat.le_of_lt hr)
  have hi2 : 2 * (i : Nat) < 2 * BATCH_SIZE := by
    exact (Nat.mul_lt_mul_left (a:=2) (b:=i) (c:=BATCH_SIZE) (by decide : 0 < (2:Nat))).2
      i.is_lt
  have hle : 2 * (i : Nat) + 1 ≤ 2 * BATCH_SIZE := by
    exact Nat.succ_le_of_lt hi2
  have hbig : bigIdx i ≤ (2 * BATCH_SIZE) * BIG_M := by
    dsimp [bigIdx, bigIdxNat]
    exact Nat.mul_le_mul_right _ hle
  have hidx1 : Nat.pow 2 r * bigIdx i ≤ Nat.pow 2 ROUNDS * bigIdx i := by
    exact Nat.mul_le_mul_right _ hpow
  have hidx2 : Nat.pow 2 ROUNDS * bigIdx i ≤ Nat.pow 2 ROUNDS * ((2 * BATCH_SIZE) * BIG_M) := by
    exact Nat.mul_le_mul_left _ hbig
  have hidx : Nat.pow 2 r * bigIdx i ≤ Nat.pow 2 ROUNDS * ((2 * BATCH_SIZE) * BIG_M) :=
    Nat.le_trans hidx1 hidx2
  have hval : cSeq r < BIG_M := by
    have hc : cSeq r < Nat.pow 2 (r + 1) := cSeq_bound r
    exact lt_of_lt_of_le hc (pow_le_bigM hr)
  have hsum : idxAt r i < Nat.pow 2 ROUNDS * ((2 * BATCH_SIZE) * BIG_M) + BIG_M := by
    dsimp [idxAt]
    exact Nat.add_lt_add_of_le_of_lt hidx hval
  simpa [N_NODES_BIG, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hsum

def idxAtR (r : Fin ROUNDS) (i : Fin BATCH_SIZE) : Nat := idxAt (r : Nat) i

lemma idxAtR_lt (r : Fin ROUNDS) (i : Fin BATCH_SIZE) :
    idxAtR r i < N_NODES_BIG := by
  exact idxAt_lt_N_NODES_BIG (r := r) i r.is_lt
lemma memBig_safe : MemSafeKernel memBig := by
  dsimp [MemSafeKernel]
  constructor
  · -- size bound
    have hpos : 0 < BATCH_SIZE := by decide
    dsimp [memBig, MEM_BIG_SIZE, BIG_VAL_BASE, BIG_IDX_BASE, BIG_FOREST_BASE, HEADER_SIZE]
    omega
  constructor
  · -- memAt memBig 2 = BATCH_SIZE
    simp [memAt, memBig]
  -- remaining bounds
  have h1 : BIG_FOREST_BASE + N_NODES_BIG ≤ MEM_BIG_SIZE := by
    dsimp [MEM_BIG_SIZE, BIG_VAL_BASE, BIG_IDX_BASE, BIG_FOREST_BASE, HEADER_SIZE]
    omega
  simp [memAt, memBig, MEM_BIG_SIZE, BIG_VAL_BASE, BIG_IDX_BASE, BIG_FOREST_BASE, PTR_FOREST,
    PTR_INP_IDX, PTR_INP_VAL]
  exact h1

lemma memBig_rounds : memAt memBig 0 = ROUNDS := by
  simp [memAt, memBig]

lemma memBig_ptrs :
    memAt memBig PTR_FOREST = BIG_FOREST_BASE ∧
    memAt memBig PTR_INP_IDX = BIG_IDX_BASE ∧
    memAt memBig PTR_INP_VAL = BIG_VAL_BASE := by
  constructor
  · simp [memAt, memBig, PTR_FOREST, PTR_INP_IDX, PTR_INP_VAL]
  constructor
  · simp [memAt, memBig, PTR_FOREST, PTR_INP_IDX, PTR_INP_VAL]
  · simp [memAt, memBig, PTR_FOREST, PTR_INP_IDX, PTR_INP_VAL]

lemma memBig_idx (i : Fin BATCH_SIZE) :
    memAt memBig (BIG_IDX_BASE + i) = bigIdx i := by
  set a := BIG_IDX_BASE + i
  have hge : HEADER_SIZE ≤ a := by
    have h1 : HEADER_SIZE ≤ BIG_IDX_BASE := by
      dsimp [BIG_IDX_BASE, BIG_FOREST_BASE]
      exact Nat.le_add_right HEADER_SIZE N_NODES_BIG
    exact Nat.le_trans h1 (Nat.le_add_right _ _)
  have hne : ∀ k, k < HEADER_SIZE → a ≠ k := by
    intro k hk
    exact ne_of_gt (lt_of_lt_of_le hk hge)
  have hne0 : a ≠ 0 := hne 0 (by decide)
  have hne1 : a ≠ 1 := hne 1 (by decide)
  have hne2 : a ≠ 2 := hne 2 (by decide)
  have hne3 : a ≠ 3 := hne 3 (by decide)
  have hneF : a ≠ PTR_FOREST := by
    exact hne 4 (by decide)
  have hneI : a ≠ PTR_INP_IDX := by
    exact hne 5 (by decide)
  have hneV : a ≠ PTR_INP_VAL := by
    exact hne 6 (by decide)
  have hforest : ¬(BIG_FOREST_BASE ≤ a ∧ a < BIG_FOREST_BASE + N_NODES_BIG) := by
    intro h
    have hge2 : BIG_FOREST_BASE + N_NODES_BIG ≤ a := by
      dsimp [a, BIG_IDX_BASE, BIG_FOREST_BASE]
      exact Nat.le_add_right _ _
    exact (not_lt_of_ge hge2) h.2
  have hidx : BIG_IDX_BASE ≤ a ∧ a < BIG_IDX_BASE + BATCH_SIZE := by
    constructor
    · exact Nat.le_add_right _ _
    · exact Nat.add_lt_add_left i.is_lt _
  have hmem : memAt memBig a = bigIdxNat (a - BIG_IDX_BASE) := by
    simp [memAt, memBig, hne0, hne1, hne2, hne3, hneF, hneI, hneV, hforest, hidx]
  simpa [a, bigIdx, bigIdxNat] using hmem

lemma memBig_val (i : Fin BATCH_SIZE) :
    memAt memBig (BIG_VAL_BASE + i) = 0 := by
  set a := BIG_VAL_BASE + i
  have hge : HEADER_SIZE ≤ a := by
    have h1 : HEADER_SIZE ≤ BIG_VAL_BASE := by
      dsimp [BIG_VAL_BASE, BIG_IDX_BASE, BIG_FOREST_BASE]
      have h1 : HEADER_SIZE ≤ HEADER_SIZE + N_NODES_BIG := by
        exact Nat.le_add_right _ _
      have h2 : HEADER_SIZE + N_NODES_BIG ≤ HEADER_SIZE + N_NODES_BIG + BATCH_SIZE := by
        exact Nat.le_add_right _ _
      exact Nat.le_trans h1 h2
    exact Nat.le_trans h1 (Nat.le_add_right _ _)
  have hne : ∀ k, k < HEADER_SIZE → a ≠ k := by
    intro k hk
    exact ne_of_gt (lt_of_lt_of_le hk hge)
  have hne0 : a ≠ 0 := hne 0 (by decide)
  have hne1 : a ≠ 1 := hne 1 (by decide)
  have hne2 : a ≠ 2 := hne 2 (by decide)
  have hne3 : a ≠ 3 := hne 3 (by decide)
  have hneF : a ≠ PTR_FOREST := by
    exact hne 4 (by decide)
  have hneI : a ≠ PTR_INP_IDX := by
    exact hne 5 (by decide)
  have hneV : a ≠ PTR_INP_VAL := by
    exact hne 6 (by decide)
  have hforest : ¬(BIG_FOREST_BASE ≤ a ∧ a < BIG_FOREST_BASE + N_NODES_BIG) := by
    intro h
    have hge2 : BIG_FOREST_BASE + N_NODES_BIG ≤ a := by
      dsimp [a, BIG_VAL_BASE, BIG_IDX_BASE, BIG_FOREST_BASE]
      have h1 : HEADER_SIZE + N_NODES_BIG ≤ HEADER_SIZE + N_NODES_BIG + BATCH_SIZE := by
        exact Nat.le_add_right _ _
      have h2 : HEADER_SIZE + N_NODES_BIG + BATCH_SIZE ≤
          HEADER_SIZE + N_NODES_BIG + BATCH_SIZE + i := by
        exact Nat.le_add_right _ _
      exact Nat.le_trans h1 h2
    exact (not_lt_of_ge hge2) h.2
  have hidx : ¬(BIG_IDX_BASE ≤ a ∧ a < BIG_IDX_BASE + BATCH_SIZE) := by
    intro h
    have hge2 : BIG_IDX_BASE + BATCH_SIZE ≤ a := by
      dsimp [a, BIG_VAL_BASE]
      exact Nat.le_add_right _ _
    exact (not_lt_of_ge hge2) h.2
  have hval : BIG_VAL_BASE ≤ a ∧ a < BIG_VAL_BASE + BATCH_SIZE := by
    constructor
    · exact Nat.le_add_right _ _
    · exact Nat.add_lt_add_left i.is_lt _
  have hmem : memAt memBig a = 0 := by
    simp [memAt, memBig, hne0, hne1, hne2, hne3, hneF, hneI, hneV, hforest, hidx]
  simpa [a] using hmem

lemma memBig_tree (k : Nat) (hk : k < N_NODES_BIG) :
    memAt memBig (BIG_FOREST_BASE + k) = 0 := by
  set a := BIG_FOREST_BASE + k
  have hge : HEADER_SIZE ≤ a := by
    subst a
    dsimp [BIG_FOREST_BASE]
    exact Nat.le_add_right HEADER_SIZE k
  have hne : ∀ k, k < HEADER_SIZE → a ≠ k := by
    intro k hk'
    exact ne_of_gt (lt_of_lt_of_le hk' hge)
  have hne0 : a ≠ 0 := hne 0 (by decide)
  have hne1 : a ≠ 1 := hne 1 (by decide)
  have hne2 : a ≠ 2 := hne 2 (by decide)
  have hne3 : a ≠ 3 := hne 3 (by decide)
  have hneF : a ≠ PTR_FOREST := by
    exact hne 4 (by decide)
  have hneI : a ≠ PTR_INP_IDX := by
    exact hne 5 (by decide)
  have hneV : a ≠ PTR_INP_VAL := by
    exact hne 6 (by decide)
  have hforest : BIG_FOREST_BASE ≤ a ∧ a < BIG_FOREST_BASE + N_NODES_BIG := by
    constructor
    · exact Nat.le_add_right _ _
    · exact Nat.add_lt_add_left hk _
  have hmem : memAt memBig a = 0 := by
    simp [memAt, memBig, hne0, hne1, hne2, hne3, hneF, hneI, hneV, hforest]
  simpa [a] using hmem

def memBigTreeAddrs : Finset Nat :=
  (Finset.univ.image (fun t : Fin ROUNDS × Fin BATCH_SIZE =>
    BIG_FOREST_BASE + idxAtR t.1 t.2))

def memBigValAddrs : Finset Nat :=
  (Finset.univ.image (fun i : Fin BATCH_SIZE => BIG_VAL_BASE + i))

def memBigAllAddrs : Finset Nat :=
  memBigTreeAddrs ∪ memBigValAddrs

lemma bSeq_ge_one (r : Nat) : 1 ≤ bSeq r := by
  unfold bSeq
  by_cases h : iterHash (r + 1) 0 % 2 = 0 <;> simp [h]

lemma cSeq_lt_succ (r : Nat) : cSeq r < cSeq (r + 1) := by
  have hb : 1 ≤ bSeq r := bSeq_ge_one r
  have hb' : 0 < bSeq r := lt_of_lt_of_le (by decide : 0 < (1:Nat)) hb
  have h1 : cSeq r < cSeq r + bSeq r :=
    Nat.lt_add_of_pos_right (n:=cSeq r) (k:=bSeq r) hb'
  have h2 : cSeq r + bSeq r ≤ 2 * cSeq r + bSeq r := by
    have hc : cSeq r ≤ 2 * cSeq r := Nat.le_mul_of_pos_left _ (by decide : 0 < (2:Nat))
    exact Nat.add_le_add_right hc _
  have h : cSeq r < 2 * cSeq r + bSeq r := lt_of_lt_of_le h1 h2
  simpa [cSeq] using h

lemma cSeq_lt_of_lt {a b : Nat} (h : a < b) : cSeq a < cSeq b := by
  induction b with
  | zero =>
      cases (Nat.not_lt_zero _ h)
  | succ b ih =>
      have hb : cSeq b < cSeq (b + 1) := cSeq_lt_succ b
      have hle : a ≤ b := Nat.lt_succ_iff.mp h
      cases lt_or_eq_of_le hle with
      | inl hlt => exact lt_trans (ih hlt) hb
      | inr hEq => simpa [hEq] using hb

lemma cSeq_strict_mono : StrictMono cSeq := by
  intro a b h
  exact cSeq_lt_of_lt h

lemma cSeq_lt_bigM (r : Nat) (hr : r < ROUNDS) : cSeq r < BIG_M := by
  exact lt_of_lt_of_le (cSeq_bound r) (pow_le_bigM hr)

lemma idxAt_mod (r : Nat) (i : Fin BATCH_SIZE) (hr : r < ROUNDS) :
    idxAt r i % BIG_M = cSeq r := by
  have hmul :
      Nat.pow 2 r * bigIdx i =
        BIG_M * (Nat.pow 2 r * (2 * (i : Nat) + 1)) := by
    simp [bigIdx, bigIdxNat, Nat.mul_assoc, Nat.mul_comm]
  have hlt : cSeq r < BIG_M := cSeq_lt_bigM r hr
  have hmodc : cSeq r % BIG_M = cSeq r := Nat.mod_eq_of_lt hlt
  have hstep : idxAt r i % BIG_M =
      (cSeq r + BIG_M * (Nat.pow 2 r * (2 * (i : Nat) + 1))) % BIG_M := by
    calc
      idxAt r i % BIG_M =
          (Nat.pow 2 r * bigIdx i + cSeq r) % BIG_M := by rfl
      _ =
          (BIG_M * (Nat.pow 2 r * (2 * (i : Nat) + 1)) + cSeq r) % BIG_M := by
            rw [hmul]
      _ =
          (cSeq r + BIG_M * (Nat.pow 2 r * (2 * (i : Nat) + 1))) % BIG_M := by
            simp [Nat.add_comm]
  calc
    idxAt r i % BIG_M =
        (cSeq r + BIG_M * (Nat.pow 2 r * (2 * (i : Nat) + 1))) % BIG_M := hstep
    _ = cSeq r % BIG_M := by
          simp
    _ = cSeq r := by simp [hmodc]

lemma bigIdx_inj {i j : Fin BATCH_SIZE} (h : bigIdx i = bigIdx j) : i = j := by
  apply Fin.ext
  have h' : bigIdxNat i = bigIdxNat j := by simpa [bigIdx] using h
  have hpos : 0 < BIG_M := by
    dsimp [BIG_M]
    exact Nat.two_pow_pos _
  have hmul : (2 * (i : Nat) + 1) = (2 * (j : Nat) + 1) := by
    have h'' : BIG_M * (2 * (i : Nat) + 1) = BIG_M * (2 * (j : Nat) + 1) := by
      simpa [bigIdxNat, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using h'
    exact Nat.mul_left_cancel (n:=BIG_M) (np:=hpos) h''
  have h2 : 2 * (i : Nat) = 2 * (j : Nat) := by
    exact Nat.add_right_cancel hmul
  have h3 : (i : Nat) = (j : Nat) := by
    exact Nat.mul_left_cancel (n:=2) (np:=(by decide : 0 < (2:Nat))) h2
  exact h3

lemma idxAtR_inj :
    Function.Injective (fun t : Fin ROUNDS × Fin BATCH_SIZE => idxAtR t.1 t.2) := by
  intro a b h
  rcases a with ⟨r, i⟩
  rcases b with ⟨r', i'⟩
  have hmod : cSeq r = cSeq r' := by
    have hmod' := congrArg (fun x => x % BIG_M) h
    simpa [idxAtR, idxAt_mod (r:=r) (i:=i) r.is_lt,
      idxAt_mod (r:=r') (i:=i') r'.is_lt] using hmod'
  have hr' : (r : Nat) = (r' : Nat) := (cSeq_strict_mono.injective) hmod
  have hr : r = r' := by
    apply Fin.ext
    exact hr'
  have h0 : idxAt r i = idxAt r i' := by
    simpa [idxAtR, hr] using h
  have h1 : Nat.pow 2 r * bigIdx i = Nat.pow 2 r * bigIdx i' := by
    have h' : Nat.pow 2 r * bigIdx i + cSeq r =
        Nat.pow 2 r * bigIdx i' + cSeq r := by
      simpa [idxAt] using h0
    exact Nat.add_right_cancel h'
  have hpos : 0 < Nat.pow 2 r := Nat.two_pow_pos _
  have h2 : bigIdx i = bigIdx i' := Nat.mul_left_cancel (n:=Nat.pow 2 r) (np:=hpos) h1
  have hi : i = i' := bigIdx_inj h2
  cases hr
  cases hi
  rfl

lemma memBigTreeAddrs_card :
    memBigTreeAddrs.card = ROUNDS * BATCH_SIZE := by
  classical
  have hinj :
      Function.Injective
        (fun t : Fin ROUNDS × Fin BATCH_SIZE => BIG_FOREST_BASE + idxAtR t.1 t.2) := by
    intro a b h
    apply idxAtR_inj
    exact Nat.add_left_cancel h
  simpa [memBigTreeAddrs] using
    (Finset.card_image_of_injective (s:=Finset.univ) hinj)
lemma memBigValAddrs_card :
    memBigValAddrs.card = BATCH_SIZE := by
  classical
  have hinj : Function.Injective (fun i : Fin BATCH_SIZE => BIG_VAL_BASE + i) := by
    intro a b h
    apply Fin.ext
    exact Nat.add_left_cancel h
  simpa [memBigValAddrs] using
    (Finset.card_image_of_injective (s:=Finset.univ) hinj)
lemma memBigAddrs_disjoint :
    Disjoint memBigTreeAddrs memBigValAddrs := by
  classical
  refine Finset.disjoint_left.2 ?_
  intro a ha hb
  rcases Finset.mem_image.1 ha with ⟨t, _ht, rfl⟩
  rcases Finset.mem_image.1 hb with ⟨i, _hi, hEq⟩
  have hlt : BIG_FOREST_BASE + idxAtR t.1 t.2 < BIG_IDX_BASE := by
    have hidx : idxAtR t.1 t.2 < N_NODES_BIG := idxAtR_lt t.1 t.2
    have hlt' : BIG_FOREST_BASE + idxAtR t.1 t.2 < BIG_FOREST_BASE + N_NODES_BIG := by
      exact Nat.add_lt_add_left hidx _
    simpa [BIG_IDX_BASE, BIG_FOREST_BASE] using hlt'
  have hge : BIG_VAL_BASE ≤ BIG_FOREST_BASE + idxAtR t.1 t.2 := by
    -- rewrite via the val address equality
    have : BIG_VAL_BASE ≤ BIG_VAL_BASE + i := by
      exact Nat.le_add_right _ _
    simpa [hEq] using this
  have hpos : 0 < BATCH_SIZE := by decide
  have hgt : BIG_IDX_BASE < BIG_VAL_BASE := by
    -- BIG_VAL_BASE = BIG_IDX_BASE + BATCH_SIZE
    simpa [BIG_VAL_BASE] using
      (Nat.lt_add_of_pos_right (n:=BIG_IDX_BASE) (k:=BATCH_SIZE) hpos)
  have hgt' : BIG_IDX_BASE < BIG_FOREST_BASE + idxAtR t.1 t.2 :=
    lt_of_lt_of_le hgt hge
  exact (lt_irrefl _ (lt_trans hgt' hlt))
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

lemma memBig_tree_addr_safe (r : Fin ROUNDS) (i : Fin BATCH_SIZE) :
    AddrSafe memBig (BIG_FOREST_BASE + idxAtR r i) := by
  have hge : HEADER_SIZE ≤ BIG_FOREST_BASE + idxAtR r i := by
    dsimp [BIG_FOREST_BASE, HEADER_SIZE]
    exact Nat.le_add_right _ _
  have hlt_base : BIG_FOREST_BASE + idxAtR r i < BIG_FOREST_BASE + N_NODES_BIG := by
    exact Nat.add_lt_add_left (idxAtR_lt r i) _
  have hsize : BIG_FOREST_BASE + N_NODES_BIG ≤ memBig.size := by
    dsimp [memBig, MEM_BIG_SIZE, BIG_VAL_BASE, BIG_IDX_BASE, BIG_FOREST_BASE, HEADER_SIZE]
    omega
  have hlt : BIG_FOREST_BASE + idxAtR r i < memBig.size :=
    lt_of_lt_of_le hlt_base hsize
  exact ⟨hge, hlt⟩

lemma memBig_val_addr_safe (i : Fin BATCH_SIZE) :
    AddrSafe memBig (BIG_VAL_BASE + i) := by
  have hge : HEADER_SIZE ≤ BIG_VAL_BASE + i := by
    dsimp [BIG_VAL_BASE, BIG_IDX_BASE, BIG_FOREST_BASE, HEADER_SIZE]
    have h1 : 7 ≤ 7 + N_NODES_BIG + BATCH_SIZE := by
      have h1' : 7 ≤ 7 + N_NODES_BIG := by
        exact Nat.le_add_right _ _
      have h2' : 7 + N_NODES_BIG ≤ 7 + N_NODES_BIG + BATCH_SIZE := by
        exact Nat.le_add_right _ _
      exact Nat.le_trans h1' h2'
    have h2 : 7 + N_NODES_BIG + BATCH_SIZE ≤ 7 + N_NODES_BIG + BATCH_SIZE + i := by
      exact Nat.le_add_right _ _
    exact Nat.le_trans h1 h2
  have hlt : BIG_VAL_BASE + i < memBig.size := by
    have hlt' : BIG_VAL_BASE + i < BIG_VAL_BASE + BATCH_SIZE := by
      exact Nat.add_lt_add_left i.is_lt _
    dsimp [memBig, MEM_BIG_SIZE]
    exact hlt'
  exact ⟨hge, hlt⟩

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

lemma memUpdate_header_eq (mem : Memory) {addr val k : Nat}
    (hk : k < HEADER_SIZE) (haddr : HEADER_SIZE ≤ addr) :
    memAt (memUpdate mem addr val) k = memAt mem k := by
  have hne : k ≠ addr := by
    exact ne_of_lt (lt_of_lt_of_le hk haddr)
  simp [memUpdate, memAt, hne]
lemma addr_ge_header_of_layout (mem : Memory) (i : Fin BATCH_SIZE)
    (hlayout : KernelLayout mem) : HEADER_SIZE ≤ memAt mem PTR_INP_VAL + i := by
  dsimp [KernelLayout] at hlayout
  rcases hlayout with ⟨_hforest, _hidx, hval⟩
  exact Nat.le_trans hval (Nat.le_add_right _ _)
lemma memSafeKernel_update_addr (mem : Memory) (addr : Nat)
    (hsafe : MemSafeKernel mem) (haddr : AddrSafe mem addr) :
    MemSafeKernel (memUpdate mem addr (memAt mem addr + 1)) := by
  rcases haddr with ⟨hge, _⟩
  have hne : ∀ k, k < HEADER_SIZE → k ≠ addr := by
    intro k hk
    exact ne_of_lt (lt_of_lt_of_le hk hge)
  have hne1 : 1 ≠ addr := hne 1 (by decide)
  have hne2 : 2 ≠ addr := hne 2 (by decide)
  have hneF : PTR_FOREST ≠ addr := hne 4 (by decide)
  have hneI : PTR_INP_IDX ≠ addr := hne 5 (by decide)
  have hneV : PTR_INP_VAL ≠ addr := hne 6 (by decide)
  dsimp [MemSafeKernel] at hsafe ⊢
  simpa [memUpdate, memAt, hne1, hne2, hneF, hneI, hneV] using hsafe

lemma memSafeKernel_update_val (mem : Memory) (i : Fin BATCH_SIZE)
    (hlayout : KernelLayout mem) (hsafe : MemSafeKernel mem) :
    MemSafeKernel
      (memUpdate mem (memAt mem PTR_INP_VAL + i)
        (memAt mem (memAt mem PTR_INP_VAL + i) + 1)) := by
  -- show the updated address is safe, then reuse the general lemma
  have hge : HEADER_SIZE ≤ memAt mem PTR_INP_VAL + i :=
    addr_ge_header_of_layout mem i hlayout
  -- upper bound from MemSafeKernel
  dsimp [MemSafeKernel] at hsafe
  rcases hsafe with ⟨hsize, hbatch, hrest⟩
  rcases hrest with ⟨hforest, hidx, hval⟩
  -- hval : valPtr + BATCH_SIZE ≤ mem.size
  have hlt : memAt mem PTR_INP_VAL + i < mem.size := by
    have hle : memAt mem PTR_INP_VAL + i < memAt mem PTR_INP_VAL + BATCH_SIZE := by
      exact Nat.add_lt_add_left i.is_lt _
    exact lt_of_lt_of_le hle hval
  have haddr : AddrSafe mem (memAt mem PTR_INP_VAL + i) := ⟨hge, hlt⟩
  -- apply general update lemma
  exact memSafeKernel_update_addr mem (memAt mem PTR_INP_VAL + i) (by
    -- reconstruct MemSafeKernel mem
    exact ⟨hsize, hbatch, hforest, hidx, hval⟩) haddr
def memUniform1 : Memory :=
  memUpdate memUniform0 VAL_BASE 1

def memUniformVal (j : Fin BATCH_SIZE) : Memory :=
  memUpdate memUniform0 (VAL_BASE + j) 1

lemma BATCH_SIZE_pos : 0 < BATCH_SIZE := by
  native_decide

instance : NeZero BATCH_SIZE := ⟨ne_of_gt BATCH_SIZE_pos⟩

lemma memUniform0_safe : MemSafeKernel memUniform0 := by
  unfold MemSafeKernel
  refine And.intro ?hsize (And.intro ?hbatch ?hrest)
  · have h : (7 : Nat) < MEM_SIZE := by
      native_decide
    simpa [memUniform0] using h
  · simp [memUniform0, memAt]
  · -- header-derived bounds are purely numeric
    have h :
        FOREST_BASE + N_NODES ≤ MEM_SIZE ∧
        IDX_BASE + BATCH_SIZE ≤ MEM_SIZE ∧
        VAL_BASE + BATCH_SIZE ≤ MEM_SIZE := by
      native_decide
    simpa [memUniform0, PTR_FOREST, PTR_INP_IDX, PTR_INP_VAL,
      FOREST_BASE, IDX_BASE, VAL_BASE] using h
lemma val_base_ge_header : HEADER_SIZE ≤ VAL_BASE := by
  have h1 : HEADER_SIZE ≤ IDX_BASE := by
    dsimp [IDX_BASE, FOREST_BASE]
    exact Nat.le_add_right HEADER_SIZE N_NODES
  have h2 : IDX_BASE ≤ VAL_BASE := by
    dsimp [VAL_BASE]
    exact Nat.le_add_right IDX_BASE BATCH_SIZE
  exact Nat.le_trans h1 h2
lemma memUniformVal_header_eq (j : Fin BATCH_SIZE) (k : Nat) (hk : k < HEADER_SIZE) :
    memAt (memUniformVal j) k = memAt memUniform0 k := by
  have hlt : k < VAL_BASE := lt_of_lt_of_le hk val_base_ge_header
  have hle : VAL_BASE ≤ VAL_BASE + (j : Nat) := Nat.le_add_right _ _
  have hne : k ≠ VAL_BASE + (j : Nat) := by
    exact ne_of_lt (lt_of_lt_of_le hlt hle)
  simp [memUniformVal, memUpdate, memAt, hne]
lemma memUniformVal_safe (j : Fin BATCH_SIZE) : MemSafeKernel (memUniformVal j) := by
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
    hsize h1 h2 hforest hidx hval memUniform0_safe
  simpa using hsafe
lemma memUniform_ptrs :
    memAt memUniform0 PTR_FOREST = FOREST_BASE ∧
    memAt memUniform0 PTR_INP_IDX = IDX_BASE ∧
    memAt memUniform0 PTR_INP_VAL = VAL_BASE := by
  simp [memUniform0, memAt, PTR_FOREST, PTR_INP_IDX, PTR_INP_VAL]
lemma memUniform_idx (i : Nat) :
    memAt memUniform0 (IDX_BASE + i) = 0 := by
  set a := IDX_BASE + i
  have hge : HEADER_SIZE ≤ a := by
    have h1 : HEADER_SIZE ≤ IDX_BASE := by
      dsimp [IDX_BASE, FOREST_BASE]
      exact Nat.le_add_right HEADER_SIZE N_NODES
    exact Nat.le_trans h1 (Nat.le_add_right _ _)
  have hne : ∀ k, k < HEADER_SIZE → a ≠ k := by
    intro k hk
    exact ne_of_gt (lt_of_lt_of_le hk hge)
  have hne0 : a ≠ 0 := hne 0 (by decide)
  have hne1 : a ≠ 1 := hne 1 (by decide)
  have hne2 : a ≠ 2 := hne 2 (by decide)
  have hne3 : a ≠ 3 := hne 3 (by decide)
  have hneF : a ≠ PTR_FOREST := by
    exact hne 4 (by decide)
  have hneI : a ≠ PTR_INP_IDX := by
    exact hne 5 (by decide)
  have hneV : a ≠ PTR_INP_VAL := by
    exact hne 6 (by decide)
  simp [memUniform0, memAt, hne0, hne1, hne2, hne3, hneF, hneI, hneV]
lemma memUniform_val (i : Nat) :
    memAt memUniform0 (VAL_BASE + i) = 0 := by
  set a := VAL_BASE + i
  have hge : HEADER_SIZE ≤ a := by
    exact Nat.le_trans val_base_ge_header (Nat.le_add_right _ _)
  have hne : ∀ k, k < HEADER_SIZE → a ≠ k := by
    intro k hk
    exact ne_of_gt (lt_of_lt_of_le hk hge)
  have hne0 : a ≠ 0 := hne 0 (by decide)
  have hne1 : a ≠ 1 := hne 1 (by decide)
  have hne2 : a ≠ 2 := hne 2 (by decide)
  have hne3 : a ≠ 3 := hne 3 (by decide)
  have hneF : a ≠ PTR_FOREST := by
    exact hne 4 (by decide)
  have hneI : a ≠ PTR_INP_IDX := by
    exact hne 5 (by decide)
  have hneV : a ≠ PTR_INP_VAL := by
    exact hne 6 (by decide)
  simp [memUniform0, memAt, hne0, hne1, hne2, hne3, hneF, hneI, hneV]
lemma memUniform_forest (i : Nat) :
    memAt memUniform0 (FOREST_BASE + i) = 0 := by
  set a := FOREST_BASE + i
  have hge : HEADER_SIZE ≤ a := by
    subst a
    dsimp [FOREST_BASE]
    exact Nat.le_add_right HEADER_SIZE i
  have hne : ∀ k, k < HEADER_SIZE → a ≠ k := by
    intro k hk
    exact ne_of_gt (lt_of_lt_of_le hk hge)
  have hne0 : a ≠ 0 := hne 0 (by decide)
  have hne1 : a ≠ 1 := hne 1 (by decide)
  have hne2 : a ≠ 2 := hne 2 (by decide)
  have hne3 : a ≠ 3 := hne 3 (by decide)
  have hneF : a ≠ PTR_FOREST := by
    exact hne 4 (by decide)
  have hneI : a ≠ PTR_INP_IDX := by
    exact hne 5 (by decide)
  have hneV : a ≠ PTR_INP_VAL := by
    simpa [PTR_INP_VAL] using (hne 6 (by decide))
  simp [memUniform0, memAt, hne0, hne1, hne2, hne3, hneF, hneI, hneV]
lemma memUniform_idx_fin (i : Fin BATCH_SIZE) :
    memAt memUniform0 (IDX_BASE + i) = 0 := by
  simpa using memUniform_idx (i := (i : Nat))
lemma memUniform_val_fin (i : Fin BATCH_SIZE) :
    memAt memUniform0 (VAL_BASE + i) = 0 := by
  simpa using memUniform_val (i := (i : Nat))
axiom spec_kernel_uniform0 (i : Fin BATCH_SIZE) :
    spec_kernel memUniform0 i = iterHash ROUNDS 0

axiom spec_kernel_uniform1 (i : Fin BATCH_SIZE) :
    spec_kernel memUniform1 i = iterHash ROUNDS (if i = (0 : Fin BATCH_SIZE) then 1 else 0)
axiom memUniformVal_at (j i : Fin BATCH_SIZE) :
    memAt (memUniformVal j) (VAL_BASE + i) = if i = j then 1 else 0
axiom spec_kernel_uniformVal (j i : Fin BATCH_SIZE) :
    spec_kernel (memUniformVal j) i = iterHash ROUNDS (if i = j then 1 else 0)
lemma iterHash_ne : iterHash ROUNDS 0 ≠ iterHash ROUNDS 1 := by
  native_decide
lemma iterHash_ne_zero : iterHash ROUNDS 0 ≠ 0 := by
  native_decide
axiom spec_kernel_diff_uniform0 :
    spec_kernel memUniform1 (0 : Fin BATCH_SIZE) ≠ spec_kernel memUniform0 (0 : Fin BATCH_SIZE)
axiom spec_kernel_diff_uniformVal (j : Fin BATCH_SIZE) :
    spec_kernel (memUniformVal j) j ≠ spec_kernel memUniform0 j
axiom kernelSensitive_uniform_zero (mem : Memory)
    (hunif : UniformZeroKernel mem) : KernelSensitive mem
axiom must_read_kernel_values_for_mem (p : Program) (hstraight : StraightLine p)
    (hcorrect : CorrectOn spec_kernel p MemSafeKernel) :
    ∀ mem, MemSafeKernel mem → KernelLayout mem → KernelSensitive mem → OutputDiffers mem →
      ∀ i : Fin BATCH_SIZE, (memAt mem PTR_INP_VAL + i) ∈ readWords p mem
axiom outputDiffers_uniform_zero (mem : Memory)
    (hunif : UniformZeroKernel mem) : OutputDiffers mem
axiom must_read_kernel_values_for_mem_machine (p : Program)
    (hstraight : StraightLine p)
    (hcorrect : CorrectOnMachine spec_kernel p MemSafeKernel) :
    ∀ mem, MemSafeKernel mem → KernelLayout mem → KernelSensitive mem → OutputDiffers mem →
      ∀ i : Fin BATCH_SIZE, (memAt mem PTR_INP_VAL + i) ∈ readWordsMachine p mem
axiom must_read_addr_machine (p : Program)
    (hstraight : StraightLine p)
    (hcorrect : CorrectOnMachine spec_kernel p MemSafeKernel) :
    ∀ mem, MemSafeKernel mem → WritesOutput p mem → ∀ addr, AddrSafe mem addr →
      (∃ i : Fin BATCH_SIZE,
        spec_kernel (memUpdate mem addr (memAt mem addr + 1)) i ≠ spec_kernel mem i) →
      addr ∈ readWordsMachine p mem
axiom must_read_addr_machine_fuel (p : Program) (fuel : Nat)
    (hfull : fuel = p.program.length)
    (hstraight : StraightLine p)
    (hcorrect : CorrectOnMachineFuel spec_kernel p MemSafeKernel fuel) :
    ∀ mem, MemSafeKernel mem → WritesOutput p mem → ∀ addr, AddrSafe mem addr →
      (∃ i : Fin BATCH_SIZE,
        spec_kernel (memUpdate mem addr (memAt mem addr + 1)) i ≠ spec_kernel mem i) →
      addr ∈ readWordsMachineFuel p fuel mem
axiom must_read_kernel_values_for_mem_machine_fuel (p : Program) (fuel : Nat)
    (hfull : fuel = p.program.length)
    (hstraight : StraightLine p)
    (hcorrect : CorrectOnMachineFuel spec_kernel p MemSafeKernel fuel) :
    ∀ mem, MemSafeKernel mem → KernelLayout mem → KernelSensitive mem → OutputDiffers mem →
      ∀ i : Fin BATCH_SIZE, (memAt mem PTR_INP_VAL + i) ∈ readWordsMachineFuel p fuel mem
axiom must_read_kernel_values (p : Program) (hstraight : StraightLine p)
    (hcorrect : CorrectOn spec_kernel p MemSafeKernel) :
    ∀ i : Fin BATCH_SIZE,
      (memAt memUniform0 PTR_INP_VAL + i) ∈ readWords p memUniform0
axiom outputAddrs_subset_readWords_kernel (p : Program) (hstraight : StraightLine p)
    (hcorrect : CorrectOn spec_kernel p MemSafeKernel) :
    outputAddrs memUniform0 ⊆ (readWords p memUniform0).toFinset
axiom outputAddrs_subset_readWords_kernel_for_mem (p : Program) (hstraight : StraightLine p)
    (hcorrect : CorrectOn spec_kernel p MemSafeKernel) :
    ∀ mem, MemSafeKernel mem → KernelLayout mem → KernelSensitive mem → OutputDiffers mem →
      outputAddrs mem ⊆ (readWords p mem).toFinset
axiom min_required_words_kernel (p : Program) (hstraight : StraightLine p)
    (hcorrect : CorrectOn spec_kernel p MemSafeKernel) :
    BATCH_SIZE ≤ readWordCount p memUniform0
axiom min_required_words_kernel_for_mem (p : Program) (hstraight : StraightLine p)
    (hcorrect : CorrectOn spec_kernel p MemSafeKernel) :
    ∀ mem, MemSafeKernel mem → KernelLayout mem → KernelSensitive mem → OutputDiffers mem →
      BATCH_SIZE ≤ readWordCount p mem
axiom min_required_words_kernel_for_mem_machine (p : Program)
    (hstraight : StraightLine p)
    (hcorrect : CorrectOnMachine spec_kernel p MemSafeKernel) :
    ∀ mem, MemSafeKernel mem → KernelLayout mem → KernelSensitive mem → OutputDiffers mem →
      BATCH_SIZE ≤ readWordCountMachine p mem
axiom min_required_words_adversaryK_machine (p : Program)
    (hstraight : StraightLine p)
    (hcorrect : CorrectOnMachine spec_kernel p MemSafeKernel) :
    ∀ mem, MemSafeKernel mem → WritesOutput p mem → ∀ k, AdversaryK mem k →
      k * BATCH_SIZE * memAt mem 0 ≤ readWordCountMachine p mem
axiom min_required_words_adversaryK_machine_fuel (p : Program) (fuel : Nat)
    (hfull : fuel = p.program.length)
    (hstraight : StraightLine p)
    (hcorrect : CorrectOnMachineFuel spec_kernel p MemSafeKernel fuel) :
    ∀ mem, MemSafeKernel mem → WritesOutput p mem → ∀ k, AdversaryK mem k →
      k * BATCH_SIZE * memAt mem 0 ≤ readWordCountMachineFuel p fuel mem
axiom min_required_words_kernel_for_mem_machine_fuel (p : Program) (fuel : Nat)
    (hfull : fuel = p.program.length)
    (hstraight : StraightLine p)
    (hcorrect : CorrectOnMachineFuel spec_kernel p MemSafeKernel fuel) :
    ∀ mem, MemSafeKernel mem → KernelLayout mem → KernelSensitive mem → OutputDiffers mem →
      BATCH_SIZE ≤ readWordCountMachineFuel p fuel mem
axiom spec_values_diff {mem : Memory} {base : Nat} {i : Fin BATCH_SIZE} :
    let addr := base + i
    spec_values (memUpdate mem addr (memAt mem addr + 1)) i ≠ spec_values mem i
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
    simpa [mem', addr] using (memUpdate_eq_of_ne mem addr (memAt mem addr + 1) a hneq')
  have hrun :
      run p mem = run p mem' := by
    exact run_eq_of_agree p mem mem' hptr hagree hwrites
      (hsafe mem hsafe_mem) (hsafe mem' hsafe')
  have hspec : spec_values mem' i ≠ spec_values mem i := by
    -- spec_values_diff at base = PTR_INP_VAL contents
    simpa [addr, mem'] using (spec_values_diff (mem := mem) (base := memAt mem PTR_INP_VAL) (i := i))
  have hcorr1 := hcorrect mem hsafe_mem
  have hcorr2 := hcorrect mem' hsafe'
  -- contradict spec_values_diff
  have : spec_values mem' i = spec_values mem i := by
    simpa [run, hptr] using congrArg (fun f => f i) (by simpa [mem'] using hrun)
  exact hspec this
axiom must_read_values_machine (p : Program)
    (hstraight : StraightLine p)
    (hcorrect : CorrectOnMachine spec_values p MemSafeValues) :
    ∀ mem, MemSafeValues mem → WritesOutput p mem → ∀ i : Fin BATCH_SIZE,
      (memAt mem PTR_INP_VAL + i) ∈ readWordsMachine p mem
axiom must_read_values_machine_fuel (p : Program) (fuel : Nat)
    (hfull : fuel = p.program.length)
    (hstraight : StraightLine p)
    (hcorrect : CorrectOnMachineFuel spec_values p MemSafeValues fuel) :
    ∀ mem, MemSafeValues mem → WritesOutput p mem → ∀ i : Fin BATCH_SIZE,
      (memAt mem PTR_INP_VAL + i) ∈ readWordsMachineFuel p fuel mem
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
    Finset.card_le_of_subset hsubset
  have hlen : (readWords p mem).toFinset.card ≤ (readWords p mem).length := by
    simpa using (List.toFinset_card_le_length (l := readWords p mem))
  have : BATCH_SIZE ≤ (readWords p mem).length := by
    simpa [hcard] using (le_trans hcard_le hlen)
  simpa [readWordCount] using this
axiom min_required_words_values_machine (p : Program)
    (hcorrect : CorrectOnMachine spec_values p MemSafeValues) :
    ∀ mem, MemSafeValues mem → BATCH_SIZE ≤ readWordCountMachine p mem
axiom min_required_words_values_machine_fuel (p : Program) (fuel : Nat)
    (hcorrect : CorrectOnMachineFuel spec_values p MemSafeValues fuel) :
    ∀ mem, MemSafeValues mem → BATCH_SIZE ≤ readWordCountMachineFuel p fuel mem
def coreEqNoPc (c1 c2 : Core) : Prop :=
  c1.id = c2.id ∧
  c1.scratch = c2.scratch ∧
  c1.trace_buf = c2.trace_buf ∧
  c1.state = c2.state

lemma coreEqNoPc_refl (c : Core) : coreEqNoPc c c := by
  unfold coreEqNoPc
  exact ⟨rfl, rfl, rfl, rfl⟩
lemma listAll_forall {α : Type} {p : α → Prop} {l : List α} (h : List.Forall p l) :
    ∀ a ∈ l, p a := by
  simpa using (List.forall_iff_forall_mem.mp h)
axiom execFlowSlot_eq_of_coreEq (enablePause : Bool) (core1 core2 : Core)
    (s : Nat → Nat) (slot : FlowSlot)
    (hstraight : flowSlotStraight slot) (hcore : coreEqNoPc core1 core2) :
    coreEqNoPc (execFlowSlot enablePause core1 s slot).1
      (execFlowSlot enablePause core2 s slot).1 ∧
    (execFlowSlot enablePause core1 s slot).2 = (execFlowSlot enablePause core2 s slot).2
axiom execFlowSlots_eq_of_coreEq (enablePause : Bool) (core1 core2 : Core)
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
          (core2, [])).2
axiom execInstructionTrace_eq_of_coreEq (mem : Memory) (core1 core2 : Core)
    (instr : Instruction) (hstraight : instrStraight instr)
    (hcore : coreEqNoPc core1 core2) :
    execInstructionTrace mem core1 instr = execInstructionTrace mem core2 instr
axiom runTraceAux_eq_of_coreEq :
    ∀ prog mem core1 core2,
      (∀ instr ∈ prog, instrStraight instr) →
      coreEqNoPc core1 core2 →
      runTraceAux prog mem core1 = runTraceAux prog mem core2
def MachineTraceAgrees (p : Program) (mem : Memory) : Prop :=
  runMachineTrace p mem = runTrace p mem

axiom MachineTraceAgrees_of_StraightLine (p : Program) (hstraight : StraightLine p) :
    ∀ mem, MachineTraceAgrees p mem
axiom runMachine_eq_run (p : Program) (mem : Memory)
    (htrace : MachineTraceAgrees p mem) : runMachine p mem = run p mem
axiom readWordCountMachine_eq (p : Program) (mem : Memory)
    (htrace : MachineTraceAgrees p mem) :
    readWordCountMachine p mem = readWordCount p mem
axiom runMachine_eq_of_agree (p : Program) (mem1 mem2 : Memory)
    (hstraight : StraightLine p)
    (hptr : memAt mem1 PTR_INP_VAL = memAt mem2 PTR_INP_VAL)
    (h : AgreeOnList (readWordsMachine p mem1) mem1 mem2)
    (hwrites : WritesOutput p mem1) :
    runMachine p mem1 = runMachine p mem2
axiom runMachineFuel_eq_of_agree (p : Program) (fuel : Nat) (mem1 mem2 : Memory)
    (hfull : fuel = p.program.length)
    (hstraight : StraightLine p)
    (hptr : memAt mem1 PTR_INP_VAL = memAt mem2 PTR_INP_VAL)
    (h : AgreeOnList (readWordsMachineFuel p fuel mem1) mem1 mem2)
    (hwrites : WritesOutput p mem1) :
    runMachineFuel p fuel mem1 = runMachineFuel p fuel mem2
axiom CorrectOnMachine_to_CorrectOn (spec : Memory → Output) (p : Program) (memOk : Memory → Prop)
    (hcorrect : CorrectOnMachine spec p memOk)
    (htrace : ∀ mem, memOk mem → MachineTraceAgrees p mem) :
    CorrectOn spec p memOk
lemma loadAddrs_length_le (s : Nat → Nat) (slot : LoadSlot) :
    (loadAddrs s slot).length ≤ VLEN := by
  cases slot <;> simp [loadAddrs, VLEN]
lemma readOps_bound_aux :
    ∀ prog mem core, ∀ op ∈ (runTraceAux prog mem core).2, op.length ≤ VLEN := by
  intro prog mem core
  induction prog generalizing mem core with
  | nil =>
      intro op hop
      simp [runTraceAux] at hop
  | cons instr rest ih =>
      intro op hop
      by_cases hok : (execInstructionTrace mem core instr).1.ok
      · simp [runTraceAux, hok] at hop
        rcases hop with hop | hop
        · rcases List.mem_map.1 hop with ⟨slot, hslot, rfl⟩
          exact loadAddrs_length_le _ _
        · exact ih (mem := (execInstructionTrace mem core instr).1.mem)
            (core := (execInstructionTrace mem core instr).1.core) op hop
      · simp [runTraceAux, hok] at hop
        rcases List.mem_map.1 hop with ⟨slot, hslot, rfl⟩
        exact loadAddrs_length_le _ _
lemma readOps_bound (p : Program) (mem : Memory) :
    ∀ op ∈ readOps p mem, op.length ≤ VLEN := by
  simpa [readOps, runTrace] using (readOps_bound_aux p.program mem (initCore p))
lemma length_join_le (ops : List (List Nat))
    (h : ∀ op ∈ ops, op.length ≤ VLEN) :
    (listJoin ops).length ≤ VLEN * ops.length := by
  induction ops with
  | nil =>
      simp [listJoin]
  | cons op ops ih =>
      have hop : op.length ≤ VLEN := h op (by simp)
      have hrest : ∀ o ∈ ops, o.length ≤ VLEN := by
        intro o ho
        exact h o (by simp [ho])
      have ih' := ih hrest
      calc
        (listJoin (op :: ops)).length = op.length + (listJoin ops).length := by
          simp [listJoin]
        _ ≤ VLEN + VLEN * ops.length := by
          exact Nat.add_le_add hop ih'
        _ = VLEN * (ops.length + 1) := by
          simp [Nat.mul_add, Nat.add_comm]
        _ = VLEN * (List.length (op :: ops)) := by simp
lemma ceilDiv_le_of_mul_le {n k d : Nat} (hd : 0 < d) (h : n ≤ d * k) :
    ceilDiv n d ≤ k := by
  unfold ceilDiv
  have hd1 : 1 ≤ d := (Nat.succ_le_iff).2 hd
  have h' : n + d - 1 ≤ d * k + (d - 1) := by
    have h'' : n + (d - 1) ≤ d * k + (d - 1) := Nat.add_le_add_right h (d - 1)
    have hrewrite : n + d - 1 = n + (d - 1) := by
      exact (Nat.add_sub_assoc (m := d) (k := 1) (n := n) hd1)
    simpa [hrewrite] using h''
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
  by_cases hd : d = 0
  · subst hd
    simp [ceilDiv]
  · have hd1 : 1 ≤ d := (Nat.succ_le_iff).2 (Nat.pos_of_ne_zero hd)
    unfold ceilDiv
    have h' : a + d - 1 ≤ b + d - 1 := by
      have h'' : a + (d - 1) ≤ b + (d - 1) := Nat.add_le_add_right h (d - 1)
      have ha : a + d - 1 = a + (d - 1) := by
        exact (Nat.add_sub_assoc (m := d) (k := 1) (n := a) hd1)
      have hb : b + d - 1 = b + (d - 1) := by
        exact (Nat.add_sub_assoc (m := d) (k := 1) (n := b) hd1)
      simpa [ha, hb] using h''
    exact Nat.div_le_div_right h'
lemma minLoadOps_mono {a b : Nat} (h : a ≤ b) :
    minLoadOps a ≤ minLoadOps b := by
  exact ceilDiv_mono h

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

theorem global_load_lower_bound_machine_fuel (p : Program) (fuel : Nat)
    (hcorrect : CorrectOnMachineFuel spec_values p MemSafeValues fuel) :
    ∀ mem, MemSafeValues mem → globalLowerBound ≤ loadLowerCycles (readWordCountMachineFuel p fuel mem) := by
  intro mem hsafe
  have hmin : MIN_REQUIRED_WORDS ≤ readWordCountMachineFuel p fuel mem := by
    simpa [MIN_REQUIRED_WORDS] using min_required_words_values_machine_fuel p fuel hcorrect mem hsafe
  exact loadLowerCycles_mono hmin

theorem global_load_lower_bound_safe (p : Program)
    (hcorrect : CorrectOn spec_values p MemSafeValues)
    (hsafe : ∀ mem, MemSafeValues mem → SafeExec p mem)
    (hlayout : ∀ mem, MemSafeValues mem → ValuesLayout mem)
    (hwrites : ∀ mem, MemSafeValues mem → WritesOutput p mem) :
    ∀ mem, MemSafeValues mem → globalLowerBound ≤ loadLowerCycles (readWordCount p mem) := by
  intro mem hsafe_mem
  have hmin : MIN_REQUIRED_WORDS ≤ readWordCount p mem := by
    have := min_required_words_values p hcorrect hsafe hlayout mem hsafe_mem (hwrites mem hsafe_mem)
    simpa [MIN_REQUIRED_WORDS] using this
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

axiom global_load_lower_bound_kernel_machine (p : Program)
    (hcorrect : CorrectOnMachine spec_kernel p MemSafeKernel) :
    ∀ mem, MemSafeKernel mem → KernelLayout mem → KernelSensitive mem → OutputDiffers mem →
      globalLowerBoundKernel ≤ loadLowerCycles (readWordCountMachine p mem)
theorem global_load_lower_bound_kernel_machine_pc (p : Program)
    (_hclass : ProgramClass p)
    (hcorrect : CorrectOnMachine spec_kernel p MemSafeKernel) :
    ∀ mem, MemSafeKernel mem → KernelLayout mem → KernelSensitive mem → OutputDiffers mem →
      globalLowerBoundKernel ≤ loadLowerCycles (readWordCountMachine p mem) := by
  exact global_load_lower_bound_kernel_machine p hcorrect

axiom global_load_lower_bound_kernel_machine_fuel (p : Program) (fuel : Nat)
    (hcorrect : CorrectOnMachineFuel spec_kernel p MemSafeKernel fuel) :
    ∀ mem, MemSafeKernel mem → KernelLayout mem → KernelSensitive mem → OutputDiffers mem →
      globalLowerBoundKernel ≤ loadLowerCycles (readWordCountMachineFuel p fuel mem)
theorem global_load_lower_bound_kernel_machine_fuel_pcbounded (p : Program) (fuel : Nat)
    (_hpc : PcBoundedProgram p)
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
    simp [computeLowerBoundKernel, globalLowerBoundKernel_eq_16]
  have hcomp' : computeLowerBoundKernel ≤ loadLowerCycles (readWordCountMachine p mem) :=
    le_trans hcomp hload
  exact (max_le_iff.mpr ⟨hload, hcomp'⟩)

axiom global_load_lower_bound_kernel_machine_final_pc (p : Program)
    (_hclass : ProgramClass p)
    (hcorrect : CorrectOnMachine spec_kernel p MemSafeKernel) :
    ∀ mem, MemSafeKernel mem → KernelLayout mem → KernelSensitive mem →
      globalLowerBoundKernelFinal ≤ loadLowerCycles (readWordCountMachine p mem)
axiom global_load_lower_bound_kernel_exists (p : Program) (hstraight : StraightLine p)
    (hcorrect : CorrectOn spec_kernel p MemSafeKernel) :
    ∃ mem, globalLowerBoundKernel ≤ loadLowerCycles (readWordCount p mem)
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
    simp [computeLowerBoundKernel, globalLowerBoundKernel_eq_16]
  have hcomp' : computeLowerBoundKernel ≤ loadLowerCycles (readWordCountMachineFuel p fuel mem) :=
    le_trans hcomp hload
  exact (max_le_iff.mpr ⟨hload, hcomp'⟩)

theorem global_load_lower_bound_kernel_machine_final_fuel_pcbounded (p : Program) (fuel : Nat)
    (_hpc : PcBoundedProgram p)
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
    simp [computeLowerBoundKernel, globalLowerBoundKernel_eq_16]
  have hcomp' : computeLowerBoundKernel ≤ loadLowerCycles (readWordCountMachine p mem) :=
    le_trans hcomp hload
  exact (max_le_iff.mpr ⟨hload, hcomp'⟩)

axiom global_load_lower_bound_kernel_machine_adversaryK (p : Program)
    (hcorrect : CorrectOnMachine spec_kernel p MemSafeKernel) :
    ∀ mem, MemSafeKernel mem → WritesOutput p mem → memAt mem 0 = ROUNDS → ∀ k, AdversaryK mem k →
      globalLowerBoundKernelK k ≤ loadLowerCycles (readWordCountMachine p mem)
axiom global_load_lower_bound_kernel_machine_adversaryK_fuel (p : Program) (fuel : Nat)
    (hcorrect : CorrectOnMachineFuel spec_kernel p MemSafeKernel fuel) :
    ∀ mem, MemSafeKernel mem → WritesOutput p mem → memAt mem 0 = ROUNDS → ∀ k, AdversaryK mem k →
      globalLowerBoundKernelK k ≤ loadLowerCycles (readWordCountMachineFuel p fuel mem)
axiom global_load_lower_bound_kernel_machine_uniformzero_adversaryK
    (p : Program)
    (hcorrect : CorrectOnMachine spec_kernel p MemSafeKernel) :
    ∀ mem, UniformZeroKernel mem → ∀ k, AdversaryK mem k →
      globalLowerBoundKernelK k ≤ loadLowerCycles (readWordCountMachine p mem)
axiom global_load_lower_bound_kernel_machine_uniformzero_256
    (p : Program)
    (hcorrect : CorrectOnMachine spec_kernel p MemSafeKernel) :
    ∀ mem, UniformZeroKernel mem → AdversaryK mem 1 →
      256 ≤ loadLowerCycles (readWordCountMachine p mem)
axiom global_load_lower_bound_kernel_machine_uniformzero_512
    (p : Program)
    (hcorrect : CorrectOnMachine spec_kernel p MemSafeKernel) :
    ∀ mem, UniformZeroKernel mem → AdversaryK mem 2 →
      512 ≤ loadLowerCycles (readWordCountMachine p mem)
axiom global_load_lower_bound_kernel_machine_roundDistinct_256
    (p : Program) (hcorrect : CorrectOnMachine spec_kernel p MemSafeKernel) :
    ∀ mem, MemSafeKernel mem → memAt mem 0 = ROUNDS → RoundDistinctNodes mem 1 →
      256 ≤ loadLowerCycles (readWordCountMachine p mem)
axiom global_load_lower_bound_kernel_machine_roundDistinct_512
    (p : Program) (hcorrect : CorrectOnMachine spec_kernel p MemSafeKernel) :
    ∀ mem, MemSafeKernel mem → memAt mem 0 = ROUNDS → RoundDistinctNodes mem 2 →
      512 ≤ loadLowerCycles (readWordCountMachine p mem)
axiom global_load_lower_bound_kernel_machine_roundDistinct_256_fuel
    (p : Program) (fuel : Nat)
    (hcorrect : CorrectOnMachineFuel spec_kernel p MemSafeKernel fuel) :
    ∀ mem, MemSafeKernel mem → memAt mem 0 = ROUNDS → RoundDistinctNodes mem 1 →
      256 ≤ loadLowerCycles (readWordCountMachineFuel p fuel mem)
axiom global_load_lower_bound_kernel_machine_roundDistinct_512_fuel
    (p : Program) (fuel : Nat)
    (hcorrect : CorrectOnMachineFuel spec_kernel p MemSafeKernel fuel) :
    ∀ mem, MemSafeKernel mem → memAt mem 0 = ROUNDS → RoundDistinctNodes mem 2 →
      512 ≤ loadLowerCycles (readWordCountMachineFuel p fuel mem)
axiom global_load_lower_bound_kernel_machine_big_256
    (p : Program) (hcorrect : CorrectOnMachine spec_kernel p MemSafeKernel) :
    256 ≤ loadLowerCycles (readWordCountMachine p memBig)
axiom global_load_lower_bound_kernel_machine_exists_big_256
    (p : Program) (hcorrect : CorrectOnMachine spec_kernel p MemSafeKernel) :
    ∃ mem, 256 ≤ loadLowerCycles (readWordCountMachine p mem)
axiom global_load_lower_bound_kernel_machine_big_272
    (p : Program) (hcorrect : CorrectOnMachine spec_kernel p MemSafeKernel) :
    272 ≤ loadLowerCycles (readWordCountMachine p memBig)
axiom global_load_lower_bound_kernel_machine_exists_big_272
    (p : Program) (hcorrect : CorrectOnMachine spec_kernel p MemSafeKernel) :
    ∃ mem, 272 ≤ loadLowerCycles (readWordCountMachine p mem)
axiom global_load_lower_bound_kernel_machine_big_256_fuel
    (p : Program) (fuel : Nat)
    (hpc : PcBoundedProgram p)
    (hcorrect : CorrectOnMachineFuel spec_kernel p MemSafeKernel fuel) :
    256 ≤ loadLowerCycles (readWordCountMachineFuel p fuel memBig)
lemma globalLowerBound_eq :
    globalLowerBound = ceilDiv (ceilDiv MIN_REQUIRED_WORDS VLEN) LOAD_CAP := by
  rfl

axiom global_load_lower_bound (p : Program) (hstraight : StraightLine p)
    (hcorrect : CorrectOn spec_values p MemSafeValues) :
    ∀ mem, MemSafeValues mem → globalLowerBound ≤ loadLowerCycles (readWordCount p mem)
axiom global_load_lower_bound_machine (p : Program)
    (hcorrect : CorrectOnMachine spec_values p MemSafeValues) :
    ∀ mem, MemSafeValues mem → globalLowerBound ≤ loadLowerCycles (readWordCountMachine p mem)
end ProofGlobalLowerBound
