import Mathlib
import proofs.common.ISA

namespace ProofMachine
open ProofISA



/-! ### ISA constants (from problem.py) -/


/-! ### Basic helpers -/

def mod32 (x : Nat) : Nat :=
  x % MOD32

def cdiv (a b : Nat) : Nat :=
  if b = 0 then 0 else (a + b - 1) / b

def natAnd (a b : Nat) : Nat :=
  Nat.bitwise (fun x y => x && y) a b

def natOr (a b : Nat) : Nat :=
  Nat.bitwise (fun x y => x || y) a b

def natXor (a b : Nat) : Nat :=
  Nat.bitwise (fun x y => x != y) a b

def shl (a b : Nat) : Nat :=
  mod32 (a * (2 ^ b))

def shr (a b : Nat) : Nat :=
  mod32 (a / (2 ^ b))

/-! ### Core state -/

inductive CoreState
  | running
  | paused
  | stopped
  deriving DecidableEq, Repr

structure Core where
  id : Nat
  scratch : Nat → Nat
  trace_buf : List Nat
  pc : Int
  state : CoreState

structure Mem where
  data : Nat → Nat
  size : Nat

def memRead (m : Mem) (addr : Nat) : Option Nat :=
  if addr < m.size then some (m.data addr) else none

def memWrite (m : Mem) (addr val : Nat) : Option Mem :=
  if addr < m.size then
    some { m with data := fun a => if a = addr then val else m.data a }
  else
    none

def memWriteMany (m : Mem) (ws : List (Nat × Nat)) : Option Mem :=
  ws.foldl
    (fun acc w =>
      match acc with
      | none => none
      | some m' => memWrite m' w.1 w.2)
    (some m)

def listGet? {α : Type} : List α → Nat → Option α
  | [], _ => none
  | x :: _, 0 => some x
  | _ :: xs, n + 1 => listGet? xs n

/-! ### Instruction slots -/

inductive AluOp
  | add | sub | mul | idiv | cdiv | xor | band | bor | shl | shr | mod | lt | eq
  deriving DecidableEq, Repr

structure AluSlot where
  op : AluOp
  dest : Nat
  a1 : Nat
  a2 : Nat
  deriving Repr

inductive ValuSlot
  | vbroadcast (dest src : Nat)
  | multiply_add (dest a b c : Nat)
  | alu (op : AluOp) (dest a1 a2 : Nat)
  deriving Repr

inductive LoadSlot
  | load (dest addr : Nat)
  | load_offset (dest addr offset : Nat)
  | vload (dest addr : Nat)
  | const (dest val : Nat)
  deriving Repr

inductive StoreSlot
  | store (addr src : Nat)
  | vstore (addr src : Nat)
  deriving Repr

inductive FlowSlot
  | select (dest cond a b : Nat)
  | add_imm (dest a imm : Nat)
  | vselect (dest cond a b : Nat)
  | halt
  | pause
  | trace_write (val : Nat)
  | cond_jump (cond : Nat) (addr : Int)
  | cond_jump_rel (cond : Nat) (offset : Int)
  | jump (addr : Int)
  | jump_indirect (addr : Nat)
  | coreid (dest : Nat)
  deriving Repr

inductive DebugSlot
  | compare (loc key : Nat)
  | vcompare (loc : Nat) (keys : List Nat)
  deriving Repr

structure Instruction where
  alu : List AluSlot := []
  valu : List ValuSlot := []
  load : List LoadSlot := []
  store : List StoreSlot := []
  flow : List FlowSlot := []
  debug : List DebugSlot := []
  deriving Repr

/-! ### Well-formedness -/

def vecInScratch (base : Nat) : Prop :=
  base + (VLEN - 1) < SCRATCH_SIZE

def aluSlotBounded (s : AluSlot) : Prop :=
  s.dest < SCRATCH_SIZE ∧ s.a1 < SCRATCH_SIZE ∧ s.a2 < SCRATCH_SIZE

def valuSlotBounded : ValuSlot → Prop
  | .vbroadcast dest src =>
      vecInScratch dest ∧ src < SCRATCH_SIZE
  | .multiply_add dest a b c =>
      vecInScratch dest ∧ vecInScratch a ∧ vecInScratch b ∧ vecInScratch c
  | .alu _ dest a1 a2 =>
      vecInScratch dest ∧ vecInScratch a1 ∧ vecInScratch a2

def loadSlotBounded : LoadSlot → Prop
  | .load dest addr =>
      dest < SCRATCH_SIZE ∧ addr < SCRATCH_SIZE
  | .load_offset dest addr offset =>
      dest + offset < SCRATCH_SIZE ∧ addr + offset < SCRATCH_SIZE
  | .vload dest addr =>
      vecInScratch dest ∧ addr < SCRATCH_SIZE
  | .const dest _ =>
      dest < SCRATCH_SIZE

def storeSlotBounded : StoreSlot → Prop
  | .store addr src =>
      addr < SCRATCH_SIZE ∧ src < SCRATCH_SIZE
  | .vstore addr src =>
      addr < SCRATCH_SIZE ∧ vecInScratch src

def flowSlotBounded : FlowSlot → Prop
  | .select dest cond a b =>
      dest < SCRATCH_SIZE ∧ cond < SCRATCH_SIZE ∧ a < SCRATCH_SIZE ∧ b < SCRATCH_SIZE
  | .add_imm dest a _ =>
      dest < SCRATCH_SIZE ∧ a < SCRATCH_SIZE
  | .vselect dest cond a b =>
      vecInScratch dest ∧ vecInScratch cond ∧ vecInScratch a ∧ vecInScratch b
  | .trace_write val =>
      val < SCRATCH_SIZE
  | .cond_jump cond _ =>
      cond < SCRATCH_SIZE
  | .cond_jump_rel cond _ =>
      cond < SCRATCH_SIZE
  | .jump _ =>
      True
  | .jump_indirect addr =>
      addr < SCRATCH_SIZE
  | .coreid dest =>
      dest < SCRATCH_SIZE
  | .halt => True
  | .pause => True

def debugSlotBounded : DebugSlot → Prop
  | .compare loc _ =>
      loc < SCRATCH_SIZE
  | .vcompare loc _ =>
      vecInScratch loc

def instrScratchBounded (i : Instruction) : Prop :=
  (∀ s ∈ i.alu, aluSlotBounded s) ∧
  (∀ s ∈ i.valu, valuSlotBounded s) ∧
  (∀ s ∈ i.load, loadSlotBounded s) ∧
  (∀ s ∈ i.store, storeSlotBounded s) ∧
  (∀ s ∈ i.flow, flowSlotBounded s) ∧
  (∀ s ∈ i.debug, debugSlotBounded s)

def flowSlotPcBoundedAt (progLen pc : Nat) : FlowSlot → Prop
  | .cond_jump _ addr =>
      0 ≤ addr ∧ addr < Int.ofNat progLen
  | .cond_jump_rel _ offset =>
      let pc' := (Int.ofNat pc) + offset
      0 ≤ pc' ∧ pc' < Int.ofNat progLen
  | .jump addr =>
      0 ≤ addr ∧ addr < Int.ofNat progLen
  | _ => True

def instrPcBoundedAt (progLen pc : Nat) (i : Instruction) : Prop :=
  List.Forall (flowSlotPcBoundedAt progLen pc) i.flow

def instrPcBounded (progLen : Nat) (i : Instruction) : Prop :=
  instrPcBoundedAt progLen 0 i

def instrWellFormed (i : Instruction) : Prop :=
  i.alu.length ≤ ALU_CAP ∧
  i.valu.length ≤ VALU_CAP ∧
  i.load.length ≤ LOAD_CAP ∧
  i.store.length ≤ STORE_CAP ∧
  i.flow.length ≤ FLOW_CAP ∧
  instrScratchBounded i

noncomputable instance (i : Instruction) : Decidable (instrWellFormed i) := by
  classical
  infer_instance

def instrHasNonDebug (i : Instruction) : Bool :=
  (!i.alu.isEmpty) || (!i.valu.isEmpty) || (!i.load.isEmpty) || (!i.store.isEmpty) || (!i.flow.isEmpty)

/-! ### Write helpers -/

def write (m : Nat → Nat) (addr : Nat) (val : Nat) : Nat → Nat :=
  fun a => if a = addr then val else m a

def writeMany (m : Nat → Nat) (ws : List (Nat × Nat)) : Nat → Nat :=
  ws.foldl (fun acc w => write acc w.1 w.2) m

def vecWrites (dest : Nat) (f : Nat → Nat) : List (Nat × Nat) :=
  (List.range VLEN).map (fun i => (dest + i, f i))

/-! ### ALU semantics -/

def aluEval (op : AluOp) (a1 a2 : Nat) : Nat :=
  match op with
  | .add => mod32 (a1 + a2)
  | .sub => mod32 (a1 + MOD32 - a2)
  | .mul => mod32 (a1 * a2)
  | .idiv => if a2 = 0 then 0 else mod32 (a1 / a2)
  | .cdiv => mod32 (cdiv a1 a2)
  | .xor => mod32 (natXor a1 a2)
  | .band => mod32 (natAnd a1 a2)
  | .bor => mod32 (natOr a1 a2)
  | .shl => shl a1 a2
  | .shr => shr a1 a2
  | .mod => if a2 = 0 then 0 else mod32 (a1 % a2)
  | .lt => if a1 < a2 then 1 else 0
  | .eq => if a1 = a2 then 1 else 0

def aluDivZero (op : AluOp) (a2 : Nat) : Bool :=
  match op with
  | .idiv | .cdiv | .mod => a2 = 0
  | _ => false

def vecDivZero (op : AluOp) (s : Nat → Nat) (a2 : Nat) : Bool :=
  match op with
  | .idiv | .cdiv | .mod =>
      (List.range VLEN).any (fun i => s (a2 + i) = 0)
  | _ => false

def execAluSlot (s : Nat → Nat) (slot : AluSlot) : Option (List (Nat × Nat)) :=
  if aluDivZero slot.op (s slot.a2) then
    none
  else
    let res := aluEval slot.op (s slot.a1) (s slot.a2)
    some [(slot.dest, res)]

def execValuSlot (s : Nat → Nat) (slot : ValuSlot) : Option (List (Nat × Nat)) :=
  match slot with
  | .vbroadcast dest src =>
      some (vecWrites dest (fun _ => s src))
  | .multiply_add dest a b c =>
      some (vecWrites dest (fun i => mod32 ((s (a + i) * s (b + i)) + s (c + i))))
  | .alu op dest a1 a2 =>
      if vecDivZero op s a2 then
        none
      else
        some (vecWrites dest (fun i => aluEval op (s (a1 + i)) (s (a2 + i))))

def execAluSlots (s : Nat → Nat) (slots : List AluSlot) : Option (List (Nat × Nat)) :=
  slots.foldl
    (fun acc slot =>
      match acc with
      | none => none
      | some ws =>
          match execAluSlot s slot with
          | none => none
          | some ws' => some (ws ++ ws'))
    (some [])

def execValuSlots (s : Nat → Nat) (slots : List ValuSlot) : Option (List (Nat × Nat)) :=
  slots.foldl
    (fun acc slot =>
      match acc with
      | none => none
      | some ws =>
          match execValuSlot s slot with
          | none => none
          | some ws' => some (ws ++ ws'))
    (some [])

def execLoadSlot (s : Nat → Nat) (m : Mem) (slot : LoadSlot) :
    Option (List (Nat × Nat)) :=
  match slot with
  | .load dest addr =>
      match memRead m (s addr) with
      | none => none
      | some v => some [(dest, v)]
  | .load_offset dest addr offset =>
      match memRead m (s (addr + offset)) with
      | none => none
      | some v => some [(dest + offset, v)]
  | .vload dest addr =>
      let base := s addr
      let vals := (List.range VLEN).map (fun i => memRead m (base + i))
      if vals.all (fun v => v.isSome) then
        let reads := (List.range VLEN).map (fun i =>
          (dest + i, (memRead m (base + i)).get!))
        some reads
      else
        none
  | .const dest val =>
      some [(dest, mod32 val)]

def execStoreSlot (s : Nat → Nat) (slot : StoreSlot) : List (Nat × Nat) :=
  match slot with
  | .store addr src =>
      [(s addr, s src)]
  | .vstore addr src =>
      let base := s addr
      vecWrites base (fun i => s (src + i))

def execFlowSlot (enablePause : Bool) (core : Core) (s : Nat → Nat) (slot : FlowSlot) :
    Core × List (Nat × Nat) :=
  match slot with
  | .select dest cond a b =>
      let v := if s cond ≠ 0 then s a else s b
      (core, [(dest, v)])
  | .add_imm dest a imm =>
      (core, [(dest, mod32 (s a + imm))])
  | .vselect dest cond a b =>
      let writes := vecWrites dest (fun i => if s (cond + i) ≠ 0 then s (a + i) else s (b + i))
      (core, writes)
  | .halt =>
      ({ core with state := .stopped }, [])
  | .pause =>
      (if enablePause then { core with state := .paused } else core, [])
  | .trace_write val =>
      ({ core with trace_buf := core.trace_buf ++ [s val] }, [])
  | .cond_jump cond addr =>
      if s cond ≠ 0 then ({ core with pc := addr }, []) else (core, [])
  | .cond_jump_rel cond offset =>
      if s cond ≠ 0 then ({ core with pc := core.pc + offset }, []) else (core, [])
  | .jump addr =>
      ({ core with pc := addr }, [])
  | .jump_indirect addr =>
      ({ core with pc := Int.ofNat (s addr) }, [])
  | .coreid dest =>
      (core, [(dest, core.id)])

def execDebugSlot (s : Nat → Nat) (valueTrace : Nat → Nat) (slot : DebugSlot) : Bool :=
  match slot with
  | .compare loc key =>
      s loc = valueTrace key
  | .vcompare loc keys =>
      (List.range VLEN).all (fun i =>
        match listGet? keys i with
        | some key => s (loc + i) = valueTrace key
        | none => False)

/-! ### Instruction execution -/

structure ExecResult where
  core : Core
  mem : Mem
  ok : Bool
  debug_ok : Bool
  has_non_debug : Bool

noncomputable def execInstruction (enablePause : Bool) (enableDebug : Bool) (valueTrace : Nat → Nat) (mem : Mem)
    (core : Core) (instr : Instruction) : ExecResult :=
  let s0 := core.scratch
  let has_non_debug := instrHasNonDebug instr
  if !decide (instrWellFormed instr) then
    { core := core, mem := mem, ok := false, debug_ok := false, has_non_debug := has_non_debug }
  else
    -- debug checks
    let dbg_ok :=
      if enableDebug then
        instr.debug.all (fun slot => execDebugSlot s0 valueTrace slot)
      else
        true
    if !dbg_ok then
      { core := core, mem := mem, ok := false, debug_ok := dbg_ok, has_non_debug := has_non_debug }
    else
      -- VALU then ALU (match Python insertion order in generator/schedule_static.py)
      match execValuSlots s0 instr.valu with
      | none =>
          { core := core, mem := mem, ok := false, debug_ok := dbg_ok, has_non_debug := has_non_debug }
      | some valu_writes =>
          match execAluSlots s0 instr.alu with
          | none =>
              { core := core, mem := mem, ok := false, debug_ok := dbg_ok, has_non_debug := has_non_debug }
          | some alu_writes =>
              let load_writes? :=
                instr.load.foldl
                  (fun acc slot =>
                    match acc, execLoadSlot s0 mem slot with
                    | some ws, some ws' => some (ws ++ ws')
                    | _, _ => none)
                  (some [])
              match load_writes? with
              | none =>
                  { core := core, mem := mem, ok := false, debug_ok := dbg_ok,
                    has_non_debug := has_non_debug }
              | some load_writes =>
                  let store_writes := instr.store.flatMap (execStoreSlot s0)
                  match memWriteMany mem store_writes with
                  | none =>
                      { core := core, mem := mem, ok := false, debug_ok := dbg_ok,
                        has_non_debug := has_non_debug }
                  | some mem' =>
                      -- flow (sequential)
                      let (core', flow_writes) :=
                        instr.flow.foldl
                          (fun acc slot =>
                            let (c, ws) := acc
                            let (c', ws') := execFlowSlot enablePause c s0 slot
                            (c', ws ++ ws'))
                          (core, [])
                      let scratch' := writeMany s0 (valu_writes ++ alu_writes ++ flow_writes ++ load_writes)
                      let core'' := { core' with scratch := scratch' }
                      { core := core'', mem := mem', ok := true, debug_ok := dbg_ok,
                        has_non_debug := has_non_debug }

/-! ### Machine-level stepping -/

structure Machine where
  cores : List Core
  mem : Mem
  program : List Instruction
  cycle : Nat
  enable_pause : Bool := true
  enable_debug : Bool := true
  value_trace : Nat → Nat := fun _ => 0
  aborted : Bool := false

def fetch (prog : List Instruction) (pc : Int) : Option Instruction :=
  if 0 ≤ pc then
    listGet? prog (Int.toNat pc)
  else
    none

noncomputable def stepCore (m : Machine) (core : Core) : Core × Mem × Bool × Bool :=
  match core.state with
  | .running =>
      match fetch m.program core.pc with
      | none =>
          ({ core with state := .stopped }, m.mem, false, true)
      | some instr =>
          let core1 := { core with pc := core.pc + 1 }
          let res :=
            execInstruction m.enable_pause m.enable_debug m.value_trace m.mem core1 instr
          let core2 := if res.ok then res.core else { core1 with state := .stopped }
          (core2, res.mem, res.has_non_debug, res.ok)
  | _ =>
      (core, m.mem, false, true)

noncomputable def stepMachine (m : Machine) : Machine :=
  if m.aborted then
    m
  else
    let (cores', mem', anyExec, okAll) :=
      m.cores.foldl
        (fun acc core =>
          let (cs, mem0, flag, ok) := acc
          let (core', mem1, did, ok') := stepCore { m with mem := mem0 } core
          (cs ++ [core'], mem1, flag || did, ok && ok'))
        ([], m.mem, false, true)
    if !okAll then
      let cores'' := cores'.map (fun c => { c with state := .stopped })
      { m with cores := cores'', mem := mem', aborted := true }
    else
      let cycle' := if anyExec then m.cycle + 1 else m.cycle
      { m with cores := cores', mem := mem', cycle := cycle' }

end ProofMachine
