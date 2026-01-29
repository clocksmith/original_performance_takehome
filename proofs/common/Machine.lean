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
  deriving Repr

abbrev Mem := Nat → Nat

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

def instrWellFormed (i : Instruction) : Prop :=
  i.alu.length ≤ ALU_CAP ∧
  i.valu.length ≤ VALU_CAP ∧
  i.load.length ≤ LOAD_CAP ∧
  i.store.length ≤ STORE_CAP ∧
  i.flow.length ≤ FLOW_CAP

def instrHasNonDebug (i : Instruction) : Bool :=
  (!i.alu.isEmpty) || (!i.valu.isEmpty) || (!i.load.isEmpty) || (!i.store.isEmpty) || (!i.flow.isEmpty)

/-! ### Write helpers -/

def write (m : Nat → Nat) (addr : Nat) (val : Nat) : Nat → Nat :=
  fun a => if a = addr then mod32 val else m a

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

def execLoadSlot (s : Nat → Nat) (m : Mem) (slot : LoadSlot) : List (Nat × Nat) :=
  match slot with
  | .load dest addr =>
      [(dest, m (s addr))]
  | .load_offset dest addr offset =>
      [(dest + offset, m (s (addr + offset)))]
  | .vload dest addr =>
      let base := s addr
      vecWrites dest (fun i => m (base + i))
  | .const dest val =>
      [(dest, mod32 val)]

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
        match keys.get? i with
        | some key => s (loc + i) = valueTrace key
        | none => False)

/-! ### Instruction execution -/

structure ExecResult where
  core : Core
  mem : Mem
  ok : Bool
  debug_ok : Bool
  has_non_debug : Bool

def execInstruction (enablePause : Bool) (enableDebug : Bool) (valueTrace : Nat → Nat) (mem : Mem)
    (core : Core) (instr : Instruction) : ExecResult :=
  let s0 := core.scratch
  let has_non_debug := instrHasNonDebug instr
  if !instrWellFormed instr then
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
              let load_writes := instr.load.bind (execLoadSlot s0 mem)
              let store_writes := instr.store.bind (execStoreSlot s0)
              -- flow (sequential)
              let (core', flow_writes) :=
                instr.flow.foldl
                  (fun acc slot =>
                    let (c, ws) := acc
                    let (c', ws') := execFlowSlot enablePause c s0 slot
                    (c', ws ++ ws'))
                  (core, [])
              let scratch' := writeMany s0 (valu_writes ++ alu_writes ++ flow_writes ++ load_writes)
              let mem' := writeMany mem store_writes
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
  if h : 0 ≤ pc then
    prog.get? (Int.toNat pc)
  else
    none

def stepCore (m : Machine) (core : Core) : Core × Mem × Bool × Bool :=
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

def stepMachine (m : Machine) : Machine :=
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
