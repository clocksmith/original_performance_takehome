import proofs.common.Machine

namespace SimpTest

open ProofMachine

variable (mem : ProofMachine.Mem) (core : ProofMachine.Core) (instr : ProofMachine.Instruction)

def loadWrites? (mem : ProofMachine.Mem) (core : ProofMachine.Core) (instr : ProofMachine.Instruction) :
    Option (List (Nat × Nat)) :=
  List.foldl
    (fun acc slot =>
      match acc, ProofMachine.execLoadSlot core.scratch mem slot with
      | some ws, some ws' => some (ws ++ ws')
      | _, _ => none)
    (some []) instr.load

example (h : loadWrites? mem core instr = none) :
    (match loadWrites? mem core instr with
      | none => 0
      | some _ => 1) = 0 := by
  have h' :
      List.foldl
          (fun acc slot =>
            match acc, execLoadSlot core.scratch mem slot with
            | some ws, some ws' => some (ws ++ ws')
            | _, _ => none)
          (some []) instr.load =
        none := by
    simpa [loadWrites?] using h
  simp [loadWrites?, h']

example (h : loadWrites? mem core instr = some [(0, 0)]) :
    (match loadWrites? mem core instr with
      | none => 0
      | some ws => ws.length) = 1 := by
  have h' :
      List.foldl
          (fun acc slot =>
            match acc, execLoadSlot core.scratch mem slot with
            | some ws, some ws' => some (ws ++ ws')
            | _, _ => none)
          (some []) instr.load =
        some [(0, 0)] := by
    simpa [loadWrites?] using h
  simp [loadWrites?, h']

end SimpTest

namespace SimpTestLet

open ProofMachine

variable (mem : ProofMachine.Mem) (core : ProofMachine.Core) (instr : ProofMachine.Instruction)

def foo (mem : ProofMachine.Mem) (core : ProofMachine.Core) (instr : ProofMachine.Instruction) : Nat :=
  let s0 := core.scratch
  match
      List.foldl
        (fun acc slot =>
          match acc, execLoadSlot s0 mem slot with
          | some ws, some ws' => some (ws ++ ws')
          | _, _ => none)
        (some []) instr.load with
    | none => 0
    | some _ => 1

-- This is the "likely mismatch" situation: the goal is in terms of `s0` but the hypothesis is in
-- terms of `core.scratch`.
example
    (h :
      List.foldl
          (fun acc slot =>
            match acc, execLoadSlot core.scratch mem slot with
            | some ws, some ws' => some (ws ++ ws')
            | _, _ => none)
          (some []) instr.load =
        none) :
    foo mem core instr = 0 := by
  -- If `simp` doesn't zeta-reduce `s0` here, rewriting by `h` won't fire.
  simp (config := { zeta := false }) [foo]
  -- Goal is now in terms of the `let s0 := core.scratch`.
  -- Rewriting with `h` should fail (syntactic mismatch), but we can fix by zeta-reducing:
  ·
    -- Demonstrate the fix:
    simp (config := { zeta := true }) [foo, h]

end SimpTestLet

namespace SimpTestAlpha

open ProofMachine

variable (mem : Mem) (core : Core) (instr : Instruction)

def eUnderscore : Option (List (Nat × Nat)) :=
  List.foldl
    (fun acc slot =>
      match acc, execLoadSlot core.scratch mem slot with
      | some ws, some ws' => some (ws ++ ws')
      | _, _ => none)
    (some []) instr.load

def eNamed : Option (List (Nat × Nat)) :=
  List.foldl
    (fun acc slot =>
      match acc, execLoadSlot core.scratch mem slot with
      | some ws, some ws' => some (ws ++ ws')
      | x, x_1 => none)
    (some []) instr.load

example (h : eUnderscore mem core instr = none) :
    (match eNamed mem core instr with
      | none => 0
      | some _ => 1) = 0 := by
  -- If simp matching is syntactic (not defeq), it might not use `h` after unfolding `eNamed`.
  have h' :
      List.foldl
          (fun acc slot =>
            match acc, execLoadSlot core.scratch mem slot with
            | some ws, some ws' => some (ws ++ ws')
            | _, _ => none)
          (some []) instr.load =
        none := by
    simpa [eUnderscore] using h
  simp [eNamed, h']

end SimpTestAlpha
