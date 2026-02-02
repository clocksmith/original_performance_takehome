import Mathlib
import proofs.baseline_program.BlockSymbolic
import proofs.common.Machine

open ProofISA
open ProofMachine
open ProofGlobalLowerBound

/-! ## Block execution helpers

This file provides small-step lemmas for single-slot instructions and a
list-execution helper. These are the building blocks for the full
blockTemplate correctness proof.
-/

def coreOf (s : Nat → Nat) : Core :=
  { id := 0, scratch := s, trace_buf := [], pc := 0, state := .running }

def execInstrs : List Instruction → Memory → Core → Core × Memory
  | [], mem, core => (core, mem)
  | instr :: rest, mem, core =>
      let res := execInstruction false false (fun _ => 0) mem core instr
      if res.ok then
        execInstrs rest res.mem res.core
      else
        (res.core, res.mem)

lemma memWrite_eq_memUpdate (mem : Memory) (addr val : Nat) (h : addr < mem.size) :
    memWrite mem addr val = some (memUpdate mem addr val) := by
  simp [memWrite, memUpdate, memAt, h]

lemma execInstruction_instrAlu
    (mem : Memory) (core : Core) (op : AluOp) (dest a1 a2 : Nat)
    (hbound : dest < SCRATCH_SIZE ∧ a1 < SCRATCH_SIZE ∧ a2 < SCRATCH_SIZE)
    (hdiv : aluDivZero op (core.scratch a2) = false) :
    execInstruction false false (fun _ => 0) mem core (instrAlu op dest a1 a2) =
      { core := { core with scratch :=
          write core.scratch dest (aluEval op (core.scratch a1) (core.scratch a2)) },
        mem := mem, ok := true, debug_ok := true, has_non_debug := true } := by
  -- unfold and simplify instruction execution
  simp [execInstruction, instrAlu, instrHasNonDebug, instrWellFormed, instrScratchBounded,
        aluSlotBounded, hbound, hdiv, execAluSlots, execAluSlot, writeMany, write] at *

lemma execInstruction_instrLoad
    (mem : Memory) (core : Core) (dest addr : Nat)
    (hbound : dest < SCRATCH_SIZE ∧ addr < SCRATCH_SIZE)
    (haddr : core.scratch addr < mem.size) :
    execInstruction false false (fun _ => 0) mem core (instrLoad (LoadSlot.load dest addr)) =
      { core := { core with scratch := write core.scratch dest (memAt mem (core.scratch addr)) },
        mem := mem, ok := true, debug_ok := true, has_non_debug := true } := by
  have hread : memRead mem (core.scratch addr) = some (memAt mem (core.scratch addr)) := by
    simp [memRead, haddr, memAt]
  simp [execInstruction, instrLoad, instrHasNonDebug, instrWellFormed, instrScratchBounded,
        loadSlotBounded, hbound, execLoadSlot, hread, writeMany, write, memAt] at *

lemma execInstruction_instrStore
    (mem : Memory) (core : Core) (addr src : Nat)
    (hbound : addr < SCRATCH_SIZE ∧ src < SCRATCH_SIZE)
    (haddr : core.scratch addr < mem.size) :
    execInstruction false false (fun _ => 0) mem core (instrStore (StoreSlot.store addr src)) =
      { core := core,
        mem := memUpdate mem (core.scratch addr) (core.scratch src),
        ok := true, debug_ok := true, has_non_debug := true } := by
  have hwrite :
      memWriteMany mem [(core.scratch addr, core.scratch src)] =
        some (memUpdate mem (core.scratch addr) (core.scratch src)) := by
    simp [memWriteMany, memWrite_eq_memUpdate, haddr]
  simp [execInstruction, instrStore, instrHasNonDebug, instrWellFormed, instrScratchBounded,
        storeSlotBounded, hbound, execStoreSlot, hwrite, writeMany, write] at *

lemma execInstruction_instrSelect
    (mem : Memory) (core : Core) (dest cond a b : Nat)
    (hbound : dest < SCRATCH_SIZE ∧ cond < SCRATCH_SIZE ∧ a < SCRATCH_SIZE ∧ b < SCRATCH_SIZE) :
    execInstruction false false (fun _ => 0) mem core (instrFlow (FlowSlot.select dest cond a b)) =
      { core := { core with scratch :=
          write core.scratch dest (if core.scratch cond = 0 then core.scratch b else core.scratch a) },
        mem := mem, ok := true, debug_ok := true, has_non_debug := true } := by
  simp [execInstruction, instrFlow, instrHasNonDebug, instrWellFormed, instrScratchBounded,
        flowSlotBounded, hbound, execFlowSlot, writeMany, write] at *

lemma execInstrs_single_alu_add
    (mem : Memory) (s : Nat → Nat) (c : Nat) (hc : c < SCRATCH_SIZE) :
    execInstrs [instrAlu AluOp.add 16 8 c] mem (coreOf s) =
      ({ coreOf s with scratch := write s 16 (aluEval AluOp.add (s 8) (s c)) }, mem) := by
  have hbound : 16 < SCRATCH_SIZE ∧ 8 < SCRATCH_SIZE ∧ c < SCRATCH_SIZE := by
    exact And.intro (by decide) (And.intro (by decide) hc)
  have hdiv : aluDivZero AluOp.add (s c) = false := by
    simp [aluDivZero]
  have hstep := execInstruction_instrAlu mem (coreOf s) AluOp.add 16 8 c hbound hdiv
  simp [execInstrs, hstep, coreOf]
lemma execInstrs_blockTemplate_eq_blockSym
    (mem : Memory) (s : Nat → Nat) (c : Nat)
    (hc : c < SCRATCH_SIZE)
    (hidx : aluEval AluOp.add (s 8) (s c) < mem.size)
    (hval : aluEval AluOp.add (s 9) (s c) < mem.size)
    (hnode : aluEval AluOp.add (s 7) (memAt mem (aluEval AluOp.add (s 8) (s c))) < mem.size)
    (hmod : s 12 ≠ 0) :
    execInstrs (blockTemplate c) mem (coreOf s) =
      ({ (coreOf s) with scratch := (blockSym s mem c).1 }, (blockSym s mem c).2) := by
  let s0 := s
  let mem0 := mem
  let s1 := write s0 16 (aluEval AluOp.add (s0 8) (s0 c))
  let s2 := write s1 13 (memAt mem0 (s1 16))
  let s3 := write s2 16 (aluEval AluOp.add (s2 9) (s2 c))
  let s4 := write s3 14 (memAt mem0 (s3 16))
  let s5 := write s4 16 (aluEval AluOp.add (s4 7) (s2 13))
  let s6 := write s5 15 (memAt mem0 (s5 16))
  let s7 := write s6 14 (aluEval AluOp.xor (s4 14) (s6 15))
  let s8 := write s7 0 (aluEval AluOp.add (s7 14) (s7 17))
  let s9 := write s8 1 (aluEval AluOp.shl (s7 14) (s8 18))
  let s10 := write s9 14 (aluEval AluOp.add (s8 0) (s9 1))
  let s11 := write s10 0 (aluEval AluOp.xor (s10 14) (s10 19))
  let s12 := write s11 1 (aluEval AluOp.shr (s10 14) (s11 20))
  let s13 := write s12 14 (aluEval AluOp.xor (s11 0) (s12 1))
  let s14 := write s13 0 (aluEval AluOp.add (s13 14) (s13 21))
  let s15 := write s14 1 (aluEval AluOp.shl (s13 14) (s14 22))
  let s16 := write s15 14 (aluEval AluOp.add (s14 0) (s15 1))
  let s17 := write s16 0 (aluEval AluOp.add (s16 14) (s16 23))
  let s18 := write s17 1 (aluEval AluOp.shl (s16 14) (s17 24))
  let s19 := write s18 14 (aluEval AluOp.xor (s17 0) (s18 1))
  let s20 := write s19 0 (aluEval AluOp.add (s19 14) (s19 25))
  let s21 := write s20 1 (aluEval AluOp.shl (s19 14) (s20 26))
  let s22 := write s21 14 (aluEval AluOp.add (s20 0) (s21 1))
  let s23 := write s22 0 (aluEval AluOp.xor (s22 14) (s22 27))
  let s24 := write s23 1 (aluEval AluOp.shr (s22 14) (s23 28))
  let s25 := write s24 14 (aluEval AluOp.xor (s23 0) (s24 1))
  let s26 := write s25 0 (aluEval AluOp.mod (s25 14) (s25 12))
  let s27 := write s26 0 (aluEval AluOp.eq (s26 0) (s26 10))
  let s28 := write s27 2 (if s27 0 = 0 then s27 12 else s27 11)
  let s29 := write s28 13 (aluEval AluOp.mul (s2 13) (s28 12))
  let s30 := write s29 13 (aluEval AluOp.add (s29 13) (s28 2))
  let s31 := write s30 0 (aluEval AluOp.lt (s30 13) (s30 4))
  let s32 := write s31 13 (if s31 0 = 0 then s31 10 else s30 13)
  let s33 := write s32 16 (aluEval AluOp.add (s32 8) (s32 c))
  let mem1 := memUpdate mem0 (s33 16) (s32 13)
  let s34 := write s33 16 (aluEval AluOp.add (s33 9) (s33 c))
  let mem2 := memUpdate mem1 (s34 16) (s25 14)
  have hbound1 : 16 < SCRATCH_SIZE ∧ 8 < SCRATCH_SIZE ∧ c < SCRATCH_SIZE := by exact And.intro (by decide) (And.intro (by decide) hc)
  have hdiv1 : aluDivZero AluOp.add (s0 c) = false := by simp [aluDivZero]
  have hstep1 :
      execInstruction false false (fun _ => 0) mem0 { (coreOf s) with scratch := s0 }
        (instrAlu AluOp.add 16 8 c) =
        { core := { (coreOf s) with scratch := write s0 16 (aluEval AluOp.add (s0 8) (s0 c)) },
          mem := mem0, ok := true, debug_ok := true, has_non_debug := true } := by
    simpa [coreOf] using (execInstruction_instrAlu mem0 { (coreOf s) with scratch := s0 } AluOp.add 16 8 c hbound1 hdiv1)
  have hbound2 : 13 < SCRATCH_SIZE ∧ 16 < SCRATCH_SIZE := by decide
  have haddr2 : s1 16 < mem.size := by simpa [s1, write] using hidx
  have hstep2 :
      execInstruction false false (fun _ => 0) mem0 { (coreOf s) with scratch := s1 }
        (instrLoad (LoadSlot.load 13 16)) =
        { core := { (coreOf s) with scratch := write s1 13 (memAt mem0 (s1 16)) },
          mem := mem0, ok := true, debug_ok := true, has_non_debug := true } := by
    simpa [coreOf] using (execInstruction_instrLoad mem0 { (coreOf s) with scratch := s1 } 13 16 hbound2 haddr2)
  have hbound3 : 16 < SCRATCH_SIZE ∧ 9 < SCRATCH_SIZE ∧ c < SCRATCH_SIZE := by exact And.intro (by decide) (And.intro (by decide) hc)
  have hdiv3 : aluDivZero AluOp.add (s2 c) = false := by simp [aluDivZero]
  have hstep3 :
      execInstruction false false (fun _ => 0) mem0 { (coreOf s) with scratch := s2 }
        (instrAlu AluOp.add 16 9 c) =
        { core := { (coreOf s) with scratch := write s2 16 (aluEval AluOp.add (s2 9) (s2 c)) },
          mem := mem0, ok := true, debug_ok := true, has_non_debug := true } := by
    simpa [coreOf] using (execInstruction_instrAlu mem0 { (coreOf s) with scratch := s2 } AluOp.add 16 9 c hbound3 hdiv3)
  have hbound4 : 14 < SCRATCH_SIZE ∧ 16 < SCRATCH_SIZE := by decide
  have haddr4 : s3 16 < mem.size := by simpa [s3, write] using hval
  have hstep4 :
      execInstruction false false (fun _ => 0) mem0 { (coreOf s) with scratch := s3 }
        (instrLoad (LoadSlot.load 14 16)) =
        { core := { (coreOf s) with scratch := write s3 14 (memAt mem0 (s3 16)) },
          mem := mem0, ok := true, debug_ok := true, has_non_debug := true } := by
    simpa [coreOf] using (execInstruction_instrLoad mem0 { (coreOf s) with scratch := s3 } 14 16 hbound4 haddr4)
  have hbound5 : 16 < SCRATCH_SIZE ∧ 7 < SCRATCH_SIZE ∧ 13 < SCRATCH_SIZE := by decide
  have hdiv5 : aluDivZero AluOp.add (s4 13) = false := by simp [aluDivZero]
  have hstep5 :
      execInstruction false false (fun _ => 0) mem0 { (coreOf s) with scratch := s4 }
        (instrAlu AluOp.add 16 7 13) =
        { core := { (coreOf s) with scratch := write s4 16 (aluEval AluOp.add (s4 7) (s4 13)) },
          mem := mem0, ok := true, debug_ok := true, has_non_debug := true } := by
    simpa [coreOf] using (execInstruction_instrAlu mem0 { (coreOf s) with scratch := s4 } AluOp.add 16 7 13 hbound5 hdiv5)
  have hbound6 : 15 < SCRATCH_SIZE ∧ 16 < SCRATCH_SIZE := by decide
  have haddr6 : s5 16 < mem.size := by
    simpa [s5, s4, s3, s2, s1, write] using hnode
  have hstep6 :
      execInstruction false false (fun _ => 0) mem0 { (coreOf s) with scratch := s5 }
        (instrLoad (LoadSlot.load 15 16)) =
        { core := { (coreOf s) with scratch := write s5 15 (memAt mem0 (s5 16)) },
          mem := mem0, ok := true, debug_ok := true, has_non_debug := true } := by
    simpa [coreOf] using (execInstruction_instrLoad mem0 { (coreOf s) with scratch := s5 } 15 16 hbound6 haddr6)
  have hbound7 : 14 < SCRATCH_SIZE ∧ 14 < SCRATCH_SIZE ∧ 15 < SCRATCH_SIZE := by decide
  have hdiv7 : aluDivZero AluOp.xor (s6 15) = false := by simp [aluDivZero]
  have hstep7 :
      execInstruction false false (fun _ => 0) mem0 { (coreOf s) with scratch := s6 }
        (instrAlu AluOp.xor 14 14 15) =
        { core := { (coreOf s) with scratch := write s6 14 (aluEval AluOp.xor (s6 14) (s6 15)) },
          mem := mem0, ok := true, debug_ok := true, has_non_debug := true } := by
    simpa [coreOf] using (execInstruction_instrAlu mem0 { (coreOf s) with scratch := s6 } AluOp.xor 14 14 15 hbound7 hdiv7)
  have hbound8 : 0 < SCRATCH_SIZE ∧ 14 < SCRATCH_SIZE ∧ 17 < SCRATCH_SIZE := by decide
  have hdiv8 : aluDivZero AluOp.add (s7 17) = false := by simp [aluDivZero]
  have hstep8 :
      execInstruction false false (fun _ => 0) mem0 { (coreOf s) with scratch := s7 }
        (instrAlu AluOp.add 0 14 17) =
        { core := { (coreOf s) with scratch := write s7 0 (aluEval AluOp.add (s7 14) (s7 17)) },
          mem := mem0, ok := true, debug_ok := true, has_non_debug := true } := by
    simpa [coreOf] using (execInstruction_instrAlu mem0 { (coreOf s) with scratch := s7 } AluOp.add 0 14 17 hbound8 hdiv8)
  have hbound9 : 1 < SCRATCH_SIZE ∧ 14 < SCRATCH_SIZE ∧ 18 < SCRATCH_SIZE := by decide
  have hdiv9 : aluDivZero AluOp.shl (s8 18) = false := by simp [aluDivZero]
  have hstep9 :
      execInstruction false false (fun _ => 0) mem0 { (coreOf s) with scratch := s8 }
        (instrAlu AluOp.shl 1 14 18) =
        { core := { (coreOf s) with scratch := write s8 1 (aluEval AluOp.shl (s8 14) (s8 18)) },
          mem := mem0, ok := true, debug_ok := true, has_non_debug := true } := by
    simpa [coreOf] using (execInstruction_instrAlu mem0 { (coreOf s) with scratch := s8 } AluOp.shl 1 14 18 hbound9 hdiv9)
  have hbound10 : 14 < SCRATCH_SIZE ∧ 0 < SCRATCH_SIZE ∧ 1 < SCRATCH_SIZE := by decide
  have hdiv10 : aluDivZero AluOp.add (s9 1) = false := by simp [aluDivZero]
  have hstep10 :
      execInstruction false false (fun _ => 0) mem0 { (coreOf s) with scratch := s9 }
        (instrAlu AluOp.add 14 0 1) =
        { core := { (coreOf s) with scratch := write s9 14 (aluEval AluOp.add (s9 0) (s9 1)) },
          mem := mem0, ok := true, debug_ok := true, has_non_debug := true } := by
    simpa [coreOf] using (execInstruction_instrAlu mem0 { (coreOf s) with scratch := s9 } AluOp.add 14 0 1 hbound10 hdiv10)
  have hbound11 : 0 < SCRATCH_SIZE ∧ 14 < SCRATCH_SIZE ∧ 19 < SCRATCH_SIZE := by decide
  have hdiv11 : aluDivZero AluOp.xor (s10 19) = false := by simp [aluDivZero]
  have hstep11 :
      execInstruction false false (fun _ => 0) mem0 { (coreOf s) with scratch := s10 }
        (instrAlu AluOp.xor 0 14 19) =
        { core := { (coreOf s) with scratch := write s10 0 (aluEval AluOp.xor (s10 14) (s10 19)) },
          mem := mem0, ok := true, debug_ok := true, has_non_debug := true } := by
    simpa [coreOf] using (execInstruction_instrAlu mem0 { (coreOf s) with scratch := s10 } AluOp.xor 0 14 19 hbound11 hdiv11)
  have hbound12 : 1 < SCRATCH_SIZE ∧ 14 < SCRATCH_SIZE ∧ 20 < SCRATCH_SIZE := by decide
  have hdiv12 : aluDivZero AluOp.shr (s11 20) = false := by simp [aluDivZero]
  have hstep12 :
      execInstruction false false (fun _ => 0) mem0 { (coreOf s) with scratch := s11 }
        (instrAlu AluOp.shr 1 14 20) =
        { core := { (coreOf s) with scratch := write s11 1 (aluEval AluOp.shr (s11 14) (s11 20)) },
          mem := mem0, ok := true, debug_ok := true, has_non_debug := true } := by
    simpa [coreOf] using (execInstruction_instrAlu mem0 { (coreOf s) with scratch := s11 } AluOp.shr 1 14 20 hbound12 hdiv12)
  have hbound13 : 14 < SCRATCH_SIZE ∧ 0 < SCRATCH_SIZE ∧ 1 < SCRATCH_SIZE := by decide
  have hdiv13 : aluDivZero AluOp.xor (s12 1) = false := by simp [aluDivZero]
  have hstep13 :
      execInstruction false false (fun _ => 0) mem0 { (coreOf s) with scratch := s12 }
        (instrAlu AluOp.xor 14 0 1) =
        { core := { (coreOf s) with scratch := write s12 14 (aluEval AluOp.xor (s12 0) (s12 1)) },
          mem := mem0, ok := true, debug_ok := true, has_non_debug := true } := by
    simpa [coreOf] using (execInstruction_instrAlu mem0 { (coreOf s) with scratch := s12 } AluOp.xor 14 0 1 hbound13 hdiv13)
  have hbound14 : 0 < SCRATCH_SIZE ∧ 14 < SCRATCH_SIZE ∧ 21 < SCRATCH_SIZE := by decide
  have hdiv14 : aluDivZero AluOp.add (s13 21) = false := by simp [aluDivZero]
  have hstep14 :
      execInstruction false false (fun _ => 0) mem0 { (coreOf s) with scratch := s13 }
        (instrAlu AluOp.add 0 14 21) =
        { core := { (coreOf s) with scratch := write s13 0 (aluEval AluOp.add (s13 14) (s13 21)) },
          mem := mem0, ok := true, debug_ok := true, has_non_debug := true } := by
    simpa [coreOf] using (execInstruction_instrAlu mem0 { (coreOf s) with scratch := s13 } AluOp.add 0 14 21 hbound14 hdiv14)
  have hbound15 : 1 < SCRATCH_SIZE ∧ 14 < SCRATCH_SIZE ∧ 22 < SCRATCH_SIZE := by decide
  have hdiv15 : aluDivZero AluOp.shl (s14 22) = false := by simp [aluDivZero]
  have hstep15 :
      execInstruction false false (fun _ => 0) mem0 { (coreOf s) with scratch := s14 }
        (instrAlu AluOp.shl 1 14 22) =
        { core := { (coreOf s) with scratch := write s14 1 (aluEval AluOp.shl (s14 14) (s14 22)) },
          mem := mem0, ok := true, debug_ok := true, has_non_debug := true } := by
    simpa [coreOf] using (execInstruction_instrAlu mem0 { (coreOf s) with scratch := s14 } AluOp.shl 1 14 22 hbound15 hdiv15)
  have hbound16 : 14 < SCRATCH_SIZE ∧ 0 < SCRATCH_SIZE ∧ 1 < SCRATCH_SIZE := by decide
  have hdiv16 : aluDivZero AluOp.add (s15 1) = false := by simp [aluDivZero]
  have hstep16 :
      execInstruction false false (fun _ => 0) mem0 { (coreOf s) with scratch := s15 }
        (instrAlu AluOp.add 14 0 1) =
        { core := { (coreOf s) with scratch := write s15 14 (aluEval AluOp.add (s15 0) (s15 1)) },
          mem := mem0, ok := true, debug_ok := true, has_non_debug := true } := by
    simpa [coreOf] using (execInstruction_instrAlu mem0 { (coreOf s) with scratch := s15 } AluOp.add 14 0 1 hbound16 hdiv16)
  have hbound17 : 0 < SCRATCH_SIZE ∧ 14 < SCRATCH_SIZE ∧ 23 < SCRATCH_SIZE := by decide
  have hdiv17 : aluDivZero AluOp.add (s16 23) = false := by simp [aluDivZero]
  have hstep17 :
      execInstruction false false (fun _ => 0) mem0 { (coreOf s) with scratch := s16 }
        (instrAlu AluOp.add 0 14 23) =
        { core := { (coreOf s) with scratch := write s16 0 (aluEval AluOp.add (s16 14) (s16 23)) },
          mem := mem0, ok := true, debug_ok := true, has_non_debug := true } := by
    simpa [coreOf] using (execInstruction_instrAlu mem0 { (coreOf s) with scratch := s16 } AluOp.add 0 14 23 hbound17 hdiv17)
  have hbound18 : 1 < SCRATCH_SIZE ∧ 14 < SCRATCH_SIZE ∧ 24 < SCRATCH_SIZE := by decide
  have hdiv18 : aluDivZero AluOp.shl (s17 24) = false := by simp [aluDivZero]
  have hstep18 :
      execInstruction false false (fun _ => 0) mem0 { (coreOf s) with scratch := s17 }
        (instrAlu AluOp.shl 1 14 24) =
        { core := { (coreOf s) with scratch := write s17 1 (aluEval AluOp.shl (s17 14) (s17 24)) },
          mem := mem0, ok := true, debug_ok := true, has_non_debug := true } := by
    simpa [coreOf] using (execInstruction_instrAlu mem0 { (coreOf s) with scratch := s17 } AluOp.shl 1 14 24 hbound18 hdiv18)
  have hbound19 : 14 < SCRATCH_SIZE ∧ 0 < SCRATCH_SIZE ∧ 1 < SCRATCH_SIZE := by decide
  have hdiv19 : aluDivZero AluOp.xor (s18 1) = false := by simp [aluDivZero]
  have hstep19 :
      execInstruction false false (fun _ => 0) mem0 { (coreOf s) with scratch := s18 }
        (instrAlu AluOp.xor 14 0 1) =
        { core := { (coreOf s) with scratch := write s18 14 (aluEval AluOp.xor (s18 0) (s18 1)) },
          mem := mem0, ok := true, debug_ok := true, has_non_debug := true } := by
    simpa [coreOf] using (execInstruction_instrAlu mem0 { (coreOf s) with scratch := s18 } AluOp.xor 14 0 1 hbound19 hdiv19)
  have hbound20 : 0 < SCRATCH_SIZE ∧ 14 < SCRATCH_SIZE ∧ 25 < SCRATCH_SIZE := by decide
  have hdiv20 : aluDivZero AluOp.add (s19 25) = false := by simp [aluDivZero]
  have hstep20 :
      execInstruction false false (fun _ => 0) mem0 { (coreOf s) with scratch := s19 }
        (instrAlu AluOp.add 0 14 25) =
        { core := { (coreOf s) with scratch := write s19 0 (aluEval AluOp.add (s19 14) (s19 25)) },
          mem := mem0, ok := true, debug_ok := true, has_non_debug := true } := by
    simpa [coreOf] using (execInstruction_instrAlu mem0 { (coreOf s) with scratch := s19 } AluOp.add 0 14 25 hbound20 hdiv20)
  have hbound21 : 1 < SCRATCH_SIZE ∧ 14 < SCRATCH_SIZE ∧ 26 < SCRATCH_SIZE := by decide
  have hdiv21 : aluDivZero AluOp.shl (s20 26) = false := by simp [aluDivZero]
  have hstep21 :
      execInstruction false false (fun _ => 0) mem0 { (coreOf s) with scratch := s20 }
        (instrAlu AluOp.shl 1 14 26) =
        { core := { (coreOf s) with scratch := write s20 1 (aluEval AluOp.shl (s20 14) (s20 26)) },
          mem := mem0, ok := true, debug_ok := true, has_non_debug := true } := by
    simpa [coreOf] using (execInstruction_instrAlu mem0 { (coreOf s) with scratch := s20 } AluOp.shl 1 14 26 hbound21 hdiv21)
  have hbound22 : 14 < SCRATCH_SIZE ∧ 0 < SCRATCH_SIZE ∧ 1 < SCRATCH_SIZE := by decide
  have hdiv22 : aluDivZero AluOp.add (s21 1) = false := by simp [aluDivZero]
  have hstep22 :
      execInstruction false false (fun _ => 0) mem0 { (coreOf s) with scratch := s21 }
        (instrAlu AluOp.add 14 0 1) =
        { core := { (coreOf s) with scratch := write s21 14 (aluEval AluOp.add (s21 0) (s21 1)) },
          mem := mem0, ok := true, debug_ok := true, has_non_debug := true } := by
    simpa [coreOf] using (execInstruction_instrAlu mem0 { (coreOf s) with scratch := s21 } AluOp.add 14 0 1 hbound22 hdiv22)
  have hbound23 : 0 < SCRATCH_SIZE ∧ 14 < SCRATCH_SIZE ∧ 27 < SCRATCH_SIZE := by decide
  have hdiv23 : aluDivZero AluOp.xor (s22 27) = false := by simp [aluDivZero]
  have hstep23 :
      execInstruction false false (fun _ => 0) mem0 { (coreOf s) with scratch := s22 }
        (instrAlu AluOp.xor 0 14 27) =
        { core := { (coreOf s) with scratch := write s22 0 (aluEval AluOp.xor (s22 14) (s22 27)) },
          mem := mem0, ok := true, debug_ok := true, has_non_debug := true } := by
    simpa [coreOf] using (execInstruction_instrAlu mem0 { (coreOf s) with scratch := s22 } AluOp.xor 0 14 27 hbound23 hdiv23)
  have hbound24 : 1 < SCRATCH_SIZE ∧ 14 < SCRATCH_SIZE ∧ 28 < SCRATCH_SIZE := by decide
  have hdiv24 : aluDivZero AluOp.shr (s23 28) = false := by simp [aluDivZero]
  have hstep24 :
      execInstruction false false (fun _ => 0) mem0 { (coreOf s) with scratch := s23 }
        (instrAlu AluOp.shr 1 14 28) =
        { core := { (coreOf s) with scratch := write s23 1 (aluEval AluOp.shr (s23 14) (s23 28)) },
          mem := mem0, ok := true, debug_ok := true, has_non_debug := true } := by
    simpa [coreOf] using (execInstruction_instrAlu mem0 { (coreOf s) with scratch := s23 } AluOp.shr 1 14 28 hbound24 hdiv24)
  have hbound25 : 14 < SCRATCH_SIZE ∧ 0 < SCRATCH_SIZE ∧ 1 < SCRATCH_SIZE := by decide
  have hdiv25 : aluDivZero AluOp.xor (s24 1) = false := by simp [aluDivZero]
  have hstep25 :
      execInstruction false false (fun _ => 0) mem0 { (coreOf s) with scratch := s24 }
        (instrAlu AluOp.xor 14 0 1) =
        { core := { (coreOf s) with scratch := write s24 14 (aluEval AluOp.xor (s24 0) (s24 1)) },
          mem := mem0, ok := true, debug_ok := true, has_non_debug := true } := by
    simpa [coreOf] using (execInstruction_instrAlu mem0 { (coreOf s) with scratch := s24 } AluOp.xor 14 0 1 hbound25 hdiv25)
  have hbound26 : 0 < SCRATCH_SIZE ∧ 14 < SCRATCH_SIZE ∧ 12 < SCRATCH_SIZE := by decide
  have hdiv26 : aluDivZero AluOp.mod (s25 12) = false := by
    have hmod' : s25 12 ≠ 0 := by
      simp [s25, s24, s23, s22, s21, s20, s19, s18, s17, s16, s15, s14, s13, s12,
        s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, write, hmod]
    simp [aluDivZero, hmod']
  have hstep26 :
      execInstruction false false (fun _ => 0) mem0 { (coreOf s) with scratch := s25 }
        (instrAlu AluOp.mod 0 14 12) =
        { core := { (coreOf s) with scratch := write s25 0 (aluEval AluOp.mod (s25 14) (s25 12)) },
          mem := mem0, ok := true, debug_ok := true, has_non_debug := true } := by
    simpa [coreOf] using (execInstruction_instrAlu mem0 { (coreOf s) with scratch := s25 } AluOp.mod 0 14 12 hbound26 hdiv26)
  have hbound27 : 0 < SCRATCH_SIZE ∧ 0 < SCRATCH_SIZE ∧ 10 < SCRATCH_SIZE := by decide
  have hdiv27 : aluDivZero AluOp.eq (s26 10) = false := by simp [aluDivZero]
  have hstep27 :
      execInstruction false false (fun _ => 0) mem0 { (coreOf s) with scratch := s26 }
        (instrAlu AluOp.eq 0 0 10) =
        { core := { (coreOf s) with scratch := write s26 0 (aluEval AluOp.eq (s26 0) (s26 10)) },
          mem := mem0, ok := true, debug_ok := true, has_non_debug := true } := by
    simpa [coreOf] using (execInstruction_instrAlu mem0 { (coreOf s) with scratch := s26 } AluOp.eq 0 0 10 hbound27 hdiv27)
  have hbound28 : 2 < SCRATCH_SIZE ∧ 0 < SCRATCH_SIZE ∧ 11 < SCRATCH_SIZE ∧ 12 < SCRATCH_SIZE := by decide
  have hstep28 :
      execInstruction false false (fun _ => 0) mem0 { (coreOf s) with scratch := s27 }
        (instrFlow (FlowSlot.select 2 0 11 12)) =
        { core := { (coreOf s) with scratch := write s27 2 (if s27 0 = 0 then s27 12 else s27 11) },
          mem := mem0, ok := true, debug_ok := true, has_non_debug := true } := by
    simpa [coreOf] using (execInstruction_instrSelect mem0 { (coreOf s) with scratch := s27 } 2 0 11 12 hbound28)
  have hbound29 : 13 < SCRATCH_SIZE ∧ 13 < SCRATCH_SIZE ∧ 12 < SCRATCH_SIZE := by decide
  have hdiv29 : aluDivZero AluOp.mul (s28 12) = false := by simp [aluDivZero]
  have hstep29 :
      execInstruction false false (fun _ => 0) mem0 { (coreOf s) with scratch := s28 }
        (instrAlu AluOp.mul 13 13 12) =
        { core := { (coreOf s) with scratch := write s28 13 (aluEval AluOp.mul (s28 13) (s28 12)) },
          mem := mem0, ok := true, debug_ok := true, has_non_debug := true } := by
    simpa [coreOf] using (execInstruction_instrAlu mem0 { (coreOf s) with scratch := s28 } AluOp.mul 13 13 12 hbound29 hdiv29)
  have hbound30 : 13 < SCRATCH_SIZE ∧ 13 < SCRATCH_SIZE ∧ 2 < SCRATCH_SIZE := by decide
  have hdiv30 : aluDivZero AluOp.add (s29 2) = false := by simp [aluDivZero]
  have hstep30 :
      execInstruction false false (fun _ => 0) mem0 { (coreOf s) with scratch := s29 }
        (instrAlu AluOp.add 13 13 2) =
        { core := { (coreOf s) with scratch := write s29 13 (aluEval AluOp.add (s29 13) (s29 2)) },
          mem := mem0, ok := true, debug_ok := true, has_non_debug := true } := by
    simpa [coreOf] using (execInstruction_instrAlu mem0 { (coreOf s) with scratch := s29 } AluOp.add 13 13 2 hbound30 hdiv30)
  have hbound31 : 0 < SCRATCH_SIZE ∧ 13 < SCRATCH_SIZE ∧ 4 < SCRATCH_SIZE := by decide
  have hdiv31 : aluDivZero AluOp.lt (s30 4) = false := by simp [aluDivZero]
  have hstep31 :
      execInstruction false false (fun _ => 0) mem0 { (coreOf s) with scratch := s30 }
        (instrAlu AluOp.lt 0 13 4) =
        { core := { (coreOf s) with scratch := write s30 0 (aluEval AluOp.lt (s30 13) (s30 4)) },
          mem := mem0, ok := true, debug_ok := true, has_non_debug := true } := by
    simpa [coreOf] using (execInstruction_instrAlu mem0 { (coreOf s) with scratch := s30 } AluOp.lt 0 13 4 hbound31 hdiv31)
  have hbound32 : 13 < SCRATCH_SIZE ∧ 0 < SCRATCH_SIZE ∧ 13 < SCRATCH_SIZE ∧ 10 < SCRATCH_SIZE := by decide
  have hstep32 :
      execInstruction false false (fun _ => 0) mem0 { (coreOf s) with scratch := s31 }
        (instrFlow (FlowSlot.select 13 0 13 10)) =
        { core := { (coreOf s) with scratch := write s31 13 (if s31 0 = 0 then s31 10 else s31 13) },
          mem := mem0, ok := true, debug_ok := true, has_non_debug := true } := by
    simpa [coreOf] using (execInstruction_instrSelect mem0 { (coreOf s) with scratch := s31 } 13 0 13 10 hbound32)
  have hbound33 : 16 < SCRATCH_SIZE ∧ 8 < SCRATCH_SIZE ∧ c < SCRATCH_SIZE := by exact And.intro (by decide) (And.intro (by decide) hc)
  have hdiv33 : aluDivZero AluOp.add (s32 c) = false := by simp [aluDivZero]
  have hstep33 :
      execInstruction false false (fun _ => 0) mem0 { (coreOf s) with scratch := s32 }
        (instrAlu AluOp.add 16 8 c) =
        { core := { (coreOf s) with scratch := write s32 16 (aluEval AluOp.add (s32 8) (s32 c)) },
          mem := mem0, ok := true, debug_ok := true, has_non_debug := true } := by
    simpa [coreOf] using (execInstruction_instrAlu mem0 { (coreOf s) with scratch := s32 } AluOp.add 16 8 c hbound33 hdiv33)
  have hbound34 : 16 < SCRATCH_SIZE ∧ 13 < SCRATCH_SIZE := by decide
  have haddr34 : s33 16 < mem.size := by
    simpa [s33, s32, s31, s30, s29, s28, s27, s26, s25, s24, s23, s22, s21, s20,
      s19, s18, s17, s16, s15, s14, s13, s12, s11, s10, s9, s8, s7, s6, s5, s4,
      s3, s2, s1, write] using hidx
  have hstep34 :
      execInstruction false false (fun _ => 0) mem0 { (coreOf s) with scratch := s33 }
        (instrStore (StoreSlot.store 16 13)) =
        { core := { (coreOf s) with scratch := s33 },
          mem := memUpdate mem0 (s33 16) (s33 13), ok := true, debug_ok := true, has_non_debug := true } := by
    simpa [coreOf] using (execInstruction_instrStore mem0 { (coreOf s) with scratch := s33 } 16 13 hbound34 haddr34)
  have hbound35 : 16 < SCRATCH_SIZE ∧ 9 < SCRATCH_SIZE ∧ c < SCRATCH_SIZE := by exact And.intro (by decide) (And.intro (by decide) hc)
  have hdiv35 : aluDivZero AluOp.add (s33 c) = false := by simp [aluDivZero]
  have hstep35 :
      execInstruction false false (fun _ => 0) mem1 { (coreOf s) with scratch := s33 }
        (instrAlu AluOp.add 16 9 c) =
        { core := { (coreOf s) with scratch := write s33 16 (aluEval AluOp.add (s33 9) (s33 c)) },
          mem := mem1, ok := true, debug_ok := true, has_non_debug := true } := by
    simpa [coreOf] using (execInstruction_instrAlu mem1 { (coreOf s) with scratch := s33 } AluOp.add 16 9 c hbound35 hdiv35)
  have hbound36 : 16 < SCRATCH_SIZE ∧ 14 < SCRATCH_SIZE := by decide
  have haddr36 : s34 16 < mem.size := by
    simpa [s34, s33, s32, s31, s30, s29, s28, s27, s26, s25, s24, s23, s22, s21, s20,
      s19, s18, s17, s16, s15, s14, s13, s12, s11, s10, s9, s8, s7, s6, s5, s4,
      s3, s2, s1, write] using hval
  have hstep36 :
      execInstruction false false (fun _ => 0) mem1 { (coreOf s) with scratch := s34 }
        (instrStore (StoreSlot.store 16 14)) =
        { core := { (coreOf s) with scratch := s34 },
          mem := memUpdate mem1 (s34 16) (s34 14), ok := true, debug_ok := true, has_non_debug := true } := by
    simpa [coreOf] using (execInstruction_instrStore mem1 { (coreOf s) with scratch := s34 } 16 14 hbound36 haddr36)
  -- reduce the execInstrs chain
  simp [execInstrs, blockTemplate, coreOf, blockSym,
    hstep1, hstep2, hstep3, hstep4, hstep5, hstep6, hstep7, hstep8, hstep9, hstep10, hstep11, hstep12, hstep13, hstep14, hstep15, hstep16, hstep17, hstep18, hstep19, hstep20, hstep21, hstep22, hstep23, hstep24, hstep25, hstep26, hstep27, hstep28, hstep29, hstep30, hstep31, hstep32, hstep33, hstep34, hstep35, hstep36]
