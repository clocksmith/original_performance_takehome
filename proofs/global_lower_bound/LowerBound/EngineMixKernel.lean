import proofs.global_lower_bound.LowerBound.EngineMixLB
import proofs.global_lower_bound.LowerBound.CycleLB

namespace ProofGlobalLowerBound
open ProofCommon
open ProofMachine
open ProofISA

/-!
Kernel-facing composition lemmas for engine-mix lower bounds.

This file connects:
1) required work assumptions (currently: required LOAD ops), and
2) machine cycle accounting (`CycleLB`)
into
3) `engineLowerBound ... ≤ cycleCountMachine ...`.
-/

def requiredLoadOnly (loadOps : Nat) : EngineCounts :=
  { valu := 0, alu := 0, load := loadOps, flow := 0, store := 0 }

lemma engineLowerBound_requiredLoadOnly (loadOps : Nat) :
    engineLowerBound (requiredLoadOnly loadOps) = ceilDiv loadOps LOAD_CAP := by
  have hvalu0 : ceilDiv 0 VALU_CAP = 0 := by native_decide
  have halu0 : ceilDiv 0 ALU_CAP = 0 := by native_decide
  have hstore0 : ceilDiv 0 STORE_CAP = 0 := by native_decide
  simp [requiredLoadOnly, engineLowerBound, hvalu0, halu0, hstore0]

def requiredFlowOnly (flowOps : Nat) : EngineCounts :=
  { valu := 0, alu := 0, load := 0, flow := flowOps, store := 0 }

lemma engineLowerBound_requiredFlowOnly (flowOps : Nat) :
    engineLowerBound (requiredFlowOnly flowOps) = flowOps := by
  have hvalu0 : ceilDiv 0 VALU_CAP = 0 := by native_decide
  have halu0 : ceilDiv 0 ALU_CAP = 0 := by native_decide
  have hload0 : ceilDiv 0 LOAD_CAP = 0 := by native_decide
  have hstore0 : ceilDiv 0 STORE_CAP = 0 := by native_decide
  have hflow : max flowOps 0 = flowOps := by simp
  simp [requiredFlowOnly, engineLowerBound, hvalu0, halu0, hload0, hstore0, hflow]

lemma loadOpCountMachine_le_cycleCountMachine
    (p : Program) (mem : Memory)
    (hnoAbort : (runMachineFinalFuel p p.program.length mem).aborted = false) :
    loadOpCountMachine p mem ≤ LOAD_CAP * cycleCountMachine p mem := by
  have h :=
    loadOpCountMachineFuel_le_cycle (p := p) (fuel := p.program.length) (mem := mem) hnoAbort
  simpa [loadOpCountMachine, loadOpCountMachineFuel, readOpsMachine, readOpsMachineFuel,
    cycleCountMachine, cycleCountMachineFuel, runMachineTrace, runMachineTraceFuel] using h

theorem engine_load_lower_bound_of_requiredLoadOps
    (p : Program) (mem : Memory) (loadReq : Nat)
    (hnoAbort : (runMachineFinalFuel p p.program.length mem).aborted = false)
    (hreq : loadReq ≤ loadOpCountMachine p mem) :
    engineLowerBound (requiredLoadOnly loadReq) ≤ cycleCountMachine p mem := by
  have hcap : loadReq ≤ LOAD_CAP * cycleCountMachine p mem := by
    exact le_trans hreq (loadOpCountMachine_le_cycleCountMachine p mem hnoAbort)
  have hfit : FitsEngineBudget (requiredLoadOnly loadReq) (cycleCountMachine p mem) := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simp [requiredLoadOnly]
    · simp [requiredLoadOnly]
    · simpa [requiredLoadOnly] using hcap
    · simp [requiredLoadOnly]
    · simp [requiredLoadOnly]
  exact engineLowerBound_le_of_fits _ _ hfit

theorem engine_load_lower_bound_of_requiredLoadOps_straightLine_safeExec
    (p : Program) (hstraight : StraightLine p)
    (mem : Memory) (hsafe : SafeExec p mem) (loadReq : Nat)
    (hreq : loadReq ≤ loadOpCountMachine p mem) :
    engineLowerBound (requiredLoadOnly loadReq) ≤ cycleCountMachine p mem := by
  have hnoAbort :
      (runMachineFinalFuel p p.program.length mem).aborted = false :=
    runMachineFinalFuel_aborted_false_of_StraightLine_safeExec (p := p) (hstraight := hstraight) mem hsafe
  exact engine_load_lower_bound_of_requiredLoadOps p mem loadReq hnoAbort hreq

theorem engine_flow_lower_bound_of_requiredFlowOps
    (p : Program) (mem : Memory) (flowReq : Nat)
    (hreq : flowReq ≤ cycleCountMachine p mem) :
    engineLowerBound (requiredFlowOnly flowReq) ≤ cycleCountMachine p mem := by
  have hfit : FitsEngineBudget (requiredFlowOnly flowReq) (cycleCountMachine p mem) := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simp [requiredFlowOnly]
    · simp [requiredFlowOnly]
    · simp [requiredFlowOnly]
    · simpa [requiredFlowOnly, FLOW_CAP] using hreq
    · simp [requiredFlowOnly]
  exact engineLowerBound_le_of_fits _ _ hfit

theorem global_engine_load_lower_bound_kernel_machine_of_requiredLoadOps
    (spec : Memory → Output) (memOk : Memory → Prop)
    (p : Program) (_hcorrect : CorrectOnMachine spec p memOk)
    (hstraight : StraightLine p)
    (hsafeExec : ∀ mem, memOk mem → SafeExec p mem)
    (mem : Memory) (hmemOk : memOk mem)
    (loadReq : Nat) (hreq : loadReq ≤ loadOpCountMachine p mem) :
    engineLowerBound (requiredLoadOnly loadReq) ≤ cycleCountMachine p mem := by
  exact engine_load_lower_bound_of_requiredLoadOps_straightLine_safeExec
    p hstraight mem (hsafeExec mem hmemOk) loadReq hreq

theorem global_engine_flow_lower_bound_kernel_machine_of_requiredFlowOps
    (spec : Memory → Output) (memOk : Memory → Prop)
    (p : Program) (_hcorrect : CorrectOnMachine spec p memOk)
    (_hstraight : StraightLine p)
    (_hsafeExec : ∀ mem, memOk mem → SafeExec p mem)
    (mem : Memory) (_hmemOk : memOk mem)
    (flowReq : Nat) (hreq : flowReq ≤ cycleCountMachine p mem) :
    engineLowerBound (requiredFlowOnly flowReq) ≤ cycleCountMachine p mem := by
  exact engine_flow_lower_bound_of_requiredFlowOps p mem flowReq hreq

end ProofGlobalLowerBound
