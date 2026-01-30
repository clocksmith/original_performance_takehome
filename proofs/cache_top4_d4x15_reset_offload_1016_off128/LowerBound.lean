import Mathlib
import proofs.common.Base

namespace ProofCachetop4D4X15Resetoffload1016Off128
open ProofCommon

/-- Guard for tool compatibility. -/
def GUARD : Nat := 0

/-- Target cycle budget for this strategy. -/
def totalCycles : Nat := 1647

/-- Engine caps (from ISA). -/
def FLOW_CAP : Nat := 1
def LOAD_CAP : Nat := 2
def STORE_CAP : Nat := 2

/-- Flow ops for cached-node selection (setup included). -/
def flowOps : Nat := 993

lemma flow_capacity : flowOps ≤ FLOW_CAP * totalCycles := by
  native_decide

/-- Load ops for cached-node preloads + vloads + uncached rounds (setup included). -/
def totalLoadOps : Nat := 2066

lemma load_capacity : totalLoadOps ≤ LOAD_CAP * totalCycles := by
  native_decide

/-- Store ops (vstore values once). -/
def storeOps : Nat := VECTORS

lemma store_capacity : storeOps ≤ STORE_CAP * totalCycles := by
  native_decide

/-! ## VALU + ALU accounting -/

/-- Total VALU ops for this strategy (after any offload). -/
def totalVALU : Nat := 8190

/-- Offload needed at cycle budget T. -/
def offloadNeeded (T : Nat) : Nat := totalVALU - VALU_CAP * T

lemma offload_needed : offloadNeeded totalCycles = 0 := by
  native_decide

lemma offloadCap_ok : offloadNeeded totalCycles ≤ offloadCap totalCycles := by
  native_decide

/-- Base ALU ops (selection + address compute), before any additional offload. -/
def BASE_ALU_OPS : Nat := 8487

def totalALUOps (T : Nat) : Nat := BASE_ALU_OPS + offloadNeeded T * VLEN

lemma alu_capacity : totalALUOps totalCycles ≤ ALU_CAP * totalCycles := by
  native_decide

/-- Combined schedule skeleton: capacity + flow + load + store. -/
theorem schedule_skeleton :
  offloadNeeded totalCycles = 0 ∧
  offloadNeeded totalCycles ≤ offloadCap totalCycles ∧
  totalALUOps totalCycles ≤ ALU_CAP * totalCycles ∧
  flowOps ≤ FLOW_CAP * totalCycles ∧
  totalLoadOps ≤ LOAD_CAP * totalCycles ∧
  storeOps ≤ STORE_CAP * totalCycles ∧
  totalCycles = 1647 := by
  refine ⟨offload_needed, offloadCap_ok, alu_capacity, flow_capacity, load_capacity, store_capacity, rfl⟩

end ProofCachetop4D4X15Resetoffload1016Off128
