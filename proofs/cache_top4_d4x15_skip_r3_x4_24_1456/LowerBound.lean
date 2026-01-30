import Mathlib
import proofs.common.Base

namespace ProofCacheTop4D4x15SkipR3X4241456
open ProofCommon

/-- Guard for tool compatibility. -/
def GUARD : Nat := 0

/-- Target cycle budget for this strategy. -/
def totalCycles : Nat := 1456

/-- Engine caps (from ISA). -/
def FLOW_CAP : Nat := 1
def LOAD_CAP : Nat := 2
def STORE_CAP : Nat := 2

/-- Flow ops for cached-node selection (setup included). -/
def flowOps : Nat := 904

lemma flow_capacity_1456 : flowOps ≤ FLOW_CAP * totalCycles := by
  native_decide

/-- Load ops for cached-node preloads + vloads + uncached rounds (setup included). -/
def totalLoadOps : Nat := 2250

lemma load_capacity_1456 : totalLoadOps ≤ LOAD_CAP * totalCycles := by
  native_decide

/-- Store ops (vstore values once). -/
def storeOps : Nat := VECTORS

lemma store_capacity_1456 : storeOps ≤ STORE_CAP * totalCycles := by
  native_decide

/-! ## VALU + ALU accounting -/

/-- Total VALU ops for this strategy (after parity offload). -/
def totalVALU1456 : Nat := 7509

/-- Offload needed at cycle budget T. -/
def offloadNeeded (T : Nat) : Nat := totalVALU1456 - VALU_CAP * T

lemma offload_needed_1456 : offloadNeeded totalCycles = 0 := by
  native_decide

lemma offloadCap_1456 : offloadCap totalCycles = 2184 := by
  native_decide

lemma offload_feasible_1456 : offloadNeeded totalCycles ≤ offloadCap totalCycles := by
  native_decide

/-- Base ALU ops (selection + address compute), before any additional offload. -/
def BASE_ALU_OPS : Nat := 10336

def totalALUOps (T : Nat) : Nat := BASE_ALU_OPS + offloadNeeded T * VLEN

lemma alu_capacity_1456 : totalALUOps totalCycles ≤ ALU_CAP * totalCycles := by
  native_decide

/-- Combined schedule skeleton: capacity + flow + load + store. -/
theorem schedule_skeleton :
  offloadNeeded totalCycles = 0 ∧
  offloadNeeded totalCycles ≤ offloadCap totalCycles ∧
  totalALUOps totalCycles ≤ ALU_CAP * totalCycles ∧
  flowOps ≤ FLOW_CAP * totalCycles ∧
  totalLoadOps ≤ LOAD_CAP * totalCycles ∧
  storeOps ≤ STORE_CAP * totalCycles ∧
  totalCycles = 1456 := by
  refine ⟨offload_needed_1456, offload_feasible_1456, alu_capacity_1456, flow_capacity_1456, load_capacity_1456, store_capacity_1456, rfl⟩

end ProofCacheTop4D4x15SkipR3X4241456
