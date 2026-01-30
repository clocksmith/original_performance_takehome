import Mathlib
import proofs.common.Base

namespace ProofCacheTop4D4x15ResetOffload1227
open ProofCommon

/-- Guard for tool compatibility. -/
def GUARD : Nat := 0

/-- Target cycle budget for this strategy. -/
def totalCycles : Nat := 1227

/-- Engine caps (from ISA). -/
def FLOW_CAP : Nat := 1
def LOAD_CAP : Nat := 2
def STORE_CAP : Nat := 2

/-- Flow ops for cached-node selection (setup excluded). -/
def flowOps : Nat := 929

lemma flow_capacity_1227 : flowOps ≤ FLOW_CAP * totalCycles := by
  native_decide

/-- Load ops for cached-node preloads + vloads + uncached rounds (setup excluded). -/
def totalLoadOps : Nat := 1928

lemma load_capacity_1227 : totalLoadOps ≤ LOAD_CAP * totalCycles := by
  native_decide

/-- Store ops (vstore values once). -/
def storeOps : Nat := VECTORS

lemma store_capacity_1227 : storeOps ≤ STORE_CAP * totalCycles := by
  native_decide

/-! ## VALU + ALU accounting -/

/-- Total VALU ops for this strategy (setup excluded). -/
def totalVALU1227 : Nat := 8273

/-- Offload needed at cycle budget T. -/
def offloadNeeded (T : Nat) : Nat := totalVALU1227 - VALU_CAP * T

lemma offload_needed_1227 : offloadNeeded totalCycles = 911 := by
  native_decide

lemma offloadCap_1227 : offloadCap totalCycles = 1840 := by
  native_decide

lemma offload_feasible_1227 : offloadNeeded totalCycles ≤ offloadCap totalCycles := by
  native_decide

/-- Base ALU ops (selection + address compute), before offload. -/
def BASE_ALU_OPS : Nat := 7432

def totalALUOps (T : Nat) : Nat := BASE_ALU_OPS + offloadNeeded T * VLEN

lemma alu_capacity_1227 : totalALUOps totalCycles ≤ ALU_CAP * totalCycles := by
  native_decide

/-- Combined schedule skeleton: capacity + flow + load + store. -/
theorem schedule_skeleton :
  offloadNeeded totalCycles = 911 ∧
  offloadNeeded totalCycles ≤ offloadCap totalCycles ∧
  totalALUOps totalCycles ≤ ALU_CAP * totalCycles ∧
  flowOps ≤ FLOW_CAP * totalCycles ∧
  totalLoadOps ≤ LOAD_CAP * totalCycles ∧
  storeOps ≤ STORE_CAP * totalCycles ∧
  totalCycles = 1227 := by
  refine ⟨offload_needed_1227, offload_feasible_1227, alu_capacity_1227, flow_capacity_1227, load_capacity_1227, store_capacity_1227, rfl⟩

end ProofCacheTop4D4x15ResetOffload1227
