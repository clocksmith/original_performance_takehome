import Mathlib
import proofs.common.Base

namespace ProofCacheTop4D4x15ResetOffload1016ParityOff
open ProofCommon

/-- Guard for tool compatibility. -/
def GUARD : Nat := 0

/-- Target cycle budget for this strategy. -/
def totalCycles : Nat := 1312

/-- Engine caps (from ISA). -/
def FLOW_CAP : Nat := 1
def LOAD_CAP : Nat := 2
def STORE_CAP : Nat := 2

/-- Flow ops for cached-node selection (setup included). -/
def flowOps : Nat := 993

lemma flow_capacity : flowOps ≤ FLOW_CAP * totalCycles := by
  native_decide

/-- Load ops for cached-node preloads + vloads + uncached rounds (setup included). -/
def totalLoadOps : Nat := 2065

lemma load_capacity : totalLoadOps ≤ LOAD_CAP * totalCycles := by
  native_decide

/-- Store ops (vstore values once). -/
def storeOps : Nat := VECTORS

lemma store_capacity : storeOps ≤ STORE_CAP * totalCycles := by
  native_decide

/-! ## VALU + ALU accounting -/

/-- Total VALU ops for this strategy (setup included). -/
def totalVALU : Nat := 7870

lemma valu_capacity : totalVALU ≤ VALU_CAP * totalCycles := by
  native_decide

/-- Base ALU ops (selection + address compute + parity offload). -/
def totalALUOps : Nat := 11047

lemma alu_capacity : totalALUOps ≤ ALU_CAP * totalCycles := by
  native_decide

/-- Combined schedule skeleton: capacity + flow + load + store. -/
theorem schedule_skeleton :
  totalALUOps ≤ ALU_CAP * totalCycles ∧
  flowOps ≤ FLOW_CAP * totalCycles ∧
  totalLoadOps ≤ LOAD_CAP * totalCycles ∧
  storeOps ≤ STORE_CAP * totalCycles ∧
  totalVALU ≤ VALU_CAP * totalCycles ∧
  totalCycles = 1312 := by
  refine ⟨alu_capacity, flow_capacity, load_capacity, store_capacity, valu_capacity, rfl⟩

end ProofCacheTop4D4x15ResetOffload1016ParityOff
