import Mathlib

namespace ProofISA

/-! ### ISA constants (from problem.py) -/

def VLEN : Nat := 8
def MOD32 : Nat := 2 ^ 32
def VALU_CAP : Nat := 6
def ALU_CAP : Nat := 12
def LOAD_CAP : Nat := 2
def STORE_CAP : Nat := 2
def FLOW_CAP : Nat := 1
def SCRATCH_SIZE : Nat := 1536

/-! ### Problem instance constants -/

def ROUNDS : Nat := 16
def VECTORS : Nat := 32
def LANES : Nat := VECTORS * VLEN

def HEIGHT : Nat := 10
def N_NODES : Nat := 2^(HEIGHT + 1) - 1

/-- Standard batch size for the 256-element instance. -/
def BATCH_SIZE : Nat := VECTORS * VLEN

/-- Guard for the cache_top4_d4x15_reset_offload schedule instance. -/
def cache_top4_d4x15_reset_offload_instance
    (forest_height n_nodes batch_size rounds : Nat) : Prop :=
  forest_height = HEIGHT ∧
  n_nodes = N_NODES ∧
  batch_size = BATCH_SIZE ∧
  rounds = ROUNDS

lemma cache_top4_d4x15_reset_offload_instance_std :
    cache_top4_d4x15_reset_offload_instance HEIGHT N_NODES BATCH_SIZE ROUNDS := by
  simp [cache_top4_d4x15_reset_offload_instance, BATCH_SIZE]

end ProofISA
