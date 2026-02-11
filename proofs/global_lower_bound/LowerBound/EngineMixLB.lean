import proofs.global_lower_bound.LowerBound.MachineTraceEq

namespace ProofGlobalLowerBound
open ProofCommon
open ProofMachine
open ProofISA

/-!
Engine-mix lower-bound arithmetic.

This module is intentionally semantic-agnostic: it only states/proves the
throughput conversion from per-engine required op counts to a cycle lower bound.
Future files can supply the hard "required op counts" lemmas for `spec_kernel`.
-/

structure EngineCounts where
  valu : Nat
  alu : Nat
  load : Nat
  flow : Nat
  store : Nat

def engineLowerBound (c : EngineCounts) : Nat :=
  max (ceilDiv c.valu VALU_CAP)
    (max (ceilDiv c.alu ALU_CAP)
      (max (ceilDiv c.load LOAD_CAP)
        (max c.flow (ceilDiv c.store STORE_CAP))))

def FitsEngineBudget (c : EngineCounts) (cycles : Nat) : Prop :=
  c.valu ≤ VALU_CAP * cycles ∧
  c.alu ≤ ALU_CAP * cycles ∧
  c.load ≤ LOAD_CAP * cycles ∧
  c.flow ≤ FLOW_CAP * cycles ∧
  c.store ≤ STORE_CAP * cycles

def engineCountsOfProgramList : List Instruction → EngineCounts
  | [] => ⟨0, 0, 0, 0, 0⟩
  | i :: rest =>
      let c := engineCountsOfProgramList rest
      ⟨i.valu.length + c.valu,
       i.alu.length + c.alu,
       i.load.length + c.load,
       i.flow.length + c.flow,
       i.store.length + c.store⟩

def engineCountsOfProgram (p : Program) : EngineCounts :=
  engineCountsOfProgramList p.program

lemma engineCountsOfProgramList_fits_length_of_wellFormed
    (prog : List Instruction)
    (hWF : ∀ i, i ∈ prog → instrWellFormed i) :
    FitsEngineBudget (engineCountsOfProgramList prog) prog.length := by
  induction prog with
  | nil =>
      simp [engineCountsOfProgramList, FitsEngineBudget]
  | cons i rest ih =>
      have hi : instrWellFormed i := hWF i (by simp)
      have hrestWF : ∀ j, j ∈ rest → instrWellFormed j := by
        intro j hj
        exact hWF j (by simp [hj])
      have hrest := ih hrestWF
      rcases hi with ⟨halu_i, hvalu_i, hload_i, hstore_i, hflow_i, _hscratch_i⟩
      rcases hrest with ⟨hvalu_r, halu_r, hload_r, hflow_r, hstore_r⟩
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · -- VALU
        have hsum : i.valu.length + (engineCountsOfProgramList rest).valu ≤
            VALU_CAP + VALU_CAP * rest.length :=
          Nat.add_le_add hvalu_i hvalu_r
        simpa [engineCountsOfProgramList, Nat.mul_add, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
          using hsum
      · -- ALU
        have hsum : i.alu.length + (engineCountsOfProgramList rest).alu ≤
            ALU_CAP + ALU_CAP * rest.length :=
          Nat.add_le_add halu_i halu_r
        simpa [engineCountsOfProgramList, Nat.mul_add, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
          using hsum
      · -- LOAD
        have hsum : i.load.length + (engineCountsOfProgramList rest).load ≤
            LOAD_CAP + LOAD_CAP * rest.length :=
          Nat.add_le_add hload_i hload_r
        simpa [engineCountsOfProgramList, Nat.mul_add, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
          using hsum
      · -- FLOW
        have hsum : i.flow.length + (engineCountsOfProgramList rest).flow ≤
            FLOW_CAP + FLOW_CAP * rest.length :=
          Nat.add_le_add hflow_i hflow_r
        simpa [engineCountsOfProgramList, Nat.mul_add, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
          using hsum
      · -- STORE
        have hsum : i.store.length + (engineCountsOfProgramList rest).store ≤
            STORE_CAP + STORE_CAP * rest.length :=
          Nat.add_le_add hstore_i hstore_r
        simpa [engineCountsOfProgramList, Nat.mul_add, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
          using hsum

lemma engineCountsOfProgram_fits_length_of_wellFormed
    (p : Program)
    (hWF : ∀ i, i ∈ p.program → instrWellFormed i) :
    FitsEngineBudget (engineCountsOfProgram p) p.program.length := by
  simpa [engineCountsOfProgram] using
    engineCountsOfProgramList_fits_length_of_wellFormed p.program hWF

lemma engineLowerBound_le_of_fits (c : EngineCounts) (cycles : Nat)
    (hfit : FitsEngineBudget c cycles) :
    engineLowerBound c ≤ cycles := by
  rcases hfit with ⟨hvalu, halu, hload, hflow, hstore⟩
  have hvalu' : ceilDiv c.valu VALU_CAP ≤ cycles :=
    ceilDiv_le_of_mul_le (by decide : 0 < VALU_CAP) hvalu
  have halu' : ceilDiv c.alu ALU_CAP ≤ cycles :=
    ceilDiv_le_of_mul_le (by decide : 0 < ALU_CAP) halu
  have hload' : ceilDiv c.load LOAD_CAP ≤ cycles :=
    ceilDiv_le_of_mul_le (by decide : 0 < LOAD_CAP) hload
  have hflow' : c.flow ≤ cycles := by
    simpa [FLOW_CAP] using hflow
  have hstore' : ceilDiv c.store STORE_CAP ≤ cycles :=
    ceilDiv_le_of_mul_le (by decide : 0 < STORE_CAP) hstore
  refine max_le_iff.2 ?_
  refine ⟨hvalu', ?_⟩
  refine max_le_iff.2 ?_
  refine ⟨halu', ?_⟩
  refine max_le_iff.2 ?_
  refine ⟨hload', ?_⟩
  exact max_le_iff.2 ⟨hflow', hstore'⟩

def loadStoreLowerBound (loadOps storeOps : Nat) : Nat :=
  max (ceilDiv loadOps LOAD_CAP) (ceilDiv storeOps STORE_CAP)

lemma loadStoreLowerBound_le_of_fits (loadOps storeOps cycles : Nat)
    (hload : loadOps ≤ LOAD_CAP * cycles)
    (hstore : storeOps ≤ STORE_CAP * cycles) :
    loadStoreLowerBound loadOps storeOps ≤ cycles := by
  have hload' : ceilDiv loadOps LOAD_CAP ≤ cycles :=
    ceilDiv_le_of_mul_le (by decide : 0 < LOAD_CAP) hload
  have hstore' : ceilDiv storeOps STORE_CAP ≤ cycles :=
    ceilDiv_le_of_mul_le (by decide : 0 < STORE_CAP) hstore
  exact max_le_iff.2 ⟨hload', hstore'⟩

end ProofGlobalLowerBound
