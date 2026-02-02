import proofs.common.Machine
import proofs.common.ISA
import proofs.global_lower_bound.LowerBound

open ProofISA
open ProofMachine
open ProofGlobalLowerBound

def instrAlu (op : AluOp) (dest a1 a2 : Nat) : Instruction :=
  { alu := [{ op := op, dest := dest, a1 := a1, a2 := a2 }] }

def instrLoad (slot : LoadSlot) : Instruction :=
  { load := [slot] }

def instrStore (slot : StoreSlot) : Instruction :=
  { store := [slot] }

def instrFlow (slot : FlowSlot) : Instruction :=
  { flow := [slot] }
