import Mathlib
import proofs.baseline_program.BlockSymbolic
import proofs.global_lower_bound.LowerBound

open ProofISA
open ProofMachine
open ProofGlobalLowerBound

/-! ## Block symbolic to spec correspondence (hash only)

This file isolates the hash computation equivalence used by the block
correctness proof.
-/-

def hash6 (x : Nat) : Nat :=
  let x1 := aluEval AluOp.add x 0x7ED55D16
  let x2 := aluEval AluOp.shl x 12
  let x3 := aluEval AluOp.add x1 x2
  let x4 := aluEval AluOp.xor x3 0xC761C23C
  let x5 := aluEval AluOp.shr x3 19
  let x6 := aluEval AluOp.xor x4 x5
  let x7 := aluEval AluOp.add x6 0x165667B1
  let x8 := aluEval AluOp.shl x6 5
  let x9 := aluEval AluOp.add x7 x8
  let x10 := aluEval AluOp.add x9 0xD3A2646C
  let x11 := aluEval AluOp.shl x9 9
  let x12 := aluEval AluOp.xor x10 x11
  let x13 := aluEval AluOp.add x12 0xFD7046C5
  let x14 := aluEval AluOp.shl x12 3
  let x15 := aluEval AluOp.add x13 x14
  let x16 := aluEval AluOp.xor x15 0xB55A4F09
  let x17 := aluEval AluOp.shr x15 16
  aluEval AluOp.xor x16 x17

lemma hash6_eq_myhash (x : Nat) : hash6 x = myhash x := by
  simp [hash6, myhash, HASH_STAGES, hashStage, List.foldl]
