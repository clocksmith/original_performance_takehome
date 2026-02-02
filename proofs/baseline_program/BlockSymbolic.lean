import proofs.baseline_program.BaselineBlocks
import proofs.global_lower_bound.LowerBound

open ProofISA
open ProofMachine
open ProofGlobalLowerBound

def blockTemplateSnapshot (c : Nat) : List Instruction := [
  instrAlu AluOp.add 16 8 c,
  instrLoad (LoadSlot.load 13 16),
  instrAlu AluOp.add 16 9 c,
  instrLoad (LoadSlot.load 14 16),
  instrAlu AluOp.add 16 7 13,
  instrLoad (LoadSlot.load 15 16),
  instrAlu AluOp.xor 14 14 15,
  instrAlu AluOp.add 0 14 17,
  instrAlu AluOp.shl 1 14 18,
  instrAlu AluOp.add 14 0 1,
  instrAlu AluOp.xor 0 14 19,
  instrAlu AluOp.shr 1 14 20,
  instrAlu AluOp.xor 14 0 1,
  instrAlu AluOp.add 0 14 21,
  instrAlu AluOp.shl 1 14 22,
  instrAlu AluOp.add 14 0 1,
  instrAlu AluOp.add 0 14 23,
  instrAlu AluOp.shl 1 14 24,
  instrAlu AluOp.xor 14 0 1,
  instrAlu AluOp.add 0 14 25,
  instrAlu AluOp.shl 1 14 26,
  instrAlu AluOp.add 14 0 1,
  instrAlu AluOp.xor 0 14 27,
  instrAlu AluOp.shr 1 14 28,
  instrAlu AluOp.xor 14 0 1,
  instrAlu AluOp.mod 0 14 12,
  instrAlu AluOp.eq 0 0 10,
  instrFlow (FlowSlot.select 2 0 11 12),
  instrAlu AluOp.mul 13 13 12,
  instrAlu AluOp.add 13 13 2,
  instrAlu AluOp.lt 0 13 4,
  instrFlow (FlowSlot.select 13 0 13 10),
  instrAlu AluOp.add 16 8 c,
  instrStore (StoreSlot.store 16 13),
  instrAlu AluOp.add 16 9 c,
  instrStore (StoreSlot.store 16 14),
]

lemma blockTemplateSnapshot_eq (c : Nat) :
    blockTemplateSnapshot c = blockTemplate c := by
  rfl

def blockSym (s : Nat → Nat) (mem : Memory) (c : Nat) : (Nat → Nat) × Memory := by
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
  exact (s34, mem2)
