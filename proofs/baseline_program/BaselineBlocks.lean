import proofs.baseline_program.BaselineHelpers

open ProofISA
open ProofMachine
open ProofGlobalLowerBound

def blockTemplate (c : Nat) : List Instruction := [
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

def blockConstRegs : List Nat := [
  10, 11, 12, 26, 29, 22, 30, 31, 32, 24, 33, 34, 18, 35, 36, 37,
  28, 38, 39, 20, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51,
  52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67,
  68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83,
  84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99,
  100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115,
  116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131,
  132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147,
  148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163,
  164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179,
  180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195,
  196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211,
  212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227,
  228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243,
  244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254, 255, 256, 257, 258, 259,
  260, 261, 262, 263, 264, 265, 266, 267, 268, 269, 270, 271, 272, 273, 274, 275
]

def blockConstReg (i : Fin BATCH_SIZE) : Nat :=
  blockConstRegs.get i

lemma blockConstReg_eq (i : Fin BATCH_SIZE) : blockConstReg i = 10 + i := by
  native_decide

def baselineBlocks : List (List Instruction) :=
  blockConstRegs.map blockTemplate
