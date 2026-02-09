import proofs.global_lower_bound.LowerBound.Defs

namespace ProofGlobalLowerBound
open ProofCommon
open ProofMachine
open ProofISA

/-! ### Adversarial input lemma for values-slice spec -/

def spec_values (mem : Memory) : Output :=
  outputOf (memAt mem PTR_INP_VAL) mem

/-! ### Full-kernel spec (reference semantics) -/

def HASH_STAGES : List (AluOp × Nat × AluOp × AluOp × Nat) :=
  [ (AluOp.add, 0x7ED55D16, AluOp.add, AluOp.shl, 12),
    (AluOp.xor, 0xC761C23C, AluOp.xor, AluOp.shr, 19),
    (AluOp.add, 0x165667B1, AluOp.add, AluOp.shl, 5),
    (AluOp.add, 0xD3A2646C, AluOp.xor, AluOp.shl, 9),
    (AluOp.add, 0xFD7046C5, AluOp.add, AluOp.shl, 3),
    (AluOp.xor, 0xB55A4F09, AluOp.xor, AluOp.shr, 16) ]

def hashStage (x : Nat) (stage : AluOp × Nat × AluOp × AluOp × Nat) : Nat :=
  let (op1, v1, op2, op3, v3) := stage
  let a := aluEval op1 x v1
  let b := aluEval op3 x v3
  aluEval op2 a b

def myhash (x : Nat) : Nat :=
  HASH_STAGES.foldl hashStage x

-- IMPORTANT: `myhash` expands into large arithmetic constants. Letting the kernel unfold it
-- during definitional equality checking can trigger "kernel deep recursion" errors.
-- We keep it unfoldable when explicitly requested (e.g. in `myhash_mod32` / `native_decide`),
-- but mark it irreducible to prevent accidental unfolding.
attribute [irreducible] myhash

lemma aluEval_mod32 (op : AluOp) (a1 a2 : Nat) :
    aluEval op a1 a2 = mod32 (aluEval op a1 a2) := by
  cases op with
  | add => simp [aluEval, mod32]
  | sub => simp [aluEval, mod32]
  | mul => simp [aluEval, mod32]
  | idiv =>
      by_cases h : a2 = 0
      · simp [aluEval, h, mod32]
      · simp [aluEval, h, mod32]
  | cdiv =>
      by_cases h : a2 = 0
      · simp [aluEval, mod32]
      · simp [aluEval, mod32]
  | xor => simp [aluEval, mod32]
  | band => simp [aluEval, mod32]
  | bor => simp [aluEval, mod32]
  | shl => simp [aluEval, mod32, shl]
  | shr => simp [aluEval, mod32, shr]
  | mod =>
      by_cases h : a2 = 0
      · simp [aluEval, h, mod32]
      · simp [aluEval, h, mod32]
  | lt =>
      by_cases h : a1 < a2
      · have h1 : (1:Nat) < MOD32 := by decide
        have hmod : (1:Nat) % MOD32 = (1:Nat) := Nat.mod_eq_of_lt h1
        simpa [h, hmod, aluEval]
      · have h0 : (0:Nat) < MOD32 := by decide
        have hmod : (0:Nat) % MOD32 = (0:Nat) := Nat.mod_eq_of_lt h0
        simpa [h, hmod, aluEval]
  | eq =>
      by_cases h : a1 = a2
      · have h1 : (1:Nat) < MOD32 := by decide
        have hmod : (1:Nat) % MOD32 = (1:Nat) := Nat.mod_eq_of_lt h1
        simpa [h, hmod, aluEval]
      · have h0 : (0:Nat) < MOD32 := by decide
        have hmod : (0:Nat) % MOD32 = (0:Nat) := Nat.mod_eq_of_lt h0
        simpa [h, hmod, aluEval]

lemma hashStage_mod32 (x : Nat) (stage : AluOp × Nat × AluOp × AluOp × Nat) :
    hashStage x stage = mod32 (hashStage x stage) := by
  rcases stage with ⟨op1, v1, op2, op3, v3⟩
  have h := aluEval_mod32 op2 (aluEval op1 x v1) (aluEval op3 x v3)
  simpa [hashStage] using h

lemma foldl_hashStage_mod32 (acc : Nat) (l : List (AluOp × Nat × AluOp × AluOp × Nat))
    (hacc : acc = mod32 acc) :
    List.foldl hashStage acc l = mod32 (List.foldl hashStage acc l) := by
  induction l generalizing acc with
  | nil =>
      simpa using hacc
  | cons stage tail ih =>
      -- foldl on cons
      have hstage : hashStage acc stage = mod32 (hashStage acc stage) :=
        hashStage_mod32 acc stage
      -- apply IH to the new accumulator
      simpa [List.foldl] using
        (ih (acc := hashStage acc stage) hstage)

lemma foldl_hashStage_mod32_nonempty (acc : Nat)
    (l : List (AluOp × Nat × AluOp × AluOp × Nat)) (hne : l ≠ []) :
    List.foldl hashStage acc l = mod32 (List.foldl hashStage acc l) := by
  cases l with
  | nil =>
      cases hne rfl
  | cons stage tail =>
      -- after first stage accumulator is mod32
      have hacc : hashStage acc stage = mod32 (hashStage acc stage) :=
        hashStage_mod32 acc stage
      simpa [List.foldl] using (foldl_hashStage_mod32 (acc := hashStage acc stage) (l := tail) hacc)

lemma myhash_mod32 (x : Nat) : myhash x = mod32 (myhash x) := by
  -- HASH_STAGES is nonempty, so after the first stage the accumulator is mod32
  unfold myhash
  have hne : (HASH_STAGES : List (AluOp × Nat × AluOp × AluOp × Nat)) ≠ [] := by
    decide
  simpa using (foldl_hashStage_mod32_nonempty x HASH_STAGES hne)

lemma mod32_myhash (x : Nat) : mod32 (myhash x) = myhash x := by
  symm
  exact myhash_mod32 x

def step (tree : Nat → Nat) (nNodes idx val : Nat) : Nat × Nat :=
  let node := tree idx
  let val' := myhash (aluEval AluOp.xor val node)
  let idx' := 2 * idx + (if val' % 2 = 0 then 1 else 2)
  let idx'' := if idx' ≥ nNodes then 0 else idx'
  (idx'', val')

def iterRounds (tree : Nat → Nat) (nNodes : Nat) (n idx val : Nat) : Nat × Nat :=
  match n with
  | 0 => (idx, val)
  | Nat.succ n =>
      let st := step tree nNodes idx val
      iterRounds tree nNodes n st.1 st.2

lemma iterRounds_zero (tree : Nat → Nat) (nNodes idx val : Nat) :
    iterRounds tree nNodes 0 idx val = (idx, val) := by
  rfl

def spec_kernel (mem : Memory) : Output :=
  let rounds := memAt mem 0
  let nNodes := memAt mem 1
  let forestPtr := memAt mem PTR_FOREST
  let idxPtr := memAt mem PTR_INP_IDX
  let valPtr := memAt mem PTR_INP_VAL
  let tree := fun i => memAt mem (forestPtr + i)
  fun i =>
    let idx0 := memAt mem (idxPtr + i)
    let val0 := memAt mem (valPtr + i)
    let (_, valF) := iterRounds tree nNodes rounds idx0 val0
    valF

def iterHash : Nat → Nat → Nat
  | 0, v => v
  | Nat.succ n, v => iterHash n (myhash v)

def zeroTree : Nat → Nat := fun _ => 0

lemma natXor_zero_right (n : Nat) : natXor n 0 = n := by
  simp [natXor, Nat.bitwise_zero_right]

lemma aluEval_xor_zero (val : Nat) : aluEval AluOp.xor val 0 = mod32 val := by
  simp [aluEval, natXor_zero_right]

lemma step_zeroTree_val (idx val : Nat) :
    (step zeroTree N_NODES idx val).2 = myhash (mod32 val) := by
  unfold step
  dsimp [zeroTree]
  -- reduce to aluEval xor on 0
  apply congrArg
  exact aluEval_xor_zero val

lemma step_idx_lt (tree : Nat → Nat) (nNodes idx val : Nat) (hnpos : 0 < nNodes) :
    (step tree nNodes idx val).1 < nNodes := by
  dsimp [step]
  set node := tree idx
  set val' := myhash (aluEval AluOp.xor val node)
  set idx' := 2 * idx + (if val' % 2 = 0 then 1 else 2)
  by_cases hge : idx' ≥ nNodes
  · have hpos : 0 < nNodes := hnpos
    simp [hge, hpos]
  · have hlt : idx' < nNodes := lt_of_not_ge hge
    simp [hge, hlt]

theorem iterRounds_zero_tree_val_range_succ (tree : Nat → Nat) (nNodes : Nat)
    (hzero : ∀ i < nNodes, tree i = 0) (hnpos : 0 < nNodes) :
    ∀ n idx val, idx < nNodes →
      (iterRounds tree nNodes (Nat.succ n) idx val).2 = iterHash (Nat.succ n) (mod32 val) := by
  intro n
  induction n with
  | zero =>
      intro idx val hidx
      have hnode : tree idx = 0 := hzero idx hidx
      -- unfold just enough to expose the single `step`
      simp only [iterRounds, iterHash]
      simp [step, hnode, aluEval_xor_zero]
  | succ n ih =>
      intro idx val hidx
      have hstepIdx : (step tree nNodes idx val).1 < nNodes :=
        step_idx_lt tree nNodes idx val hnpos
      have hrest :
          (iterRounds tree nNodes (Nat.succ n)
              (step tree nNodes idx val).1 (step tree nNodes idx val).2).2 =
            iterHash (Nat.succ n) (mod32 ((step tree nNodes idx val).2)) :=
        ih (idx := (step tree nNodes idx val).1) (val := (step tree nNodes idx val).2) hstepIdx
      have hnode : tree idx = 0 := hzero idx hidx
      have hstepVal : (step tree nNodes idx val).2 = myhash (mod32 val) := by
        simp [step, hnode, aluEval_xor_zero]
      have hmod : mod32 ((step tree nNodes idx val).2) = myhash (mod32 val) := by
        calc
          mod32 ((step tree nNodes idx val).2) = mod32 (myhash (mod32 val)) := by
            simpa [hstepVal]
          _ = myhash (mod32 val) := mod32_myhash (mod32 val)
      calc
        (iterRounds tree nNodes (Nat.succ (Nat.succ n)) idx val).2 =
            (iterRounds tree nNodes (Nat.succ n)
                (step tree nNodes idx val).1 (step tree nNodes idx val).2).2 := by
              simp [iterRounds]
        _ = iterHash (Nat.succ n) (mod32 ((step tree nNodes idx val).2)) := hrest
        _ = iterHash (Nat.succ n) (myhash (mod32 val)) := by
              simp [hmod]
        _ = iterHash (Nat.succ (Nat.succ n)) (mod32 val) := by
              rfl

theorem spec_kernel_uniform_val (mem : Memory) (i : Fin BATCH_SIZE) (v : Nat)
    (hrounds : memAt mem 0 = ROUNDS)
    (hnodes : memAt mem 1 = N_NODES)
    (hforest : ∀ k, k < N_NODES → memAt mem (memAt mem PTR_FOREST + k) = 0)
    (hidx : memAt mem (memAt mem PTR_INP_IDX + i) = 0)
    (hval : memAt mem (memAt mem PTR_INP_VAL + i) = v) :
    spec_kernel mem i = iterHash ROUNDS (mod32 v) := by
  classical
  -- expand `spec_kernel` at lane `i`
  simp [spec_kernel, hrounds, hnodes, hidx, hval]
  -- discharge the iterRounds value component using the zero-tree lemma
  let forestPtr := memAt mem PTR_FOREST
  let tree : Nat → Nat := fun k => memAt mem (forestPtr + k)
  have htree0 : ∀ k < N_NODES, tree k = 0 := by
    intro k hk
    simpa [tree, forestPtr] using hforest k hk
  have hnpos : 0 < N_NODES := by
    -- N_NODES = 2^(HEIGHT+1) - 1, so it's positive for the standard instance
    decide
  have hrounds_pos : 1 ≤ ROUNDS := by
    decide
  have hrounds_succ : (ROUNDS - 1) + 1 = ROUNDS :=
    Nat.sub_add_cancel hrounds_pos
  -- `idx0 = 0` is in range
  have hidx0 : (0 : Nat) < N_NODES := hnpos
  -- apply the `n+1` lemma at `n = ROUNDS - 1`
  have hvalF :
      (iterRounds tree N_NODES ((ROUNDS - 1) + 1) 0 v).2 = iterHash ((ROUNDS - 1) + 1) (mod32 v) := by
    simpa using
      iterRounds_zero_tree_val_range_succ tree N_NODES htree0 hnpos (n := ROUNDS - 1)
        (idx := 0) (val := v) hidx0
  -- rewrite `(ROUNDS - 1) + 1`
  simpa [tree, forestPtr, hrounds_succ] using hvalF

def memUniform0 : Memory :=
  { data :=
      fun a =>
        if a = 0 then ROUNDS
        else if a = 1 then N_NODES
        else if a = 2 then BATCH_SIZE
        else if a = 3 then HEIGHT
        else if a = PTR_FOREST then FOREST_BASE
        else if a = PTR_INP_IDX then IDX_BASE
        else if a = PTR_INP_VAL then VAL_BASE
        else if FOREST_BASE ≤ a ∧ a < FOREST_BASE + N_NODES then 0
        else if IDX_BASE ≤ a ∧ a < IDX_BASE + BATCH_SIZE then 0
        else if VAL_BASE ≤ a ∧ a < VAL_BASE + BATCH_SIZE then 0
        else 0,
    size := MEM_SIZE }

def memUpdate (mem : Memory) (addr val : Nat) : Memory :=
  { mem with data := fun a => if a = addr then val else mem.data a }

lemma memUpdate_ptr_eq (mem : Memory) (addr val : Nat) (hneq : addr ≠ PTR_INP_VAL) :
    memAt (memUpdate mem addr val) PTR_INP_VAL = memAt mem PTR_INP_VAL := by
  have hne : PTR_INP_VAL ≠ addr := by
    exact Ne.symm hneq
  simp [memUpdate, memAt, hne]

lemma memUpdate_eq_of_ne (mem : Memory) (addr val a : Nat) (hneq : a ≠ addr) :
    memAt (memUpdate mem addr val) a = memAt mem a := by
  simp [memUpdate, memAt, hneq]

def KernelSensitive (mem : Memory) : Prop :=
  ∀ i : Fin BATCH_SIZE,
    spec_kernel
        (memUpdate mem (memAt mem PTR_INP_VAL + i)
          (memAt mem (memAt mem PTR_INP_VAL + i) + 1)) i
      ≠ spec_kernel mem i

def OutputDiffers (mem : Memory) : Prop :=
  ∀ i : Fin BATCH_SIZE,
    spec_kernel mem i ≠ memAt mem (memAt mem PTR_INP_VAL + i)

def ValidInput (mem : Memory) : Prop :=
  MemSafeKernel mem ∧ KernelLayout mem ∧ KernelSensitive mem ∧ OutputDiffers mem
def UniformZeroKernel (mem : Memory) : Prop :=
  MemSafeKernel mem ∧
  memAt mem 0 = ROUNDS ∧
  memAt mem 1 = N_NODES ∧
  memAt mem 2 = BATCH_SIZE ∧
  memAt mem 3 = HEIGHT ∧
  KernelLayout mem ∧
  KernelDisjoint mem ∧
  (∀ k, k < N_NODES → memAt mem (memAt mem PTR_FOREST + k) = 0) ∧
  (∀ i : Fin BATCH_SIZE, memAt mem (memAt mem PTR_INP_IDX + i) = 0) ∧
  (∀ i : Fin BATCH_SIZE, memAt mem (memAt mem PTR_INP_VAL + i) = 0)

def AdversaryList (mem : Memory) (L : List Nat) : Prop :=
  List.Nodup L ∧
  (∀ addr ∈ L, AddrSafe mem addr) ∧
  (∀ addr ∈ L, ∃ i : Fin BATCH_SIZE,
    spec_kernel (memUpdate mem addr (memAt mem addr + 1)) i ≠ spec_kernel mem i)

def AdversaryK (mem : Memory) (k : Nat) : Prop :=
  ∃ L : List Nat, AdversaryList mem L ∧
    L.length = k * BATCH_SIZE * memAt mem 0


end ProofGlobalLowerBound
