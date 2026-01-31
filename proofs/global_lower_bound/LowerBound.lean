import Mathlib
import proofs.common.Base
import proofs.common.Machine

namespace ProofGlobalLowerBound
open ProofCommon
open ProofMachine

/--
Global lower-bound scaffold (Phase 1).

We keep the formal core arithmetic-only and leave semantic obligations as TODOs
in the accompanying markdown.
- `MIN_REQUIRED_WORDS` is a placeholder for the number of memory words that any
  correct program must read (to be proved via non-interference + adversarial
  input).
- The bounds below convert that word requirement into load-op and cycle lower
  bounds using ISA caps.
-/- 

def MIN_REQUIRED_WORDS : Nat := BATCH_SIZE

/-! ## Program model (Phase 1 scaffold) -/

def Memory : Type := Nat → Nat

/-! Output model (Phase 1): only the output values matter, fixed-size. -/
def Output : Type := Fin BATCH_SIZE → Nat

def PTR_INP_VAL : Nat := 6

def outputOf (base : Nat) (mem : Memory) : Output :=
  fun i => mem (base + i)

def AgreeOnList (xs : List Nat) (m1 m2 : Memory) : Prop :=
  ∀ a, a ∈ xs → m1 a = m2 a

/-! ### Load-op arithmetic helpers -/

def minLoadOps (words : Nat) : Nat := ceilDiv words VLEN

structure Program where
  program : List Instruction
  /-- Initial scratch contents. -/
  initScratch : Nat → Nat := fun _ => 0

def initCore (p : Program) : Core :=
  { id := 0, scratch := p.initScratch, trace_buf := [], pc := 0, state := .running }

def loadAddrs (s : Nat → Nat) (slot : LoadSlot) : List Nat :=
  match slot with
  | .load _ addr => [s addr]
  | .load_offset _ addr offset => [s (addr + offset)]
  | .vload _ addr =>
      let base := s addr
      (List.range VLEN).map (fun i => base + i)
  | .const _ _ => []

def execInstructionTrace (mem : Memory) (core : Core) (instr : Instruction) :
    ExecResult × List (List Nat) :=
  let reads := instr.load.map (loadAddrs core.scratch)
  let res := execInstruction false false (fun _ => 0) mem core instr
  (res, reads)

def runTraceAux : List Instruction → Memory → Core → (Memory × List (List Nat))
  | [], mem, _ => (mem, [])
  | instr :: rest, mem, core =>
      let (res, reads) := execInstructionTrace mem core instr
      let (mem', reads') := runTraceAux rest res.mem res.core
      (mem', reads ++ reads')

def runTrace (p : Program) (mem : Memory) : Memory × List (List Nat) :=
  runTraceAux p.program mem (initCore p)

def runMem (p : Program) (mem : Memory) : Memory :=
  (runTrace p mem).1

def readOps (p : Program) (mem : Memory) : List (List Nat) :=
  (runTrace p mem).2

def readWords (p : Program) (mem : Memory) : List Nat :=
  (readOps p mem).join

def readWordCount (p : Program) (mem : Memory) : Nat :=
  (readWords p mem).length

def loadOpCount (p : Program) (mem : Memory) : Nat :=
  (readOps p mem).length

def run (p : Program) (mem : Memory) : Output :=
  outputOf (mem PTR_INP_VAL) (runMem p mem)

def Correct (spec : Memory → Output) (p : Program) : Prop :=
  ∀ mem, run p mem = spec mem

/-! ### Trace-equivalence non-interference (straight-line programs) -/

lemma agreeOnList_append_left {xs ys : List Nat} {m1 m2 : Memory}
    (h : AgreeOnList (xs ++ ys) m1 m2) : AgreeOnList xs m1 m2 := by
  intro a ha
  exact h a (by simp [ha])

lemma agreeOnList_append_right {xs ys : List Nat} {m1 m2 : Memory}
    (h : AgreeOnList (xs ++ ys) m1 m2) : AgreeOnList ys m1 m2 := by
  intro a ha
  exact h a (by simp [ha])

lemma agreeOnList_of_join {ops : List (List Nat)} {m1 m2 : Memory}
    (h : AgreeOnList (List.join ops) m1 m2) :
    ∀ op ∈ ops, AgreeOnList op m1 m2 := by
  intro op hop
  induction ops with
  | nil =>
      simp at hop
  | cons op' ops ih =>
      simp at hop
      rcases hop with hop | hop
      · subst hop
        have h' : AgreeOnList (op' ++ List.join ops) m1 m2 := by
          simpa [List.join] using h
        exact agreeOnList_append_left h'
      ·
        have h' : AgreeOnList (List.join ops) m1 m2 := by
          have h'' : AgreeOnList (op' ++ List.join ops) m1 m2 := by
            simpa [List.join] using h
          exact agreeOnList_append_right h''
        exact ih h' _ hop

lemma execLoadSlot_eq_of_agree (s : Nat → Nat) (m1 m2 : Memory) (slot : LoadSlot)
    (h : AgreeOnList (loadAddrs s slot) m1 m2) :
    execLoadSlot s m1 slot = execLoadSlot s m2 slot := by
  cases slot with
  | load dest addr =>
      have h' : m1 (s addr) = m2 (s addr) := h _ (by simp [loadAddrs])
      simp [execLoadSlot, loadAddrs, h']
  | load_offset dest addr offset =>
      have h' : m1 (s (addr + offset)) = m2 (s (addr + offset)) := by
        exact h _ (by simp [loadAddrs])
      simp [execLoadSlot, loadAddrs, h']
  | vload dest addr =>
      let base := s addr
      apply List.map_congr_left
      intro i hi
      have hi' : base + i ∈ loadAddrs s (.vload dest addr) := by
        simp [loadAddrs, base, hi]
      have h' : m1 (base + i) = m2 (base + i) := h _ hi'
      simp [execLoadSlot, loadAddrs, vecWrites, base, h']
  | const dest val =>
      simp [execLoadSlot, loadAddrs]

lemma execInstructionTrace_eq_of_agree (mem1 mem2 : Memory) (core : Core)
    (instr : Instruction)
    (h : AgreeOnList (List.join (instr.load.map (loadAddrs core.scratch))) mem1 mem2) :
    execInstructionTrace mem1 core instr = execInstructionTrace mem2 core instr := by
  have hslots : ∀ slot ∈ instr.load, AgreeOnList (loadAddrs core.scratch slot) mem1 mem2 := by
    have := agreeOnList_of_join (m1:=mem1) (m2:=mem2) (ops:=instr.load.map (loadAddrs core.scratch)) h
    intro slot hslot
    have hmem : loadAddrs core.scratch slot ∈ instr.load.map (loadAddrs core.scratch) := by
      exact List.mem_map.2 ⟨slot, hslot, rfl⟩
    exact this _ hmem
  have hload :
      instr.load.bind (execLoadSlot core.scratch mem1) =
      instr.load.bind (execLoadSlot core.scratch mem2) := by
    induction instr.load with
    | nil =>
        simp
    | cons slot rest ih =>
        have hslot : AgreeOnList (loadAddrs core.scratch slot) mem1 mem2 :=
          hslots slot (by simp)
        have hslot_eq := execLoadSlot_eq_of_agree core.scratch mem1 mem2 slot hslot
        have hrest : ∀ s ∈ rest, AgreeOnList (loadAddrs core.scratch s) mem1 mem2 := by
          intro s hs
          exact hslots s (by simp [hs])
        have ih' : rest.bind (execLoadSlot core.scratch mem1) =
            rest.bind (execLoadSlot core.scratch mem2) := by
          exact ih
        simp [hslot_eq, ih']
  -- execInstruction depends on mem only through load_writes
  simp [execInstructionTrace, execInstruction, hload]

lemma runTraceAux_eq_of_agree :
    ∀ prog mem1 mem2 core,
      AgreeOnList (List.join (runTraceAux prog mem1 core).2) mem1 mem2 →
      runTraceAux prog mem1 core = runTraceAux prog mem2 core := by
  intro prog mem1 mem2 core
  induction prog with
  | nil =>
      intro h
      simp at h
      simp [runTraceAux]
  | cons instr rest ih =>
      intro h
      simp [runTraceAux] at h
      let res1 := execInstructionTrace mem1 core instr
      let res2 := execInstructionTrace mem2 core instr
      -- split agreement over current reads and remaining reads
      have hreads :
          AgreeOnList (List.join (instr.load.map (loadAddrs core.scratch))) mem1 mem2 := by
        have h' : AgreeOnList
            (List.join (instr.load.map (loadAddrs core.scratch)) ++
             List.join (runTraceAux rest res1.1.mem res1.1.core).2) mem1 mem2 := by
          simpa [runTraceAux, res1] using h
        exact agreeOnList_append_left h'
      have hrest :
          AgreeOnList
            (List.join (runTraceAux rest res1.1.mem res1.1.core).2) mem1 mem2 := by
        have h' : AgreeOnList
            (List.join (instr.load.map (loadAddrs core.scratch)) ++
             List.join (runTraceAux rest res1.1.mem res1.1.core).2) mem1 mem2 := by
          simpa [runTraceAux, res1] using h
        exact agreeOnList_append_right h'
      have hstep :
          res1 = res2 := by
        exact execInstructionTrace_eq_of_agree mem1 mem2 core instr hreads
      -- rewrite with equal step, then apply IH
      have ih' : runTraceAux rest res1.1.mem res1.1.core =
          runTraceAux rest res2.1.mem res2.1.core := by
        have hrest' : AgreeOnList (List.join (runTraceAux rest res2.1.mem res2.1.core).2) mem1 mem2 := by
          simpa [hstep] using hrest
        exact ih _ _ _ hrest'
      simp [runTraceAux, res1, res2, hstep, ih']

lemma run_eq_of_agree (p : Program) (mem1 mem2 : Memory)
    (h : AgreeOnList (readWords p mem1) mem1 mem2) :
    run p mem1 = run p mem2 := by
  have htrace : runTrace p mem1 = runTrace p mem2 := by
    have := runTraceAux_eq_of_agree p.program mem1 mem2 (initCore p)
    simpa [runTrace, readWords, readOps] using this h
  simp [run, runMem, htrace]

/-! ### Adversarial input lemma for values-slice spec -/

def spec_values (mem : Memory) : Output :=
  outputOf (mem PTR_INP_VAL) mem

def memUpdate (mem : Memory) (addr val : Nat) : Memory :=
  fun a => if a = addr then val else mem a

lemma spec_values_diff {mem : Memory} {base : Nat} {i : Fin BATCH_SIZE} :
    let addr := base + i
    spec_values (memUpdate mem addr (mem addr + 1)) i ≠ spec_values mem i := by
  intro addr
  simp [spec_values, outputOf, memUpdate, addr]

lemma must_read_values (p : Program) (hstraight : StraightLine p) (hcorrect : Correct spec_values p) :
    ∀ mem, ∀ i : Fin BATCH_SIZE,
      (mem (mem PTR_INP_VAL + i)) ∈ readWords p mem := by
  intro mem i
  by_contra hnot
  have hagree : AgreeOnList (readWords p mem) mem
      (memUpdate mem (mem PTR_INP_VAL + i) (mem (mem PTR_INP_VAL + i) + 1)) := by
    intro a ha
    have hne : a ≠ mem PTR_INP_VAL + i := by
      intro hEq
      apply hnot
      simpa [hEq] using ha
    simp [memUpdate, hne]
  have hrun :
      run p mem =
      run p (memUpdate mem (mem PTR_INP_VAL + i) (mem (mem PTR_INP_VAL + i) + 1)) := by
    exact run_eq_of_agree p mem
      (memUpdate mem (mem PTR_INP_VAL + i) (mem (mem PTR_INP_VAL + i) + 1)) hagree
  have hspec :
      spec_values mem =
      spec_values (memUpdate mem (mem PTR_INP_VAL + i) (mem (mem PTR_INP_VAL + i) + 1)) := by
    calc
      spec_values mem = run p mem := by symm; exact hcorrect mem
      _ = run p (memUpdate mem (mem PTR_INP_VAL + i) (mem (mem PTR_INP_VAL + i) + 1)) := hrun
      _ = spec_values (memUpdate mem (mem PTR_INP_VAL + i) (mem (mem PTR_INP_VAL + i) + 1)) := by
        exact hcorrect _
  have hdiff := spec_values_diff (mem:=mem) (base:=mem PTR_INP_VAL) (i:=i)
  exact hdiff (by simpa using congrArg (fun f => f i) hspec)

def outputAddrs (mem : Memory) : Finset Nat :=
  (Finset.univ.image (fun i : Fin BATCH_SIZE => mem PTR_INP_VAL + i))

lemma outputAddrs_card (mem : Memory) : (outputAddrs mem).card = BATCH_SIZE := by
  classical
  have hinj : Function.Injective (fun i : Fin BATCH_SIZE => mem PTR_INP_VAL + i) := by
    intro a b h
    apply Fin.ext
    exact Nat.add_left_cancel h
  simpa [outputAddrs] using
    (Finset.card_image_of_injective (s:=Finset.univ) hinj)

lemma outputAddrs_subset_readWords (p : Program) (hstraight : StraightLine p)
    (hcorrect : Correct spec_values p) (mem : Memory) :
    outputAddrs mem ⊆ (readWords p mem).toFinset := by
  classical
  intro a ha
  rcases Finset.mem_image.mp (by simpa [outputAddrs] using ha) with ⟨i, hi, hEq⟩
  have hread : mem (mem PTR_INP_VAL + i) ∈ readWords p mem :=
    must_read_values p hstraight hcorrect mem i
  have : a ∈ readWords p mem := by simpa [hEq] using hread
  exact List.mem_toFinset.mpr this

lemma min_required_words_values (p : Program) (hstraight : StraightLine p)
    (hcorrect : Correct spec_values p) :
    ∀ mem, BATCH_SIZE ≤ readWordCount p mem := by
  intro mem
  have hsubset : outputAddrs mem ⊆ (readWords p mem).toFinset :=
    outputAddrs_subset_readWords p hstraight hcorrect mem
  have hcard_le : (outputAddrs mem).card ≤ (readWords p mem).toFinset.card :=
    Finset.card_le_card hsubset
  have hlen : (readWords p mem).toFinset.card ≤ (readWords p mem).length :=
    List.toFinset_card_le
  have hcard : (outputAddrs mem).card = BATCH_SIZE := outputAddrs_card mem
  have : BATCH_SIZE ≤ (readWords p mem).length := by
    exact le_trans (by simpa [hcard] using hcard_le) hlen
  simpa [readWordCount] using this
/-! ### Straight-line program predicate -/

def flowSlotStraight : FlowSlot → Prop
  | .select _ _ _ _ => True
  | .add_imm _ _ _ => True
  | .vselect _ _ _ _ => True
  | .trace_write _ => True
  | .coreid _ => True
  | .halt => False
  | .pause => False
  | .cond_jump _ _ => False
  | .cond_jump_rel _ _ => False
  | .jump _ => False
  | .jump_indirect _ => False

def instrStraight (i : Instruction) : Prop :=
  i.flow.all (fun s => flowSlotStraight s)

def StraightLine (p : Program) : Prop :=
  ∀ instr ∈ p.program, instrStraight instr

/-! ### Derived load-op lower bound from readOps_bound -/

lemma loadAddrs_length_le (s : Nat → Nat) (slot : LoadSlot) :
    (loadAddrs s slot).length ≤ VLEN := by
  cases slot <;> simp [loadAddrs, VLEN]

lemma readOps_bound_aux :
    ∀ prog mem core, ∀ op ∈ (runTraceAux prog mem core).2, op.length ≤ VLEN := by
  intro prog mem core
  induction prog with
  | nil =>
      intro op hmem
      simp at hmem
  | cons instr rest ih =>
      intro op hop
      simp [runTraceAux] at hop
      rcases hop with hop | hop
      · -- op is from current instruction
        rcases hop with ⟨slot, hslot, rfl⟩
        exact loadAddrs_length_le _ _
      · -- op is from remaining program
        exact ih _ _ _ op hop

lemma readOps_bound (p : Program) (mem : Memory) :
    ∀ op ∈ readOps p mem, op.length ≤ VLEN := by
  simpa [readOps, runTrace] using (readOps_bound_aux p.program mem (initCore p))

lemma length_join_le (ops : List (List Nat))
    (h : ∀ op ∈ ops, op.length ≤ VLEN) :
    (List.join ops).length ≤ VLEN * ops.length := by
  induction ops with
  | nil =>
      simp
  | cons op ops ih =>
      have hop : op.length ≤ VLEN := h op (by simp)
      have hrest : ∀ o ∈ ops, o.length ≤ VLEN := by
        intro o ho
        exact h o (by simp [ho])
      have ih' := ih hrest
      calc
        (List.join (op :: ops)).length = op.length + (List.join ops).length := by simp
        _ ≤ VLEN + VLEN * ops.length := by
          exact Nat.add_le_add hop ih'
        _ = VLEN * (ops.length + 1) := by
          simp [Nat.mul_add, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
        _ = VLEN * (List.length (op :: ops)) := by simp

lemma ceilDiv_le_of_mul_le {n k d : Nat} (hd : 0 < d) (h : n ≤ d * k) :
    ceilDiv n d ≤ k := by
  unfold ceilDiv
  have h' : n + d - 1 ≤ d * k + (d - 1) := by
    exact Nat.add_le_add_right h (d - 1)
  -- `Nat.div_le_iff_le_mul_add_pred` : a / d ≤ k ↔ a ≤ d*k + (d-1)
  have hdiv : (n + d - 1) / d ≤ k :=
    (Nat.div_le_iff_le_mul_add_pred hd).2 h'
  exact hdiv

lemma loadOps_lower_bound (p : Program) (mem : Memory) :
    minLoadOps (readWordCount p mem) ≤ loadOpCount p mem := by
  have hlen : (readWords p mem).length ≤ VLEN * (loadOpCount p mem) := by
    have := length_join_le (readOps p mem) (readOps_bound p mem)
    simpa [readWords, loadOpCount] using this
  exact ceilDiv_le_of_mul_le (by decide : 0 < VLEN) hlen

lemma ceilDiv_mono {a b d : Nat} (h : a ≤ b) :
    ceilDiv a d ≤ ceilDiv b d := by
  unfold ceilDiv
  have h' : a + d - 1 ≤ b + d - 1 := by
    exact Nat.add_le_add_right h (d - 1)
  exact Nat.div_le_div_right h' d

lemma minLoadOps_mono {a b : Nat} (h : a ≤ b) :
    minLoadOps a ≤ minLoadOps b := by
  exact ceilDiv_mono h

lemma loadLowerCycles_mono {a b : Nat} (h : a ≤ b) :
    loadLowerCycles a ≤ loadLowerCycles b := by
  exact ceilDiv_mono (minLoadOps_mono h)

/-- Lower bound on cycles implied by the load engine capacity. -/
def loadLowerCycles (words : Nat) : Nat := ceilDiv (minLoadOps words) LOAD_CAP

/-- Global lower bound (currently load-only). -/
def globalLowerBound : Nat := loadLowerCycles MIN_REQUIRED_WORDS

lemma globalLowerBound_eq :
    globalLowerBound = ceilDiv (ceilDiv MIN_REQUIRED_WORDS VLEN) LOAD_CAP := by
  rfl

theorem global_load_lower_bound (p : Program) (hstraight : StraightLine p)
    (hcorrect : Correct spec_values p) :
    ∀ mem, globalLowerBound ≤ loadLowerCycles (readWordCount p mem) := by
  intro mem
  have hmin : MIN_REQUIRED_WORDS ≤ readWordCount p mem := by
    simpa [MIN_REQUIRED_WORDS] using min_required_words_values p hstraight hcorrect mem
  exact loadLowerCycles_mono hmin

end ProofGlobalLowerBound
