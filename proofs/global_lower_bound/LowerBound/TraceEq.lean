import proofs.global_lower_bound.LowerBound.Defs

namespace ProofGlobalLowerBound
open ProofCommon
open ProofMachine
open ProofISA

/-! ### Trace-equivalence non-interference (straight-line programs) -/

lemma agreeOnList_append_left {xs ys : List Nat} {m1 m2 : Memory}
    (h : AgreeOnList (xs ++ ys) m1 m2) : AgreeOnList xs m1 m2 := by
  refine ⟨h.1, ?_⟩
  intro a ha
  exact h.2 a (by simp [ha])

lemma agreeOnList_append_right {xs ys : List Nat} {m1 m2 : Memory}
    (h : AgreeOnList (xs ++ ys) m1 m2) : AgreeOnList ys m1 m2 := by
  refine ⟨h.1, ?_⟩
  intro a ha
  exact h.2 a (by simp [ha])

lemma agreeOnList_of_join {ops : List (List Nat)} {m1 m2 : Memory}
    (h : AgreeOnList (listJoin ops) m1 m2) :
    ∀ op ∈ ops, AgreeOnList op m1 m2 := by
  intro op hop
  refine ⟨h.1, ?_⟩
  intro a ha
  apply h.2 a
  -- a ∈ listJoin ops via mem_flatMap
  exact List.mem_flatMap.mpr ⟨op, hop, ha⟩

lemma memRead_eq_of_agree (m1 m2 : Memory) (addr : Nat)
    (hsize : m1.size = m2.size) (hval : memAt m1 addr = memAt m2 addr) :
    memRead m1 addr = memRead m2 addr := by
  by_cases h : addr < m1.size
  · have h' : addr < m2.size := by simpa [hsize] using h
    have hval' : m1.data addr = m2.data addr := by simpa [memAt] using hval
    simp [memRead, h, h', hval']
  · have h' : ¬ addr < m2.size := by simpa [hsize] using h
    simp [memRead, h, h']

lemma execLoadSlot_eq_of_agree (s : Nat → Nat) (m1 m2 : Memory) (slot : LoadSlot)
    (h : AgreeOnList (loadAddrs s slot) m1 m2) :
    execLoadSlot s m1 slot = execLoadSlot s m2 slot := by
  cases slot with
  | load dest addr =>
      have h' : memAt m1 (s addr) = memAt m2 (s addr) := h.2 _ (by simp [loadAddrs])
      have hread := memRead_eq_of_agree m1 m2 (s addr) h.1 h'
      simp [execLoadSlot, hread]
  | load_offset dest addr offset =>
      have h' : memAt m1 (s (addr + offset)) = memAt m2 (s (addr + offset)) := by
        exact h.2 _ (by simp [loadAddrs])
      have hread := memRead_eq_of_agree m1 m2 (s (addr + offset)) h.1 h'
      simp [execLoadSlot, hread]
  | vload dest addr =>
      let base := s addr
      have hread : ∀ i, i < VLEN → memRead m1 (base + i) = memRead m2 (base + i) := by
        intro i hi
        have hi' : base + i ∈ loadAddrs s (.vload dest addr) := by
          simp [loadAddrs, base, hi]
        have hval : memAt m1 (base + i) = memAt m2 (base + i) := h.2 _ hi'
        exact memRead_eq_of_agree m1 m2 (base + i) h.1 hval
      have hvals :
          (List.range VLEN).map (fun i => memRead m1 (base + i)) =
          (List.range VLEN).map (fun i => memRead m2 (base + i)) := by
        apply List.map_congr_left
        intro i hi
        have hi' : i < VLEN := by simpa using hi
        exact hread i hi'
      have hreads :
          (List.range VLEN).map (fun i => (dest + i, (memRead m1 (base + i)).get!)) =
          (List.range VLEN).map (fun i => (dest + i, (memRead m2 (base + i)).get!)) := by
        apply List.map_congr_left
        intro i hi
        have hi' : i < VLEN := by simpa using hi
        have := hread i hi'
        simp [this]
      simp [execLoadSlot, base, hvals, hreads]
  | const dest val =>
      simp [execLoadSlot]

lemma execLoadSlots_eq_of_agree (s : Nat → Nat) (m1 m2 : Memory) (slots : List LoadSlot)
    (h : AgreeOnList (listJoin (slots.map (loadAddrs s))) m1 m2) :
    slots.foldl
        (fun acc slot =>
          match acc, execLoadSlot s m1 slot with
          | some ws, some ws' => some (ws ++ ws')
          | _, _ => none)
        (some []) =
    slots.foldl
        (fun acc slot =>
          match acc, execLoadSlot s m2 slot with
          | some ws, some ws' => some (ws ++ ws')
          | _, _ => none)
        (some []) := by
  -- Strengthen the induction hypothesis to allow an arbitrary accumulator.
  have aux :
      ∀ (slots : List LoadSlot),
        AgreeOnList (listJoin (slots.map (loadAddrs s))) m1 m2 →
          ∀ acc,
            slots.foldl
                (fun acc slot =>
                  match acc, execLoadSlot s m1 slot with
                  | some ws, some ws' => some (ws ++ ws')
                  | _, _ => none)
                acc =
              slots.foldl
                (fun acc slot =>
                  match acc, execLoadSlot s m2 slot with
                  | some ws, some ws' => some (ws ++ ws')
                  | _, _ => none)
                acc := by
    intro slots
    induction slots with
    | nil =>
        intro _h acc
        simp
    | cons slot rest ih =>
        intro h acc
        have hslot : AgreeOnList (loadAddrs s slot) m1 m2 := by
          have := agreeOnList_append_left (xs := loadAddrs s slot)
              (ys := listJoin (rest.map (loadAddrs s))) (m1 := m1) (m2 := m2)
          -- listJoin (slot :: rest) = loadAddrs slot ++ listJoin rest
          have h' : AgreeOnList (loadAddrs s slot ++ listJoin (rest.map (loadAddrs s))) m1 m2 := by
            simpa [listJoin] using h
          exact this h'
        have hrest : AgreeOnList (listJoin (rest.map (loadAddrs s))) m1 m2 := by
          have := agreeOnList_append_right (xs := loadAddrs s slot)
              (ys := listJoin (rest.map (loadAddrs s))) (m1 := m1) (m2 := m2)
          have h' : AgreeOnList (loadAddrs s slot ++ listJoin (rest.map (loadAddrs s))) m1 m2 := by
            simpa [listJoin] using h
          exact this h'
        have hslot_eq := execLoadSlot_eq_of_agree s m1 m2 slot hslot
        -- After rewriting `execLoadSlot` on the head slot, both folds start from the same accumulator.
        simp [List.foldl, hslot_eq]
        exact ih hrest _
  exact aux slots h (some [])

lemma execInstructionTrace_ok_core_eq_of_agree (mem1 mem2 : Memory) (core : Core) (instr : Instruction)
    (h : AgreeOnList (listJoin (instr.load.map (loadAddrs core.scratch))) mem1 mem2) :
    let r1 := execInstructionTrace mem1 core instr
    let r2 := execInstructionTrace mem2 core instr
    r1.1.ok = r2.1.ok ∧ r1.1.core = r2.1.core := by
  unfold execInstructionTrace
  by_cases hWF : instrWellFormed instr
  · have hsize : mem1.size = mem2.size := h.1
    have hload :
        instr.load.foldl
            (fun acc slot =>
              match acc, execLoadSlot core.scratch mem1 slot with
              | some ws, some ws' => some (ws ++ ws')
              | _, _ => none)
            (some []) =
          instr.load.foldl
            (fun acc slot =>
              match acc, execLoadSlot core.scratch mem2 slot with
              | some ws, some ws' => some (ws ++ ws')
              | _, _ => none)
            (some []) := execLoadSlots_eq_of_agree core.scratch mem1 mem2 instr.load h
    cases hvalu : execValuSlots core.scratch instr.valu with
    | none =>
        simp [execInstruction, hWF, hvalu]
    | some valu_writes =>
        cases halu : execAluSlots core.scratch instr.alu with
        | none =>
            simp [execInstruction, hWF, hvalu, halu]
        | some alu_writes =>
            -- load-writes fold
            cases hload1 :
                (instr.load.foldl
                  (fun acc slot =>
                    match acc, execLoadSlot core.scratch mem1 slot with
                    | some ws, some ws' => some (ws ++ ws')
                    | _, _ => none)
                  (some [])) with
            | none =>
                have hload2 :
                    instr.load.foldl
                        (fun acc slot =>
                          match acc, execLoadSlot core.scratch mem2 slot with
                          | some ws, some ws' => some (ws ++ ws')
                          | _, _ => none)
                        (some []) = none := by
                  simpa [hload] using hload1
                -- Both executions fail in the load fold, so res = ok_false on both sides.
                have hres1 :
                    execInstruction false false (fun _ => 0) mem1 core instr =
                      { core := core, mem := mem1, ok := false, debug_ok := true,
                        has_non_debug := instrHasNonDebug instr } := by
                  unfold execInstruction
                  simp (config := { zeta := true }) [hWF, hvalu, halu]
                  -- Push `hload1` through the surrounding `match` via `congrArg`.
                  let f : Option (List (Nat × Nat)) → ExecResult := fun load_writes? =>
                    match load_writes? with
                    | none =>
                        { core := core, mem := mem1, ok := false, debug_ok := true,
                          has_non_debug := instrHasNonDebug instr }
                    | some load_writes =>
                        match memWriteMany mem1 (List.flatMap (execStoreSlot core.scratch) instr.store) with
                        | none =>
                            { core := core, mem := mem1, ok := false, debug_ok := true,
                              has_non_debug := instrHasNonDebug instr }
                        | some mem' =>
                            let (core', flow_writes) :=
                              instr.flow.foldl
                                (fun acc slot =>
                                  let (c, ws) := acc
                                  let (c', ws') := execFlowSlot false c core.scratch slot
                                  (c', ws ++ ws'))
                                (core, [])
                            let scratch' :=
                              writeMany core.scratch
                                (valu_writes ++ alu_writes ++ flow_writes ++ load_writes)
                            let core'' := { core' with scratch := scratch' }
                            { core := core'', mem := mem', ok := true, debug_ok := true,
                              has_non_debug := instrHasNonDebug instr }
                  simpa (config := { zeta := true }) [f] using congrArg f hload1
                have hres2 :
                    execInstruction false false (fun _ => 0) mem2 core instr =
                      { core := core, mem := mem2, ok := false, debug_ok := true,
                        has_non_debug := instrHasNonDebug instr } := by
                  unfold execInstruction
                  simp (config := { zeta := true }) [hWF, hvalu, halu]
                  let f : Option (List (Nat × Nat)) → ExecResult := fun load_writes? =>
                    match load_writes? with
                    | none =>
                        { core := core, mem := mem2, ok := false, debug_ok := true,
                          has_non_debug := instrHasNonDebug instr }
                    | some load_writes =>
                        match memWriteMany mem2 (List.flatMap (execStoreSlot core.scratch) instr.store) with
                        | none =>
                            { core := core, mem := mem2, ok := false, debug_ok := true,
                              has_non_debug := instrHasNonDebug instr }
                        | some mem' =>
                            let (core', flow_writes) :=
                              instr.flow.foldl
                                (fun acc slot =>
                                  let (c, ws) := acc
                                  let (c', ws') := execFlowSlot false c core.scratch slot
                                  (c', ws ++ ws'))
                                (core, [])
                            let scratch' :=
                              writeMany core.scratch
                                (valu_writes ++ alu_writes ++ flow_writes ++ load_writes)
                            let core'' := { core' with scratch := scratch' }
                            { core := core'', mem := mem', ok := true, debug_ok := true,
                              has_non_debug := instrHasNonDebug instr }
                  simpa (config := { zeta := true }) [f] using congrArg f hload2
                refine ⟨?_, ?_⟩
                · simpa [hres1, hres2]
                · simpa [hres1, hres2]
            | some load_writes =>
                have hload2 :
                    instr.load.foldl
                        (fun acc slot =>
                          match acc, execLoadSlot core.scratch mem2 slot with
                          | some ws, some ws' => some (ws ++ ws')
                          | _, _ => none)
                        (some []) = some load_writes := by
                  simpa [hload] using hload1
                let store_writes := instr.store.flatMap (execStoreSlot core.scratch)
                cases hmw1 : memWriteMany mem1 store_writes with
                  | none =>
                      -- memWriteMany succeeds/fails only based on bounds, so equal-sized memories agree on isSome.
                      have hisSome :
                          (memWriteMany mem1 store_writes).isSome =
                            (memWriteMany mem2 store_writes).isSome :=
                        memWriteMany_ok_eq mem1 mem2 store_writes hsize
                      have hmw2 : memWriteMany mem2 store_writes = none := by
                        -- If mem1 fails, mem2 must also fail (otherwise isSome would differ).
                        have hIsSome2 : (memWriteMany mem2 store_writes).isSome = false := by
                          have : false = (memWriteMany mem2 store_writes).isSome := by
                            simpa [hmw1] using hisSome
                          simpa using this.symm
                        cases h2 : memWriteMany mem2 store_writes with
                        | none => simpa [h2]
                        | some mem2' =>
                            have : (some mem2').isSome = false := by
                              simpa [h2] using hIsSome2
                            simp at this
                      have hres1 :
                          execInstruction false false (fun _ => 0) mem1 core instr =
                            { core := core, mem := mem1, ok := false, debug_ok := true,
                              has_non_debug := instrHasNonDebug instr } := by
                        have hmw1' :
                            memWriteMany mem1 (instr.store.flatMap (execStoreSlot core.scratch)) = none := by
                          simpa [store_writes] using hmw1
                        unfold execInstruction
                        simp (config := { zeta := true }) [hWF, hvalu, halu]
                        let f : Option (List (Nat × Nat)) → ExecResult := fun load_writes? =>
                          match load_writes? with
                          | none =>
                              { core := core, mem := mem1, ok := false, debug_ok := true,
                                has_non_debug := instrHasNonDebug instr }
                          | some load_writes =>
                              match memWriteMany mem1 (List.flatMap (execStoreSlot core.scratch) instr.store) with
                              | none =>
                                  { core := core, mem := mem1, ok := false, debug_ok := true,
                                    has_non_debug := instrHasNonDebug instr }
                              | some mem' =>
                                  let (core', flow_writes) :=
                                    instr.flow.foldl
                                      (fun acc slot =>
                                        let (c, ws) := acc
                                        let (c', ws') := execFlowSlot false c core.scratch slot
                                        (c', ws ++ ws'))
                                      (core, [])
                                  let scratch' :=
                                    writeMany core.scratch
                                      (valu_writes ++ alu_writes ++ flow_writes ++ load_writes)
                                  let core'' := { core' with scratch := scratch' }
                                  { core := core'', mem := mem', ok := true, debug_ok := true,
                                    has_non_debug := instrHasNonDebug instr }
                        simpa (config := { zeta := true }) [f, hmw1'] using congrArg f hload1
                      have hres2 :
                          execInstruction false false (fun _ => 0) mem2 core instr =
                            { core := core, mem := mem2, ok := false, debug_ok := true,
                              has_non_debug := instrHasNonDebug instr } := by
                        have hmw2' :
                            memWriteMany mem2 (instr.store.flatMap (execStoreSlot core.scratch)) = none := by
                          simpa [store_writes] using hmw2
                        unfold execInstruction
                        simp (config := { zeta := true }) [hWF, hvalu, halu]
                        let f : Option (List (Nat × Nat)) → ExecResult := fun load_writes? =>
                          match load_writes? with
                          | none =>
                              { core := core, mem := mem2, ok := false, debug_ok := true,
                                has_non_debug := instrHasNonDebug instr }
                          | some load_writes =>
                              match memWriteMany mem2 (List.flatMap (execStoreSlot core.scratch) instr.store) with
                              | none =>
                                  { core := core, mem := mem2, ok := false, debug_ok := true,
                                    has_non_debug := instrHasNonDebug instr }
                              | some mem' =>
                                  let (core', flow_writes) :=
                                    instr.flow.foldl
                                      (fun acc slot =>
                                        let (c, ws) := acc
                                        let (c', ws') := execFlowSlot false c core.scratch slot
                                        (c', ws ++ ws'))
                                      (core, [])
                                  let scratch' :=
                                    writeMany core.scratch
                                      (valu_writes ++ alu_writes ++ flow_writes ++ load_writes)
                                  let core'' := { core' with scratch := scratch' }
                                  { core := core'', mem := mem', ok := true, debug_ok := true,
                                    has_non_debug := instrHasNonDebug instr }
                        simpa (config := { zeta := true }) [f, hmw2'] using congrArg f hload2
                      refine ⟨?_, ?_⟩
                      · simpa [hres1, hres2]
                      · simpa [hres1, hres2]
                  | some mem1' =>
                    -- if memWriteMany succeeds on mem1, it must succeed on mem2
                    cases hmw2 : memWriteMany mem2 store_writes with
                    | none =>
                        have hsome : (memWriteMany mem1 store_writes).isSome =
                            (memWriteMany mem2 store_writes).isSome :=
                          memWriteMany_ok_eq mem1 mem2 store_writes hsize
                        have : False := by simpa [hmw1, hmw2] using hsome
                        exact False.elim this
                    | some mem2' =>
                        -- ok=true branch: ok matches and core depends only on scratch and the writes lists
                        have hmw1' :
                            memWriteMany mem1 (instr.store.flatMap (execStoreSlot core.scratch)) =
                              some mem1' := by
                          simpa [store_writes] using hmw1
                        have hmw2' :
                            memWriteMany mem2 (instr.store.flatMap (execStoreSlot core.scratch)) =
                              some mem2' := by
                          simpa [store_writes] using hmw2
                        refine ⟨?_, ?_⟩
                        ·
                          -- Reduce the goal to an equality of `execInstruction` results.
                          simp (config := { zeta := true })
                          have hok1 :
                              (execInstruction false false (fun _ => 0) mem1 core instr).ok = true := by
                            unfold execInstruction
                            simp (config := { zeta := true }) [hWF, hvalu, halu]
                            let f : Option (List (Nat × Nat)) → ExecResult := fun load_writes? =>
                              match load_writes? with
                              | none =>
                                  { core := core, mem := mem1, ok := false, debug_ok := true,
                                    has_non_debug := instrHasNonDebug instr }
                              | some load_writes =>
                                  match memWriteMany mem1
                                      (List.flatMap (execStoreSlot core.scratch) instr.store) with
                                  | none =>
                                      { core := core, mem := mem1, ok := false, debug_ok := true,
                                        has_non_debug := instrHasNonDebug instr }
                                  | some mem' =>
                                      let (core', flow_writes) :=
                                        instr.flow.foldl
                                          (fun acc slot =>
                                            let (c, ws) := acc
                                            let (c', ws') := execFlowSlot false c core.scratch slot
                                            (c', ws ++ ws'))
                                          (core, [])
                                      let scratch' :=
                                        writeMany core.scratch
                                          (valu_writes ++ alu_writes ++ flow_writes ++ load_writes)
                                      let core'' := { core' with scratch := scratch' }
                                      { core := core'', mem := mem', ok := true, debug_ok := true,
                                        has_non_debug := instrHasNonDebug instr }
                            let f_ok : Option (List (Nat × Nat)) → Bool :=
                              fun load_writes? => (f load_writes?).ok
                            simpa (config := { zeta := true }) [f_ok, f, hmw1'] using congrArg f_ok hload1
                          have hok2 :
                              (execInstruction false false (fun _ => 0) mem2 core instr).ok = true := by
                            unfold execInstruction
                            simp (config := { zeta := true }) [hWF, hvalu, halu]
                            let f : Option (List (Nat × Nat)) → ExecResult := fun load_writes? =>
                              match load_writes? with
                              | none =>
                                  { core := core, mem := mem2, ok := false, debug_ok := true,
                                    has_non_debug := instrHasNonDebug instr }
                              | some load_writes =>
                                  match memWriteMany mem2
                                      (List.flatMap (execStoreSlot core.scratch) instr.store) with
                                  | none =>
                                      { core := core, mem := mem2, ok := false, debug_ok := true,
                                        has_non_debug := instrHasNonDebug instr }
                                  | some mem' =>
                                      let (core', flow_writes) :=
                                        instr.flow.foldl
                                          (fun acc slot =>
                                            let (c, ws) := acc
                                            let (c', ws') := execFlowSlot false c core.scratch slot
                                            (c', ws ++ ws'))
                                          (core, [])
                                      let scratch' :=
                                        writeMany core.scratch
                                          (valu_writes ++ alu_writes ++ flow_writes ++ load_writes)
                                      let core'' := { core' with scratch := scratch' }
                                      { core := core'', mem := mem', ok := true, debug_ok := true,
                                        has_non_debug := instrHasNonDebug instr }
                            let f_ok : Option (List (Nat × Nat)) → Bool :=
                              fun load_writes? => (f load_writes?).ok
                            simpa (config := { zeta := true }) [f_ok, f, hmw2'] using congrArg f_ok hload2
                          calc
                            (execInstruction false false (fun _ => 0) mem1 core instr).ok = true := hok1
                            _ = (execInstruction false false (fun _ => 0) mem2 core instr).ok := by
                              symm; exact hok2
                        ·
                          simp (config := { zeta := true })
                          let coreOut : Core :=
                            let (core', flow_writes) :=
                              instr.flow.foldl
                                (fun acc slot =>
                                  let (c, ws) := acc
                                  let (c', ws') := execFlowSlot false c core.scratch slot
                                  (c', ws ++ ws'))
                                (core, [])
                            let scratch' :=
                              writeMany core.scratch
                                (valu_writes ++ alu_writes ++ flow_writes ++ load_writes)
                            { core' with scratch := scratch' }
                          have hcore1 :
                              (execInstruction false false (fun _ => 0) mem1 core instr).core = coreOut := by
                            unfold execInstruction
                            simp (config := { zeta := true }) [hWF, hvalu, halu]
                            let f : Option (List (Nat × Nat)) → ExecResult := fun load_writes? =>
                              match load_writes? with
                              | none =>
                                  { core := core, mem := mem1, ok := false, debug_ok := true,
                                    has_non_debug := instrHasNonDebug instr }
                              | some load_writes =>
                                  match memWriteMany mem1
                                      (List.flatMap (execStoreSlot core.scratch) instr.store) with
                                  | none =>
                                      { core := core, mem := mem1, ok := false, debug_ok := true,
                                        has_non_debug := instrHasNonDebug instr }
                                  | some mem' =>
                                      let (core', flow_writes) :=
                                        instr.flow.foldl
                                          (fun acc slot =>
                                            let (c, ws) := acc
                                            let (c', ws') := execFlowSlot false c core.scratch slot
                                            (c', ws ++ ws'))
                                          (core, [])
                                      let scratch' :=
                                        writeMany core.scratch
                                          (valu_writes ++ alu_writes ++ flow_writes ++ load_writes)
                                      let core'' := { core' with scratch := scratch' }
                                      { core := core'', mem := mem', ok := true, debug_ok := true,
                                        has_non_debug := instrHasNonDebug instr }
                            let f_core : Option (List (Nat × Nat)) → Core :=
                              fun load_writes? => (f load_writes?).core
                            simpa (config := { zeta := true }) [f_core, f, coreOut, hmw1'] using
                              congrArg f_core hload1
                          have hcore2 :
                              (execInstruction false false (fun _ => 0) mem2 core instr).core = coreOut := by
                            unfold execInstruction
                            simp (config := { zeta := true }) [hWF, hvalu, halu]
                            let f : Option (List (Nat × Nat)) → ExecResult := fun load_writes? =>
                              match load_writes? with
                              | none =>
                                  { core := core, mem := mem2, ok := false, debug_ok := true,
                                    has_non_debug := instrHasNonDebug instr }
                              | some load_writes =>
                                  match memWriteMany mem2
                                      (List.flatMap (execStoreSlot core.scratch) instr.store) with
                                  | none =>
                                      { core := core, mem := mem2, ok := false, debug_ok := true,
                                        has_non_debug := instrHasNonDebug instr }
                                  | some mem' =>
                                      let (core', flow_writes) :=
                                        instr.flow.foldl
                                          (fun acc slot =>
                                            let (c, ws) := acc
                                            let (c', ws') := execFlowSlot false c core.scratch slot
                                            (c', ws ++ ws'))
                                          (core, [])
                                      let scratch' :=
                                        writeMany core.scratch
                                          (valu_writes ++ alu_writes ++ flow_writes ++ load_writes)
                                      let core'' := { core' with scratch := scratch' }
                                      { core := core'', mem := mem', ok := true, debug_ok := true,
                                        has_non_debug := instrHasNonDebug instr }
                            let f_core : Option (List (Nat × Nat)) → Core :=
                              fun load_writes? => (f load_writes?).core
                            simpa (config := { zeta := true }) [f_core, f, coreOut, hmw2'] using
                              congrArg f_core hload2
                          calc
                            (execInstruction false false (fun _ => 0) mem1 core instr).core = coreOut := hcore1
                            _ = (execInstruction false false (fun _ => 0) mem2 core instr).core := by
                              symm; exact hcore2
  ·
    have hdec : decide (instrWellFormed instr) = false := by
      exact (decide_eq_false_iff_not).2 hWF
    -- In the ill-formed case, execInstruction bails out before touching mem.
    simp [execInstruction, hdec]

lemma runTraceAuxRW_writeAddrs_eq_of_agree :
    ∀ prog mem1 mem2 core,
      AgreeOnList (listJoin (runTraceAux prog mem1 core).2) mem1 mem2 →
      SafeExecAux prog mem1 core →
      SafeExecAux prog mem2 core →
      listJoin
          ((runTraceAuxRW prog mem1 core).2.2.map (fun ws => ws.map Prod.fst)) =
        listJoin
          ((runTraceAuxRW prog mem2 core).2.2.map (fun ws => ws.map Prod.fst)) := by
  intro prog
  induction prog with
  | nil =>
      intro mem1 mem2 core hagree hsafe1 hsafe2
      simp [runTraceAuxRW]
  | cons instr rest ih =>
      intro mem1 mem2 core hagree hsafe1 hsafe2
      have hsafe1' :
          (execInstructionTrace mem1 core instr).1.ok = true ∧
            SafeExecAux rest (execInstructionTrace mem1 core instr).1.mem
              (execInstructionTrace mem1 core instr).1.core := by
        simpa [SafeExecAux] using hsafe1
      have hsafe2' :
          (execInstructionTrace mem2 core instr).1.ok = true ∧
            SafeExecAux rest (execInstructionTrace mem2 core instr).1.mem
              (execInstructionTrace mem2 core instr).1.core := by
        simpa [SafeExecAux] using hsafe2
      have hok1 : (execInstructionTrace mem1 core instr).1.ok = true := hsafe1'.1
      have hreads_head :
          AgreeOnList (listJoin (instr.load.map (loadAddrs core.scratch))) mem1 mem2 := by
        have h' :
            AgreeOnList
              (listJoin (instr.load.map (loadAddrs core.scratch)) ++
                listJoin ((runTraceAux rest (execInstructionTrace mem1 core instr).1.mem
                      (execInstructionTrace mem1 core instr).1.core).2))
              mem1 mem2 := by
          simp [runTraceAux, hok1, listJoin_append] at hagree
          simpa using hagree
        exact agreeOnList_append_left (m1 := mem1) (m2 := mem2) h'
      have hok_core :=
        execInstructionTrace_ok_core_eq_of_agree mem1 mem2 core instr hreads_head
      have hok2 : (execInstructionTrace mem2 core instr).1.ok = true := by
        have := hok_core.1
        simpa [hok1] using this
      have hcore_eq : (execInstructionTrace mem1 core instr).1.core =
          (execInstructionTrace mem2 core instr).1.core := hok_core.2
      have hagree_rest :
          AgreeOnList
            (listJoin ((runTraceAux rest (execInstructionTrace mem1 core instr).1.mem
              (execInstructionTrace mem1 core instr).1.core).2))
            (execInstructionTrace mem1 core instr).1.mem
            (execInstructionTrace mem2 core instr).1.mem := by
        have h' :
            AgreeOnList
              (listJoin (instr.load.map (loadAddrs core.scratch)) ++
                listJoin ((runTraceAux rest (execInstructionTrace mem1 core instr).1.mem
                      (execInstructionTrace mem1 core instr).1.core).2))
              mem1 mem2 := by
          simp [runTraceAux, hok1, listJoin_append] at hagree
          simpa using hagree
        have hrest0 := agreeOnList_append_right (m1 := mem1) (m2 := mem2) h'
        let store_writes := instr.store.flatMap (execStoreSlot core.scratch)
        have hmw1 :
            memWriteMany mem1 store_writes =
              some (execInstructionTrace mem1 core instr).1.mem :=
          execInstructionTrace_memWriteMany_of_ok mem1 core instr hok1
        have hmw2 :
            memWriteMany mem2 store_writes =
              some (execInstructionTrace mem2 core instr).1.mem :=
          execInstructionTrace_memWriteMany_of_ok mem2 core instr hok2
        exact agreeOnList_after_writes
          (xs := listJoin
            ((runTraceAux rest (execInstructionTrace mem1 core instr).1.mem
                (execInstructionTrace mem1 core instr).1.core).2))
          (m1 := mem1) (m2 := mem2)
          (m1' := (execInstructionTrace mem1 core instr).1.mem)
          (m2' := (execInstructionTrace mem2 core instr).1.mem)
          store_writes hrest0 hmw1 hmw2
      have hsafe1r : SafeExecAux rest
          (execInstructionTrace mem1 core instr).1.mem
          (execInstructionTrace mem1 core instr).1.core := hsafe1'.2
      have hsafe2r : SafeExecAux rest
          (execInstructionTrace mem2 core instr).1.mem
          (execInstructionTrace mem1 core instr).1.core := by
        -- rewrite goal core using `hcore_eq`
        simpa [hcore_eq] using hsafe2'.2
      have htail := ih
        (mem1 := (execInstructionTrace mem1 core instr).1.mem)
        (mem2 := (execInstructionTrace mem2 core instr).1.mem)
        (core := (execInstructionTrace mem1 core instr).1.core)
        hagree_rest hsafe1r hsafe2r
      have hcore_eq2 : (execInstructionTrace mem2 core instr).1.core =
          (execInstructionTrace mem1 core instr).1.core := hcore_eq.symm
      -- `writes` for the head instruction depend only on the starting scratch, so they match.
      simpa [runTraceAuxRW, hok1, hok2, hcore_eq2, listJoin_append, htail]

-- NOTE: Non-interference is stated at the output level (not full memory equality).
-- The proof should show that if two memories agree on all addresses read by the program,
-- then the program's output slice is equal. This avoids the false stronger claim that
-- the entire final memory is equal.
-- Non-interference at the output level requires that the program actually writes
-- the output slice; otherwise outputs can differ without any reads.
lemma runTraceAuxRW_eq_on_written :
    ∀ prog mem1 mem2 core,
      AgreeOnList (listJoin (runTraceAux prog mem1 core).2) mem1 mem2 →
      SafeExecAux prog mem1 core →
      SafeExecAux prog mem2 core →
      ∀ addr,
        addr ∈
          listJoin
            ((runTraceAuxRW prog mem1 core).2.2.map (fun ws => ws.map Prod.fst)) →
        memAt (runTraceAuxRW prog mem1 core).1 addr =
        memAt (runTraceAuxRW prog mem2 core).1 addr := by
  intro prog
  induction prog with
  | nil =>
      intro mem1 mem2 core hagree hsafe1 hsafe2 addr hmem
      cases hmem
  | cons instr rest ih =>
      intro mem1 mem2 core hagree hsafe1 hsafe2 addr hmem
      -- unpack SafeExec on the head
      have hsafe1' :
          (execInstructionTrace mem1 core instr).1.ok = true ∧
          SafeExecAux rest (execInstructionTrace mem1 core instr).1.mem
            (execInstructionTrace mem1 core instr).1.core := by
        simpa [SafeExecAux] using hsafe1
      have hsafe2' :
          (execInstructionTrace mem2 core instr).1.ok = true ∧
          SafeExecAux rest (execInstructionTrace mem2 core instr).1.mem
            (execInstructionTrace mem2 core instr).1.core := by
        simpa [SafeExecAux] using hsafe2
      have hreads_head :
          AgreeOnList (listJoin (instr.load.map (loadAddrs core.scratch))) mem1 mem2 := by
        -- split agreement on full reads
        have h' :
            AgreeOnList
              (listJoin (instr.load.map (loadAddrs core.scratch)) ++
                listJoin ((runTraceAux rest
                  (execInstructionTrace mem1 core instr).1.mem
                  (execInstructionTrace mem1 core instr).1.core).2))
              mem1 mem2 := by
          -- runTraceAux on cons
          have hok : (execInstructionTrace mem1 core instr).1.ok = true := hsafe1'.1
          simp [runTraceAux, hok, listJoin_append] at hagree
          simpa using hagree
        exact agreeOnList_append_left (m1 := mem1) (m2 := mem2) h'
      -- ok/core equality on the head step
      have hok_core :=
        execInstructionTrace_ok_core_eq_of_agree mem1 mem2 core instr hreads_head
      have hok1 : (execInstructionTrace mem1 core instr).1.ok = true := hsafe1'.1
      have hok2 : (execInstructionTrace mem2 core instr).1.ok = true := by
        have := hok_core.1
        simpa [hok1] using this
      have hcore_eq : (execInstructionTrace mem1 core instr).1.core =
          (execInstructionTrace mem2 core instr).1.core := hok_core.2
      -- simplify runTraceAuxRW on ok branch
      have hmem_in :
          addr ∈
            listJoin ((instr.store.map (storeWrites core.scratch)).map (fun ws => ws.map Prod.fst)) ∨
            addr ∈
              listJoin
                (((runTraceAuxRW rest
                  (execInstructionTrace mem1 core instr).1.mem
                  (execInstructionTrace mem1 core instr).1.core).2.2).map (fun ws => ws.map Prod.fst)) := by
        have hok : (execInstructionTrace mem1 core instr).1.ok = true := hok1
        simpa [runTraceAuxRW, hok, listJoin_append, List.map_map] using hmem
      cases hmem_in with
      | inl hcur =>
          -- current-step written address
          -- show equality after the rest (either rewritten or preserved)
          -- build rest agreement + SafeExec once (used in both hlater branches)
          have hagree_rest :
              AgreeOnList
                (listJoin ((runTraceAux rest
                  (execInstructionTrace mem1 core instr).1.mem
                  (execInstructionTrace mem1 core instr).1.core).2))
                (execInstructionTrace mem1 core instr).1.mem
                (execInstructionTrace mem2 core instr).1.mem := by
            have h' :
                AgreeOnList
                  (listJoin (instr.load.map (loadAddrs core.scratch)) ++
                    listJoin ((runTraceAux rest
                      (execInstructionTrace mem1 core instr).1.mem
                      (execInstructionTrace mem1 core instr).1.core).2))
                  mem1 mem2 := by
              have hok : (execInstructionTrace mem1 core instr).1.ok = true := hok1
              simp [runTraceAux, hok, listJoin_append] at hagree
              simpa using hagree
            have hrest0 := agreeOnList_append_right (m1 := mem1) (m2 := mem2) h'
            let store_writes := instr.store.flatMap (execStoreSlot core.scratch)
            have hmw1 :
                memWriteMany mem1 store_writes =
                  some (execInstructionTrace mem1 core instr).1.mem :=
              execInstructionTrace_memWriteMany_of_ok mem1 core instr hok1
            have hmw2 :
                memWriteMany mem2 store_writes =
                  some (execInstructionTrace mem2 core instr).1.mem :=
              execInstructionTrace_memWriteMany_of_ok mem2 core instr hok2
            exact agreeOnList_after_writes
              (xs := listJoin
                ((runTraceAux rest (execInstructionTrace mem1 core instr).1.mem
                  (execInstructionTrace mem1 core instr).1.core).2))
              (m1 := mem1) (m2 := mem2)
              (m1' := (execInstructionTrace mem1 core instr).1.mem)
              (m2' := (execInstructionTrace mem2 core instr).1.mem)
              store_writes hrest0 hmw1 hmw2
          have hsafe1r : SafeExecAux rest
              (execInstructionTrace mem1 core instr).1.mem
              (execInstructionTrace mem1 core instr).1.core := hsafe1'.2
          have hsafe2r : SafeExecAux rest
              (execInstructionTrace mem2 core instr).1.mem
              (execInstructionTrace mem1 core instr).1.core := by
            simpa [hcore_eq] using hsafe2'.2
          by_cases hlater :
              addr ∈
                listJoin
                  (((runTraceAuxRW rest
                    (execInstructionTrace mem1 core instr).1.mem
                    (execInstructionTrace mem1 core instr).1.core).2.2).map (fun ws => ws.map Prod.fst))
          · -- written later: use IH
            -- apply IH on rest
            have hrest_eq := ih
              (mem1 := (execInstructionTrace mem1 core instr).1.mem)
              (mem2 := (execInstructionTrace mem2 core instr).1.mem)
              (core := (execInstructionTrace mem1 core instr).1.core)
              hagree_rest hsafe1r hsafe2r addr hlater
            have hcore_eq2 : (execInstructionTrace mem2 core instr).1.core =
                (execInstructionTrace mem1 core instr).1.core := hcore_eq.symm
            -- full execution's final memory is the tail memory (ok-branch), so reduce to IH.
            simpa [runTraceAuxRW, hok1, hok2, hcore_eq2] using hrest_eq
          · -- not written later: value set in this step and preserved
            -- show equality right after this step
            let store_writes := instr.store.flatMap (execStoreSlot core.scratch)
            have hmw1 :
                memWriteMany mem1 store_writes =
                  some (execInstructionTrace mem1 core instr).1.mem :=
              execInstructionTrace_memWriteMany_of_ok mem1 core instr hok1
            have hmw2 :
                memWriteMany mem2 store_writes =
                  some (execInstructionTrace mem2 core instr).1.mem :=
              execInstructionTrace_memWriteMany_of_ok mem2 core instr hok2
            have hcur' : addr ∈ store_writes.map Prod.fst := by
              -- current writes list is store_writes
              have hstore_addrs_eq :
                  store_writes.map Prod.fst =
                    listJoin ((instr.store.map (storeWrites core.scratch)).map (fun ws => ws.map Prod.fst)) := by
                simpa [store_writes, storeWrites] using
                  (map_fst_flatMap_execStoreSlot_eq_listJoin (slots := instr.store) (s := core.scratch))
              simpa [hstore_addrs_eq] using hcur
            have hmem_eq_step :
                memAt (execInstructionTrace mem1 core instr).1.mem addr =
                memAt (execInstructionTrace mem2 core instr).1.mem addr := by
              have hmem_eq := memWriteMany_eq_on mem1 mem2
                (execInstructionTrace mem1 core instr).1.mem
                (execInstructionTrace mem2 core instr).1.mem store_writes hmw1 hmw2
              exact hmem_eq addr hcur'
            -- later execution doesn't touch addr
            have hnot_later :
                addr ∉
                  listJoin
                    (((runTraceAuxRW rest
                      (execInstructionTrace mem1 core instr).1.mem
                      (execInstructionTrace mem1 core instr).1.core).2.2).map (fun ws => ws.map Prod.fst)) := by
              exact hlater
            have hmem1_tail :
                memAt
                    (runTraceAuxRW rest
                      (execInstructionTrace mem1 core instr).1.mem
                      (execInstructionTrace mem1 core instr).1.core).1 addr =
                  memAt (execInstructionTrace mem1 core instr).1.mem addr := by
              exact runTraceAuxRW_eq_of_not_written rest
                (execInstructionTrace mem1 core instr).1.mem
                (execInstructionTrace mem1 core instr).1.core addr hnot_later
            have hmem2_tail :
                memAt
                    (runTraceAuxRW rest
                      (execInstructionTrace mem2 core instr).1.mem
                      (execInstructionTrace mem2 core instr).1.core).1 addr =
                  memAt (execInstructionTrace mem2 core instr).1.mem addr := by
              -- transfer not-written to mem2 using write-addrs equality
              have htail_eq :=
                runTraceAuxRW_writeAddrs_eq_of_agree rest
                  (mem1 := (execInstructionTrace mem1 core instr).1.mem)
                  (mem2 := (execInstructionTrace mem2 core instr).1.mem)
                  (core := (execInstructionTrace mem1 core instr).1.core)
                  hagree_rest hsafe1r hsafe2r
              have hnot_later2_core1 :
                  addr ∉
                    listJoin
                      (((runTraceAuxRW rest
                        (execInstructionTrace mem2 core instr).1.mem
                        (execInstructionTrace mem1 core instr).1.core).2.2).map
                        (fun ws => ws.map Prod.fst)) := by
                simpa [htail_eq] using hnot_later
              have hcore_eq2 : (execInstructionTrace mem2 core instr).1.core =
                  (execInstructionTrace mem1 core instr).1.core := hcore_eq.symm
              have hnot_later2 :
                  addr ∉
                    listJoin
                      (((runTraceAuxRW rest
                        (execInstructionTrace mem2 core instr).1.mem
                        (execInstructionTrace mem2 core instr).1.core).2.2).map
                        (fun ws => ws.map Prod.fst)) := by
                simpa [hcore_eq2] using hnot_later2_core1
              exact runTraceAuxRW_eq_of_not_written rest
                (execInstructionTrace mem2 core instr).1.mem
                (execInstructionTrace mem2 core instr).1.core addr hnot_later2
            -- finish by rewriting the ok branch (avoid rewriting cores in inconsistent directions)
            calc
              memAt (runTraceAuxRW (instr :: rest) mem1 core).1 addr
                  =
                memAt
                    (runTraceAuxRW rest (execInstructionTrace mem1 core instr).1.mem
                      (execInstructionTrace mem1 core instr).1.core).1 addr := by
                      simp [runTraceAuxRW, hok1]
              _ = memAt (execInstructionTrace mem1 core instr).1.mem addr := hmem1_tail
              _ = memAt (execInstructionTrace mem2 core instr).1.mem addr := hmem_eq_step
              _ =
                memAt
                    (runTraceAuxRW rest (execInstructionTrace mem2 core instr).1.mem
                      (execInstructionTrace mem2 core instr).1.core).1 addr := by
                      symm
                      exact hmem2_tail
              _ = memAt (runTraceAuxRW (instr :: rest) mem2 core).1 addr := by
                      symm
                      simp [runTraceAuxRW, hok2]
      | inr hrest =>
          -- written later: apply IH
          have hagree_rest :
              AgreeOnList
                (listJoin ((runTraceAux rest
                  (execInstructionTrace mem1 core instr).1.mem
                  (execInstructionTrace mem1 core instr).1.core).2))
                (execInstructionTrace mem1 core instr).1.mem
                (execInstructionTrace mem2 core instr).1.mem := by
            have h' :
                AgreeOnList
                  (listJoin (instr.load.map (loadAddrs core.scratch)) ++
                    listJoin ((runTraceAux rest
                      (execInstructionTrace mem1 core instr).1.mem
                      (execInstructionTrace mem1 core instr).1.core).2))
                  mem1 mem2 := by
              have hok : (execInstructionTrace mem1 core instr).1.ok = true := hok1
              simp [runTraceAux, hok, listJoin_append] at hagree
              simpa using hagree
            have hrest0 := agreeOnList_append_right (m1 := mem1) (m2 := mem2) h'
            let store_writes := instr.store.flatMap (execStoreSlot core.scratch)
            have hmw1 :
                memWriteMany mem1 store_writes =
                  some (execInstructionTrace mem1 core instr).1.mem :=
              execInstructionTrace_memWriteMany_of_ok mem1 core instr hok1
            have hmw2 :
                memWriteMany mem2 store_writes =
                  some (execInstructionTrace mem2 core instr).1.mem :=
              execInstructionTrace_memWriteMany_of_ok mem2 core instr hok2
            exact agreeOnList_after_writes
              (xs := listJoin
                ((runTraceAux rest (execInstructionTrace mem1 core instr).1.mem
                  (execInstructionTrace mem1 core instr).1.core).2))
              (m1 := mem1) (m2 := mem2)
              (m1' := (execInstructionTrace mem1 core instr).1.mem)
              (m2' := (execInstructionTrace mem2 core instr).1.mem)
              store_writes hrest0 hmw1 hmw2
          have hsafe1r : SafeExecAux rest
              (execInstructionTrace mem1 core instr).1.mem
              (execInstructionTrace mem1 core instr).1.core := hsafe1'.2
          have hsafe2r : SafeExecAux rest
              (execInstructionTrace mem2 core instr).1.mem
              (execInstructionTrace mem1 core instr).1.core := by
            simpa [hcore_eq] using hsafe2'.2
          have hrest_eq := ih
            (mem1 := (execInstructionTrace mem1 core instr).1.mem)
            (mem2 := (execInstructionTrace mem2 core instr).1.mem)
            (core := (execInstructionTrace mem1 core instr).1.core)
            hagree_rest hsafe1r hsafe2r addr hrest
          have hcore_eq2 : (execInstructionTrace mem2 core instr).1.core =
              (execInstructionTrace mem1 core instr).1.core := hcore_eq.symm
          simpa [runTraceAuxRW, hok1, hok2, hcore_eq2] using hrest_eq

lemma runMem_eq_on_writeWords (p : Program) (mem1 mem2 : Memory)
    (hreads : AgreeOnList (readWords p mem1) mem1 mem2)
    (hsafe1 : SafeExec p mem1) (hsafe2 : SafeExec p mem2) :
    ∀ addr ∈ writeWords p mem1,
      memAt (runMem p mem1) addr = memAt (runMem p mem2) addr := by
  intro addr hmem
  have hreads' : AgreeOnList (listJoin (runTraceAux p.program mem1 (initCore p)).2) mem1 mem2 := by
    simpa [readWords, readOps, runTrace] using hreads
  have hsafe1' : SafeExecAux p.program mem1 (initCore p) := hsafe1
  have hsafe2' : SafeExecAux p.program mem2 (initCore p) := hsafe2
  have hmem' :
      addr ∈
        listJoin
          ((runTraceAuxRW p.program mem1 (initCore p)).2.2.map (fun ws => ws.map Prod.fst)) := by
    simpa [writeWords, writeOps] using hmem
  have hmem_eq := runTraceAuxRW_eq_on_written
      p.program mem1 mem2 (initCore p) hreads' hsafe1' hsafe2' addr hmem'
  have hfst := runTraceAuxRW_fst_eq p.program mem1 (initCore p)
  have hfst2 := runTraceAuxRW_fst_eq p.program mem2 (initCore p)
  -- rewrite runMem via runTraceAuxRW
  simpa [runMem, runTrace, hfst, hfst2] using hmem_eq

theorem run_eq_of_agree (p : Program) (mem1 mem2 : Memory)
    (hptr : memAt mem1 PTR_INP_VAL = memAt mem2 PTR_INP_VAL)
    (h : AgreeOnList (readWords p mem1) mem1 mem2)
    (hwrites : WritesOutput p mem1)
    (hsafe1 : SafeExec p mem1) (hsafe2 : SafeExec p mem2) :
    run p mem1 = run p mem2 := by
  funext i
  have haddr :
      memAt mem1 PTR_INP_VAL + i ∈ writeWords p mem1 := by
    have hsubset : outputAddrs mem1 ⊆ (writeWords p mem1).toFinset := hwrites
    have hmem : memAt mem1 PTR_INP_VAL + i ∈ outputAddrs mem1 := by
      classical
      -- element of outputAddrs by definition
      simp [outputAddrs]
    -- convert Finset membership to List membership
    simpa using (List.mem_toFinset.mp (hsubset hmem))
  have hmem_eq := runMem_eq_on_writeWords p mem1 mem2 h hsafe1 hsafe2 _ haddr
  -- rewrite output pointer for `mem2` to match `mem1`
  have hptr2 : memAt mem2 PTR_INP_VAL = memAt mem1 PTR_INP_VAL := hptr.symm
  simpa [run, outputOf, hptr2] using hmem_eq

/-! ### PC-trace non-interference (single-core machine) -/

def machineEqNoMem (m1 m2 : Machine) : Prop :=
  m1.cores = m2.cores ∧
  m1.program = m2.program ∧
  m1.cycle = m2.cycle ∧
  m1.enable_pause = m2.enable_pause ∧
  m1.enable_debug = m2.enable_debug ∧
  m1.value_trace = m2.value_trace ∧
  m1.aborted = m2.aborted



-- run_eq_of_agree is now axiomatized above to avoid an unsound full-memory-equality claim.


end ProofGlobalLowerBound
