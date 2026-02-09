import proofs.global_lower_bound.LowerBound.TraceEq

namespace ProofGlobalLowerBound
open ProofCommon
open ProofMachine
open ProofISA

def coreEqNoPc (c1 c2 : Core) : Prop :=
  c1.id = c2.id ∧
  c1.scratch = c2.scratch ∧
  c1.trace_buf = c2.trace_buf ∧
  c1.state = c2.state

lemma coreEqNoPc_refl (c : Core) : coreEqNoPc c c := by
  unfold coreEqNoPc
  exact ⟨rfl, rfl, rfl, rfl⟩
lemma listAll_forall {α : Type} {p : α → Prop} {l : List α} (h : List.Forall p l) :
    ∀ a ∈ l, p a := by
  simpa using (List.forall_iff_forall_mem.mp h)
lemma execFlowSlot_eq_of_coreEq (enablePause : Bool) (core1 core2 : Core)
    (s : Nat → Nat) (slot : FlowSlot)
    (hstraight : flowSlotStraight slot) (hcore : coreEqNoPc core1 core2) :
    coreEqNoPc (execFlowSlot enablePause core1 s slot).1
      (execFlowSlot enablePause core2 s slot).1 ∧
    (execFlowSlot enablePause core1 s slot).2 = (execFlowSlot enablePause core2 s slot).2 := by
  rcases hcore with ⟨hid, hscr, htrace, hstate⟩
  cases slot <;>
    simp [execFlowSlot, flowSlotStraight, coreEqNoPc, hid, hscr, htrace, hstate] at hstraight ⊢

lemma execFlowSlots_eq_of_coreEq (enablePause : Bool) (core1 core2 : Core)
    (s : Nat → Nat) (slots : List FlowSlot) (ws : List (Nat × Nat))
    (hstraight : ∀ slot ∈ slots, flowSlotStraight slot)
    (hcore : coreEqNoPc core1 core2) :
    coreEqNoPc
        (slots.foldl
          (fun acc slot =>
            let (c, ws) := acc
            let (c', ws') := execFlowSlot enablePause c s slot
            (c', ws ++ ws'))
          (core1, ws)).1
        (slots.foldl
          (fun acc slot =>
            let (c, ws) := acc
            let (c', ws') := execFlowSlot enablePause c s slot
            (c', ws ++ ws'))
          (core2, ws)).1 ∧
    (slots.foldl
          (fun acc slot =>
            let (c, ws) := acc
            let (c', ws') := execFlowSlot enablePause c s slot
            (c', ws ++ ws'))
          (core1, ws)).2
      =
    (slots.foldl
          (fun acc slot =>
            let (c, ws) := acc
            let (c', ws') := execFlowSlot enablePause c s slot
            (c', ws ++ ws'))
          (core2, ws)).2 := by
  induction slots generalizing core1 core2 ws with
  | nil =>
      simp [hcore]
  | cons slot rest ih =>
      have hslot : flowSlotStraight slot := hstraight slot (by simp)
      have hrest : ∀ slot ∈ rest, flowSlotStraight slot := by
        intro sl hsl
        exact hstraight sl (by simp [hsl])
      have hstep := execFlowSlot_eq_of_coreEq enablePause core1 core2 s slot hslot hcore
      rcases hstep with ⟨hcore', hws⟩
      have ih' := ih
        (core1 := (execFlowSlot enablePause core1 s slot).1)
        (core2 := (execFlowSlot enablePause core2 s slot).1)
        (ws := ws ++ (execFlowSlot enablePause core1 s slot).2)
        hrest hcore'
      simpa [List.foldl, hws] using ih'
lemma execInstructionTrace_eq_of_coreEq (mem : Memory) (core1 core2 : Core)
    (instr : Instruction) (hstraight : instrStraight instr)
    (hcore : coreEqNoPc core1 core2) :
    let r1 := execInstructionTrace mem core1 instr
    let r2 := execInstructionTrace mem core2 instr
    r1.1.ok = r2.1.ok ∧
      r1.1.mem = r2.1.mem ∧
      coreEqNoPc r1.1.core r2.1.core ∧
      r1.2 = r2.2 := by
  rcases hcore with ⟨hid, hscr, htrace, hstate⟩
  -- Read-trace lists depend only on the pre-exec scratch.
  have hreads :
      instr.load.map (loadAddrs core1.scratch) =
        instr.load.map (loadAddrs core2.scratch) := by
    simpa [hscr]
  -- Now compare `execInstruction` results.
  by_cases hWF : instrWellFormed instr
  · -- Well-formed: debug is disabled, so only slot semantics matters.
    cases hvalu : execValuSlots core1.scratch instr.valu with
    | none =>
        have hvalu2 : execValuSlots core2.scratch instr.valu = none := by
          simpa [hscr] using hvalu
        have hres1 :
            execInstruction false false (fun _ => 0) mem core1 instr =
              { core := core1, mem := mem, ok := false, debug_ok := true,
                has_non_debug := instrHasNonDebug instr } := by
          simp [execInstruction, hWF, hvalu]
        have hres2 :
            execInstruction false false (fun _ => 0) mem core2 instr =
              { core := core2, mem := mem, ok := false, debug_ok := true,
                has_non_debug := instrHasNonDebug instr } := by
          simp [execInstruction, hWF, hvalu2]
        -- Both sides fail in the VALU stage and return the input core/mem.
        refine ⟨?_, ⟨?_, ⟨?_, ?_⟩⟩⟩
        · simp [execInstructionTrace, hres1, hres2]
        · simp [execInstructionTrace, hres1, hres2]
        · simpa [execInstructionTrace, hres1, hres2, coreEqNoPc] using ⟨hid, hscr, htrace, hstate⟩
        · simpa [execInstructionTrace] using hreads
    | some valu_writes =>
        have hvalu2 : execValuSlots core2.scratch instr.valu = some valu_writes := by
          simpa [hscr] using hvalu
        cases halu : execAluSlots core1.scratch instr.alu with
        | none =>
            have halu2 : execAluSlots core2.scratch instr.alu = none := by
              simpa [hscr] using halu
            have hres1 :
                execInstruction false false (fun _ => 0) mem core1 instr =
                  { core := core1, mem := mem, ok := false, debug_ok := true,
                    has_non_debug := instrHasNonDebug instr } := by
              simp [execInstruction, hWF, hvalu, halu]
            have hres2 :
                execInstruction false false (fun _ => 0) mem core2 instr =
                  { core := core2, mem := mem, ok := false, debug_ok := true,
                    has_non_debug := instrHasNonDebug instr } := by
              simp [execInstruction, hWF, hvalu2, halu2]
            refine ⟨?_, ⟨?_, ⟨?_, ?_⟩⟩⟩
            · simp [execInstructionTrace, hres1, hres2]
            · simp [execInstructionTrace, hres1, hres2]
            · simpa [execInstructionTrace, hres1, hres2, coreEqNoPc] using ⟨hid, hscr, htrace, hstate⟩
            · simpa [execInstructionTrace] using hreads
        | some alu_writes =>
            have halu2 : execAluSlots core2.scratch instr.alu = some alu_writes := by
              simpa [hscr] using halu
            -- Load fold result is determined by `mem` and `scratch`.
            cases hload1 :
                (instr.load.foldl
                  (fun acc slot =>
                    match acc, execLoadSlot core1.scratch mem slot with
                    | some ws, some ws' => some (ws ++ ws')
                    | _, _ => none)
                  (some [])) with
            | none =>
                  have hload2 :
                      (instr.load.foldl
                        (fun acc slot =>
                          match acc, execLoadSlot core2.scratch mem slot with
                          | some ws, some ws' => some (ws ++ ws')
                          | _, _ => none)
                        (some [])) = none := by
                    simpa [hscr] using hload1
                  have hres1 :
                      execInstruction false false (fun _ => 0) mem core1 instr =
                        { core := core1, mem := mem, ok := false, debug_ok := true,
                          has_non_debug := instrHasNonDebug instr } := by
                    unfold execInstruction
                    simp (config := { zeta := true }) [hWF, hvalu, halu]
                    -- Push the load-fold result through the surrounding `match` using `congrArg`.
                    let f : Option (List (Nat × Nat)) → ExecResult := fun load_writes? =>
                      match load_writes? with
                      | none =>
                          { core := core1, mem := mem, ok := false, debug_ok := true,
                            has_non_debug := instrHasNonDebug instr }
                      | some load_writes =>
                          match memWriteMany mem (List.flatMap (execStoreSlot core1.scratch) instr.store) with
                          | none =>
                              { core := core1, mem := mem, ok := false, debug_ok := true,
                                has_non_debug := instrHasNonDebug instr }
                          | some mem' =>
                              let (core', flow_writes) :=
                                instr.flow.foldl
                                  (fun acc slot =>
                                    let (c, ws) := acc
                                    let (c', ws') := execFlowSlot false c core1.scratch slot
                                    (c', ws ++ ws'))
                                  (core1, [])
                              let scratch' :=
                                writeMany core1.scratch
                                  (valu_writes ++ alu_writes ++ flow_writes ++ load_writes)
                              let core'' := { core' with scratch := scratch' }
                              { core := core'', mem := mem', ok := true, debug_ok := true,
                                has_non_debug := instrHasNonDebug instr }
                    simpa (config := { zeta := true }) [f] using congrArg f hload1
                  have hres2 :
                      execInstruction false false (fun _ => 0) mem core2 instr =
                        { core := core2, mem := mem, ok := false, debug_ok := true,
                          has_non_debug := instrHasNonDebug instr } := by
                    unfold execInstruction
                    simp (config := { zeta := true }) [hWF, hvalu2, halu2]
                    let f : Option (List (Nat × Nat)) → ExecResult := fun load_writes? =>
                      match load_writes? with
                      | none =>
                          { core := core2, mem := mem, ok := false, debug_ok := true,
                            has_non_debug := instrHasNonDebug instr }
                      | some load_writes =>
                          match memWriteMany mem (List.flatMap (execStoreSlot core2.scratch) instr.store) with
                          | none =>
                              { core := core2, mem := mem, ok := false, debug_ok := true,
                                has_non_debug := instrHasNonDebug instr }
                          | some mem' =>
                              let (core', flow_writes) :=
                                instr.flow.foldl
                                  (fun acc slot =>
                                    let (c, ws) := acc
                                    let (c', ws') := execFlowSlot false c core2.scratch slot
                                    (c', ws ++ ws'))
                                  (core2, [])
                              let scratch' :=
                                writeMany core2.scratch
                                  (valu_writes ++ alu_writes ++ flow_writes ++ load_writes)
                              let core'' := { core' with scratch := scratch' }
                              { core := core'', mem := mem', ok := true, debug_ok := true,
                                has_non_debug := instrHasNonDebug instr }
                    simpa (config := { zeta := true }) [f] using congrArg f hload2
                  refine ⟨?_, ⟨?_, ⟨?_, ?_⟩⟩⟩
                  · simp [execInstructionTrace, hres1, hres2]
                  · simp [execInstructionTrace, hres1, hres2]
                  · simpa [execInstructionTrace, hres1, hres2, coreEqNoPc] using ⟨hid, hscr, htrace, hstate⟩
                  · simpa [execInstructionTrace] using hreads
            | some load_writes =>
                have hload2 :
                    (instr.load.foldl
                      (fun acc slot =>
                        match acc, execLoadSlot core2.scratch mem slot with
                        | some ws, some ws' => some (ws ++ ws')
                        | _, _ => none)
                      (some [])) = some load_writes := by
                  simpa [hscr] using hload1
                -- Store writes also depend only on scratch.
                cases hmw1 :
                    memWriteMany mem (instr.store.flatMap (execStoreSlot core1.scratch)) with
                | none =>
                    have hmw2 :
                        memWriteMany mem (instr.store.flatMap (execStoreSlot core2.scratch)) = none := by
                      simpa [hscr] using hmw1
                    have hres1 :
                        execInstruction false false (fun _ => 0) mem core1 instr =
                          { core := core1, mem := mem, ok := false, debug_ok := true,
                            has_non_debug := instrHasNonDebug instr } := by
                      -- In this branch `memWriteMany` fails, so the result is `ok=false`.
                      unfold execInstruction
                      simp (config := { zeta := true }) [hWF, hvalu, halu]
                      let f : Option (List (Nat × Nat)) → ExecResult := fun load_writes? =>
                        match load_writes? with
                        | none =>
                            { core := core1, mem := mem, ok := false, debug_ok := true,
                              has_non_debug := instrHasNonDebug instr }
                        | some load_writes =>
                            match memWriteMany mem (List.flatMap (execStoreSlot core1.scratch) instr.store) with
                            | none =>
                                { core := core1, mem := mem, ok := false, debug_ok := true,
                                  has_non_debug := instrHasNonDebug instr }
                            | some mem' =>
                                let (core', flow_writes) :=
                                  instr.flow.foldl
                                    (fun acc slot =>
                                      let (c, ws) := acc
                                      let (c', ws') := execFlowSlot false c core1.scratch slot
                                      (c', ws ++ ws'))
                                    (core1, [])
                                let scratch' :=
                                  writeMany core1.scratch
                                    (valu_writes ++ alu_writes ++ flow_writes ++ load_writes)
                                let core'' := { core' with scratch := scratch' }
                                { core := core'', mem := mem', ok := true, debug_ok := true,
                                  has_non_debug := instrHasNonDebug instr }
                      simpa (config := { zeta := true }) [f, hmw1] using congrArg f hload1
                    have hres2 :
                        execInstruction false false (fun _ => 0) mem core2 instr =
                          { core := core2, mem := mem, ok := false, debug_ok := true,
                            has_non_debug := instrHasNonDebug instr } := by
                      -- Same as `hres1` but starting from `core2`.
                      unfold execInstruction
                      simp (config := { zeta := true }) [hWF, hvalu2, halu2]
                      let f : Option (List (Nat × Nat)) → ExecResult := fun load_writes? =>
                        match load_writes? with
                        | none =>
                            { core := core2, mem := mem, ok := false, debug_ok := true,
                              has_non_debug := instrHasNonDebug instr }
                        | some load_writes =>
                            match memWriteMany mem (List.flatMap (execStoreSlot core2.scratch) instr.store) with
                            | none =>
                                { core := core2, mem := mem, ok := false, debug_ok := true,
                                  has_non_debug := instrHasNonDebug instr }
                            | some mem' =>
                                let (core', flow_writes) :=
                                  instr.flow.foldl
                                    (fun acc slot =>
                                      let (c, ws) := acc
                                      let (c', ws') := execFlowSlot false c core2.scratch slot
                                      (c', ws ++ ws'))
                                    (core2, [])
                                let scratch' :=
                                  writeMany core2.scratch
                                    (valu_writes ++ alu_writes ++ flow_writes ++ load_writes)
                                let core'' := { core' with scratch := scratch' }
                                { core := core'', mem := mem', ok := true, debug_ok := true,
                                  has_non_debug := instrHasNonDebug instr }
                      simpa (config := { zeta := true }) [f, hmw2] using congrArg f hload2
                    refine ⟨?_, ⟨?_, ⟨?_, ?_⟩⟩⟩
                    · simp [execInstructionTrace, hres1, hres2]
                    · simp [execInstructionTrace, hres1, hres2]
                    · simpa [execInstructionTrace, hres1, hres2, coreEqNoPc] using ⟨hid, hscr, htrace, hstate⟩
                    · simpa [execInstructionTrace] using hreads
                | some mem' =>
                    have hmw2 :
                        memWriteMany mem (instr.store.flatMap (execStoreSlot core2.scratch)) = some mem' := by
                      simpa [hscr] using hmw1
                    -- Flow fold: preserve all core fields except pc, and produce identical writes.
                    have hslots : ∀ slot ∈ instr.flow, flowSlotStraight slot :=
                      listAll_forall hstraight
                    let flowFold (core : Core) : Core × List (Nat × Nat) :=
                      instr.flow.foldl
                        (fun acc slot =>
                          let (c, ws) := acc
                          let (c', ws') := execFlowSlot false c core1.scratch slot
                          (c', ws ++ ws'))
                        (core, [])
                    have hflow :
                        coreEqNoPc (flowFold core1).1 (flowFold core2).1 ∧
                          (flowFold core1).2 = (flowFold core2).2 := by
                      -- `execFlowSlots_eq_of_coreEq` matches the `foldl` in `flowFold`.
                      simpa [flowFold] using
                        (execFlowSlots_eq_of_coreEq false core1 core2 core1.scratch instr.flow []
                          hslots ⟨hid, hscr, htrace, hstate⟩)
                    rcases hflow with ⟨hcoreFlow, hwsFlow⟩
                    let scratch' (core : Core) : Nat → Nat :=
                      writeMany core1.scratch (valu_writes ++ alu_writes ++ (flowFold core).2 ++ load_writes)
                    have hscratch : scratch' core1 = scratch' core2 := by
                      simp [scratch', hwsFlow]
                    let coreFinal (core : Core) : Core :=
                      { (flowFold core).1 with scratch := scratch' core }
                    have hcoreFinal : coreEqNoPc (coreFinal core1) (coreFinal core2) := by
                      -- unfold the record fields explicitly
                      rcases hcoreFlow with ⟨hid', hscr', htrace', hstate'⟩
                      refine ⟨hid', ?_, htrace', hstate'⟩
                    -- scratch is overwritten with the same function on both sides
                      simpa [coreFinal, hscratch]
                    -- Both executions succeed; relate their results to `coreFinal`.
                    have hres1 :
                        execInstruction false false (fun _ => 0) mem core1 instr =
                          { core := coreFinal core1, mem := mem', ok := true, debug_ok := true,
                            has_non_debug := instrHasNonDebug instr } := by
                      unfold execInstruction
                      simp (config := { zeta := true }) [hWF, hvalu, halu]
                      let f : Option (List (Nat × Nat)) → ExecResult := fun load_writes? =>
                        match load_writes? with
                        | none =>
                            { core := core1, mem := mem, ok := false, debug_ok := true,
                              has_non_debug := instrHasNonDebug instr }
                        | some load_writes =>
                            match memWriteMany mem (List.flatMap (execStoreSlot core1.scratch) instr.store) with
                            | none =>
                                { core := core1, mem := mem, ok := false, debug_ok := true,
                                  has_non_debug := instrHasNonDebug instr }
                            | some mem' =>
                                let (core', flow_writes) :=
                                  instr.flow.foldl
                                    (fun acc slot =>
                                      let (c, ws) := acc
                                      let (c', ws') := execFlowSlot false c core1.scratch slot
                                      (c', ws ++ ws'))
                                    (core1, [])
                                let scratch' :=
                                  writeMany core1.scratch
                                    (valu_writes ++ alu_writes ++ flow_writes ++ load_writes)
                                let core'' := { core' with scratch := scratch' }
                                { core := core'', mem := mem', ok := true, debug_ok := true,
                                  has_non_debug := instrHasNonDebug instr }
                      simpa (config := { zeta := true }) [f, hmw1, flowFold, scratch', coreFinal] using
                        congrArg f hload1
                    have hres2 :
                        execInstruction false false (fun _ => 0) mem core2 instr =
                          { core := coreFinal core2, mem := mem', ok := true, debug_ok := true,
                            has_non_debug := instrHasNonDebug instr } := by
                      unfold execInstruction
                      simp (config := { zeta := true }) [hWF, hvalu2, halu2]
                      let f : Option (List (Nat × Nat)) → ExecResult := fun load_writes? =>
                        match load_writes? with
                        | none =>
                            { core := core2, mem := mem, ok := false, debug_ok := true,
                              has_non_debug := instrHasNonDebug instr }
                        | some load_writes =>
                            match memWriteMany mem (List.flatMap (execStoreSlot core2.scratch) instr.store) with
                            | none =>
                                { core := core2, mem := mem, ok := false, debug_ok := true,
                                  has_non_debug := instrHasNonDebug instr }
                            | some mem' =>
                                let (core', flow_writes) :=
                                  instr.flow.foldl
                                    (fun acc slot =>
                                      let (c, ws) := acc
                                      let (c', ws') := execFlowSlot false c core2.scratch slot
                                      (c', ws ++ ws'))
                                    (core2, [])
                                let scratch' :=
                                  writeMany core2.scratch
                                    (valu_writes ++ alu_writes ++ flow_writes ++ load_writes)
                                let core'' := { core' with scratch := scratch' }
                                { core := core'', mem := mem', ok := true, debug_ok := true,
                                  has_non_debug := instrHasNonDebug instr }
                      simpa (config := { zeta := true }) [f, hmw2, hscr, flowFold, scratch', coreFinal] using
                        congrArg f hload2
                    -- Finish by projecting the required fields.
                    simp [execInstructionTrace, hreads, hres1, hres2, hcoreFinal]
  · -- Not well-formed: both sides return `ok=false` with the input core/mem.
      have hres1 :
          execInstruction false false (fun _ => 0) mem core1 instr =
            { core := core1, mem := mem, ok := false, debug_ok := false,
              has_non_debug := instrHasNonDebug instr } := by
        simp [execInstruction, hWF]
      have hres2 :
          execInstruction false false (fun _ => 0) mem core2 instr =
            { core := core2, mem := mem, ok := false, debug_ok := false,
              has_non_debug := instrHasNonDebug instr } := by
        simp [execInstruction, hWF]
      refine ⟨?_, ⟨?_, ⟨?_, ?_⟩⟩⟩
      · simp [execInstructionTrace, hres1, hres2]
      · simp [execInstructionTrace, hres1, hres2]
      · simpa [execInstructionTrace, hres1, hres2, coreEqNoPc] using ⟨hid, hscr, htrace, hstate⟩
      · simpa [execInstructionTrace] using hreads

theorem runTraceAux_eq_of_coreEq :
    ∀ prog mem core1 core2,
      (∀ instr ∈ prog, instrStraight instr) →
      coreEqNoPc core1 core2 →
      runTraceAux prog mem core1 = runTraceAux prog mem core2 := by
  intro prog mem core1 core2 hstraight hcore
  induction prog generalizing mem core1 core2 with
  | nil =>
      simp [runTraceAux]
  | cons instr rest ih =>
      have hstraight_head : instrStraight instr := hstraight instr (by simp)
      have hstraight_tail : ∀ instr ∈ rest, instrStraight instr := by
        intro i hi
        exact hstraight i (by simp [hi])
      -- Compare the single-step traces.
      have hstep :=
        execInstructionTrace_eq_of_coreEq mem core1 core2 instr hstraight_head hcore
      -- Unpack the result and split on `ok`.
      have hok :
          (execInstructionTrace mem core1 instr).1.ok =
            (execInstructionTrace mem core2 instr).1.ok := hstep.1
      have hmem :
          (execInstructionTrace mem core1 instr).1.mem =
            (execInstructionTrace mem core2 instr).1.mem := hstep.2.1
      have hcore' : coreEqNoPc (execInstructionTrace mem core1 instr).1.core
          (execInstructionTrace mem core2 instr).1.core := hstep.2.2.1
      have hreads :
          (execInstructionTrace mem core1 instr).2 = (execInstructionTrace mem core2 instr).2 := hstep.2.2.2
      -- Case split on ok for the shared next-step behavior.
      by_cases hok1 : (execInstructionTrace mem core1 instr).1.ok
      · have hok2 : (execInstructionTrace mem core2 instr).1.ok := by simpa [hok] using hok1
        -- recurse on the tail with the updated mem/core
        have htail :=
          ih (mem := (execInstructionTrace mem core1 instr).1.mem)
            (core1 := (execInstructionTrace mem core1 instr).1.core)
            (core2 := (execInstructionTrace mem core2 instr).1.core)
            hstraight_tail hcore'
        have htail_fst := congrArg Prod.fst htail
        have htail_snd := congrArg Prod.snd htail
        apply Prod.ext
        · simpa [runTraceAux, hok1, hok2, hmem] using htail_fst
        ·
          have :=
            congrArg (fun rs => (execInstructionTrace mem core1 instr).2 ++ rs) htail_snd
          simpa [runTraceAux, hok1, hok2, hmem, hreads] using this
      · have hok2 : ¬ (execInstructionTrace mem core2 instr).1.ok := by
          simpa [hok] using hok1
        -- both stop immediately; mem/read equality suffices
        simp [runTraceAux, hok1, hok2, hmem, hreads]
def MachineTraceAgrees (p : Program) (mem : Memory) : Prop :=
  runMachineTrace p mem = runTrace p mem

lemma listGet?_eq_some_of_drop_eq_cons {α : Type} {l : List α} {n : Nat} {x : α} {xs : List α} :
    l.drop n = x :: xs → listGet? l n = some x := by
  induction n generalizing l with
  | zero =>
      intro h
      cases l with
      | nil =>
          cases h
      | cons a as =>
          -- `drop 0` is the identity.
          cases h
          simp [listGet?]
  | succ n ih =>
      intro h
      cases l with
      | nil =>
          cases h
      | cons a as =>
          -- drop (n+1) (a::as) = drop n as, and get? (n+1) peels one cons.
          simp [List.drop] at h
          simpa [listGet?] using ih (l := as) h

lemma execFlowSlot_pc_state_eq_of_straight (enablePause : Bool) (core : Core)
    (s : Nat → Nat) (slot : FlowSlot) (hstraight : flowSlotStraight slot) :
    (execFlowSlot enablePause core s slot).1.pc = core.pc ∧
    (execFlowSlot enablePause core s slot).1.state = core.state := by
  cases slot <;> simp [execFlowSlot, flowSlotStraight] at hstraight ⊢

lemma execFlowSlots_pc_state_eq_of_straight (enablePause : Bool) (core : Core)
    (s : Nat → Nat) (slots : List FlowSlot) (ws : List (Nat × Nat))
    (hstraight : ∀ slot ∈ slots, flowSlotStraight slot) :
    (slots.foldl
          (fun acc slot =>
            let (c, ws) := acc
            let (c', ws') := execFlowSlot enablePause c s slot
            (c', ws ++ ws'))
          (core, ws)).1.pc = core.pc ∧
      (slots.foldl
          (fun acc slot =>
            let (c, ws) := acc
            let (c', ws') := execFlowSlot enablePause c s slot
            (c', ws ++ ws'))
          (core, ws)).1.state = core.state := by
  induction slots generalizing core ws with
  | nil =>
      simp
  | cons slot rest ih =>
      have hslot : flowSlotStraight slot := hstraight slot (by simp)
      have hrest : ∀ slot ∈ rest, flowSlotStraight slot := by
        intro sl hsl
        exact hstraight sl (by simp [hsl])
      have hstep := execFlowSlot_pc_state_eq_of_straight enablePause core s slot hslot
      have ih' :=
        ih (core := (execFlowSlot enablePause core s slot).1)
          (ws := ws ++ (execFlowSlot enablePause core s slot).2) hrest
      constructor
      · -- pc
        simpa [List.foldl, hstep.1] using ih'.1
      · -- state
        simpa [List.foldl, hstep.2] using ih'.2

lemma int_ofNat_add_one (n : Nat) : (Int.ofNat n) + 1 = Int.ofNat (n + 1) := by
  rfl

lemma execInstruction_pc_state_eq_of_instrStraight (enablePause : Bool) (enableDebug : Bool)
    (valueTrace : Nat → Nat) (mem : Memory) (core : Core) (instr : Instruction)
    (hstraight : instrStraight instr) :
    (execInstruction enablePause enableDebug valueTrace mem core instr).core.pc = core.pc ∧
      (execInstruction enablePause enableDebug valueTrace mem core instr).core.state = core.state := by
  -- Unfold once and split on the well-formedness and slot-stage failures; in all failure branches
  -- the returned core is the input core.
  classical
  by_cases hWF : instrWellFormed instr
  · -- Well-formed branch.
    have hflow : ∀ slot ∈ instr.flow, flowSlotStraight slot := by
      exact listAll_forall hstraight
    -- Debug branch only affects `ok`; core fields are unchanged on failure.
    by_cases hdbg : (if enableDebug then instr.debug.all (fun slot => execDebugSlot core.scratch valueTrace slot) else true)
    · -- Continue through remaining stages; regardless of which stage fails, pc/state preserved.
      cases hvalu : execValuSlots core.scratch instr.valu with
      | none =>
          simp (config := { zeta := true }) [execInstruction, hWF, hdbg, hvalu]
      | some valu_writes =>
          cases halu : execAluSlots core.scratch instr.alu with
            | none =>
                simp (config := { zeta := true }) [execInstruction, hWF, hdbg, hvalu, halu]
            | some alu_writes =>
                -- Loads/stores success or failure doesn't affect `pc/state`; only flow can, and straight-line
                -- flow slots preserve them.
                have hflow_pc_state :=
                  execFlowSlots_pc_state_eq_of_straight enablePause core core.scratch instr.flow [] hflow
                constructor
                · -- pc
                  simp (config := { zeta := true }) [execInstruction, hWF, hdbg, hvalu, halu]
                  -- `rw` is brittle here due to `mdata` wrappers in the elaborated fold function;
                  -- `generalize` with `_` reliably abstracts the scrutinee.
                  generalize hlw : List.foldl _ (some ([] : List (Nat × Nat))) instr.load = lw
                  cases lw with
                  | none =>
                      simp (config := { failIfUnchanged := false })
                  | some load_writes =>
                      generalize hmw : memWriteMany mem _ = mw
                      cases mw with
                      | none =>
                          simp (config := { failIfUnchanged := false })
                      | some mem' =>
                          simp [hflow_pc_state.1]
                · -- state
                  simp (config := { zeta := true }) [execInstruction, hWF, hdbg, hvalu, halu]
                  generalize hlw : List.foldl _ (some ([] : List (Nat × Nat))) instr.load = lw
                  cases lw with
                  | none =>
                      simp (config := { failIfUnchanged := false })
                  | some load_writes =>
                      generalize hmw : memWriteMany mem _ = mw
                      cases mw with
                      | none =>
                          simp (config := { failIfUnchanged := false })
                      | some mem' =>
                          simp [hflow_pc_state.2]
    · -- debug failed: core is unchanged
      constructor <;> simp (config := { zeta := true }) [execInstruction, hWF, hdbg]
  · -- Not well-formed: core is unchanged
    constructor <;> simp (config := { zeta := true }) [execInstruction, hWF]

theorem MachineTraceAgrees_of_StraightLine (p : Program) (hstraight : StraightLine p) :
    ∀ mem, MachineTraceAgrees p mem := by
  intro mem
  have hprog_straight : ∀ instr ∈ p.program, instrStraight instr := hstraight
  -- Simulation lemma: for a suffix `suf = drop pc p.program`, running the single-core machine for
  -- `suf.length` steps matches the list-recursive trace on that suffix.
  have hsim :
      ∀ (mem0 : Memory) (pc : Nat) (suf : List Instruction) (core : Core) (mcycle : Nat),
        suf = List.drop pc p.program →
        core.state = .running →
        core.pc = Int.ofNat pc →
        runMachineTraceAux suf.length
            { cores := [core], mem := mem0, program := p.program, cycle := mcycle,
              enable_pause := false, enable_debug := false, value_trace := fun _ => 0,
              aborted := false }
          =
          runTraceAux suf mem0 core := by
    intro mem0 pc suf core mcycle hsuf hrun hpc
    induction suf generalizing pc core mem0 mcycle with
    | nil =>
        simp [runMachineTraceAux, runTraceAux]
    | cons instr rest ih =>
        -- Suffix facts: head is at index `pc`, tail is `drop (pc+1)`.
        have hget : listGet? p.program pc = some instr := by
          apply listGet?_eq_some_of_drop_eq_cons (l := p.program) (n := pc) (x := instr) (xs := rest)
          -- hsuf : instr :: rest = drop pc p.program
          simpa [hsuf] using hsuf.symm
        have hrest : rest = List.drop (pc + 1) p.program := by
          calc
            rest = List.drop 1 (instr :: rest) := by simp [List.drop]
            _ = List.drop 1 (List.drop pc p.program) := by simpa [hsuf]
            _ = List.drop (pc + 1) p.program := by
              simpa using (List.drop_drop (l := p.program) (i := 1) (j := pc))
        -- The machine will take the step branch since the single core is running.
        have hany :
            anyRunning
                { cores := [core], mem := mem0, program := p.program, cycle := mcycle,
                  enable_pause := false, enable_debug := false, value_trace := fun _ => 0,
                  aborted := false } = true := by
          simp [anyRunning, hrun]
        -- Fetch identifies the head instruction.
        have hfetch : fetch p.program core.pc = some instr := by
          have : fetch p.program (Int.ofNat pc) = some instr := by
            simp [fetch, hget]
          simpa [hpc] using this
        -- Align the sequential step with the machine's pre-incremented PC.
        let core1 : Core := { core with pc := core.pc + 1 }
        have hcore_eq : coreEqNoPc core core1 := by
          unfold coreEqNoPc core1
          exact ⟨rfl, rfl, rfl, rfl⟩
        have hstraight_suf : ∀ ins ∈ (instr :: rest), instrStraight ins := by
          intro ins hins
          have : ins ∈ List.drop pc p.program := by simpa [hsuf] using hins
          have : ins ∈ p.program := List.mem_of_mem_drop this
          exact hprog_straight ins this
        have hrun_shift :
            runTraceAux (instr :: rest) mem0 core = runTraceAux (instr :: rest) mem0 core1 := by
          exact runTraceAux_eq_of_coreEq (prog := instr :: rest) (mem := mem0)
            (core1 := core) (core2 := core1) hstraight_suf hcore_eq
        have hinstr_straight : instrStraight instr := hstraight_suf instr (by simp)
        -- Unfold one step on both sides; then split on `ok` to match the recursion.
        -- LHS: `runMachineTraceAux` with succ fuel.
        have hstep :
            runMachineTraceAux (List.length (instr :: rest))
                { cores := [core], mem := mem0, program := p.program, cycle := mcycle,
                  enable_pause := false, enable_debug := false, value_trace := fun _ => 0,
                  aborted := false }
              =
              runTraceAux (instr :: rest) mem0 core := by
          -- rewrite RHS to start from `core1` (machine uses `core1` for exec)
          rw [hrun_shift]
          -- unfold `runMachineTraceAux` (succ) and choose the stepping branch
          simp [runMachineTraceAux, hany]
          -- unfold one machine step (singleton core)
          simp [stepMachineTrace, stepCoreTrace, hrun, hfetch, execInstructionTraceMachine, core1,
            execInstructionTrace]
          -- split on ok
          cases hok : (execInstruction false false (fun _ => 0) mem0 core1 instr).ok with
          | true =>
            -- ok=true: recurse on tail
            have hpc' :
                (execInstruction false false (fun _ => 0) mem0 core1 instr).core.pc =
                  Int.ofNat (pc + 1) := by
              have hpc_pres :=
                (execInstruction_pc_state_eq_of_instrStraight (enablePause := false) (enableDebug := false)
                    (valueTrace := fun _ => 0) (mem := mem0) (core := core1) (instr := instr)
                    hinstr_straight).1
              -- core1.pc = core.pc + 1 = ofNat pc + 1 = ofNat (pc+1)
              have hcore1_pc : core1.pc = Int.ofNat (pc + 1) := by
                simp [core1, hpc, int_ofNat_add_one]
              simpa [hpc_pres, hcore1_pc]
            have hstate' :
                (execInstruction false false (fun _ => 0) mem0 core1 instr).core.state = .running := by
              have hstate_pres :=
                (execInstruction_pc_state_eq_of_instrStraight (enablePause := false) (enableDebug := false)
                    (valueTrace := fun _ => 0) (mem := mem0) (core := core1) (instr := instr)
                    hinstr_straight).2
              simpa [core1, hrun] using hstate_pres
            -- After unfolding `stepMachineTrace`/`stepCoreTrace` we often end up with a core record where
            -- `state` is syntactically `.running`. Rewrite `hok` to match that shape so `simp` can use it.
            have hok_run :
                (execInstruction false false (fun _ => 0) mem0
                      { id := core.id, scratch := core.scratch, trace_buf := core.trace_buf, pc := core.pc + 1,
                        state := CoreState.running }
                      instr).ok = true := by
              simpa [core1, hrun] using hok
            -- Simplify (including unfolding one trace-step on the RHS) and then rewrite the recursive call by IH.
            simp (config := { failIfUnchanged := false }) [runTraceAux, execInstructionTrace, hok_run]
            have ih' :=
              ih (pc := pc + 1)
                (core := (execInstruction false false (fun _ => 0) mem0 core1 instr).core)
                (mem0 := (execInstruction false false (fun _ => 0) mem0 core1 instr).mem)
                (mcycle :=
                  if
                      (execInstruction false false (fun _ => 0) mem0 core1 instr).has_non_debug = true then
                    mcycle + 1
                  else mcycle)
                (by simpa [hrest])
                hstate' hpc'
            have ih_run := (by simpa [core1, hrun] using ih')
            simpa [ih_run]
          | false =>
            -- ok=false: both stop immediately; tail trace is empty
            have hok_run :
                (execInstruction false false (fun _ => 0) mem0
                      { id := core.id, scratch := core.scratch, trace_buf := core.trace_buf, pc := core.pc + 1,
                        state := CoreState.running }
                      instr).ok = false := by
              simpa [core1, hrun] using hok
            simp (config := { failIfUnchanged := false })
              [runTraceAux, execInstructionTrace, hok_run]
            constructor <;>
              cases hlen : rest.length <;>
                simp [runMachineTraceAux, anyRunning, hlen]
        -- Finish cons-case goal by rewriting `suf` and using the one-step lemma.
        simpa using hstep
  -- Apply the simulation lemma at `pc=0`, suffix = full program, and the initial machine/core.
  have hmain :=
    hsim (mem0 := mem) (pc := 0) (suf := p.program) (core := initCore p) (mcycle := 0)
      (by simp) rfl rfl
  -- Unfold wrappers `runMachineTrace`/`runTrace`.
  simpa [MachineTraceAgrees, runMachineTrace, runMachineTraceFuel, initMachine, runTrace] using hmain
lemma runMachine_eq_run (p : Program) (mem : Memory)
    (htrace : MachineTraceAgrees p mem) : runMachine p mem = run p mem := by
  -- `MachineTraceAgrees` gives equality of the final memories; outputs are a projection of that.
  have hmem : runMemMachine p mem = runMem p mem := by
    have := congrArg (fun t => t.1) htrace
    simpa [runMemMachine, runMem] using this
  simp [runMachine, run, hmem]

lemma readWordCountMachine_eq (p : Program) (mem : Memory)
    (htrace : MachineTraceAgrees p mem) :
    readWordCountMachine p mem = readWordCount p mem := by
  have hreads : readOpsMachine p mem = readOps p mem := by
    have := congrArg (fun t => t.2) htrace
    simpa [readOpsMachine, readOps] using this
  simp [readWordCountMachine, readWordCount, readWordsMachine, readWords, hreads]
lemma CorrectOnMachine_to_CorrectOn (spec : Memory → Output) (p : Program) (memOk : Memory → Prop)
    (hcorrect : CorrectOnMachine spec p memOk)
    (htrace : ∀ mem, memOk mem → MachineTraceAgrees p mem) :
    CorrectOn spec p memOk := by
  intro mem hOk
  have hmach : runMachine p mem = spec mem := hcorrect mem hOk
  have hr : runMachine p mem = run p mem := runMachine_eq_run p mem (htrace mem hOk)
  -- rewrite machine correctness through the trace agreement
  calc
    run p mem = runMachine p mem := hr.symm
    _ = spec mem := hmach
lemma loadAddrs_length_le (s : Nat → Nat) (slot : LoadSlot) :
    (loadAddrs s slot).length ≤ VLEN := by
  cases slot <;> simp [loadAddrs, VLEN]
lemma readOps_bound_aux :
    ∀ prog mem core, ∀ op ∈ (runTraceAux prog mem core).2, op.length ≤ VLEN := by
  intro prog mem core
  induction prog generalizing mem core with
  | nil =>
      intro op hop
      simp [runTraceAux] at hop
  | cons instr rest ih =>
      intro op hop
      by_cases hok : (execInstructionTrace mem core instr).1.ok
      · simp [runTraceAux, hok] at hop
        rcases hop with hop | hop
        · rcases List.mem_map.1 hop with ⟨slot, hslot, rfl⟩
          exact loadAddrs_length_le _ _
        · exact ih (mem := (execInstructionTrace mem core instr).1.mem)
            (core := (execInstructionTrace mem core instr).1.core) op hop
      · simp [runTraceAux, hok] at hop
        rcases List.mem_map.1 hop with ⟨slot, hslot, rfl⟩
        exact loadAddrs_length_le _ _
lemma readOps_bound (p : Program) (mem : Memory) :
    ∀ op ∈ readOps p mem, op.length ≤ VLEN := by
  simpa [readOps, runTrace] using (readOps_bound_aux p.program mem (initCore p))
lemma length_join_le (ops : List (List Nat))
    (h : ∀ op ∈ ops, op.length ≤ VLEN) :
    (listJoin ops).length ≤ VLEN * ops.length := by
  induction ops with
  | nil =>
      simp [listJoin]
  | cons op ops ih =>
      have hop : op.length ≤ VLEN := h op (by simp)
      have hrest : ∀ o ∈ ops, o.length ≤ VLEN := by
        intro o ho
        exact h o (by simp [ho])
      have ih' := ih hrest
      calc
        (listJoin (op :: ops)).length = op.length + (listJoin ops).length := by
          simp [listJoin]
        _ ≤ VLEN + VLEN * ops.length := by
          exact Nat.add_le_add hop ih'
        _ = VLEN * (ops.length + 1) := by
          simp [Nat.mul_add, Nat.add_comm]
        _ = VLEN * (List.length (op :: ops)) := by simp
lemma ceilDiv_le_of_mul_le {n k d : Nat} (hd : 0 < d) (h : n ≤ d * k) :
    ceilDiv n d ≤ k := by
  unfold ceilDiv
  have hd1 : 1 ≤ d := (Nat.succ_le_iff).2 hd
  have h' : n + d - 1 ≤ d * k + (d - 1) := by
    have h'' : n + (d - 1) ≤ d * k + (d - 1) := Nat.add_le_add_right h (d - 1)
    have hrewrite : n + d - 1 = n + (d - 1) := by
      exact (Nat.add_sub_assoc (m := d) (k := 1) (n := n) hd1)
    simpa [hrewrite] using h''
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
  by_cases hd : d = 0
  · subst hd
    simp [ceilDiv]
  · have hd1 : 1 ≤ d := (Nat.succ_le_iff).2 (Nat.pos_of_ne_zero hd)
    unfold ceilDiv
    have h' : a + d - 1 ≤ b + d - 1 := by
      have h'' : a + (d - 1) ≤ b + (d - 1) := Nat.add_le_add_right h (d - 1)
      have ha : a + d - 1 = a + (d - 1) := by
        exact (Nat.add_sub_assoc (m := d) (k := 1) (n := a) hd1)
      have hb : b + d - 1 = b + (d - 1) := by
        exact (Nat.add_sub_assoc (m := d) (k := 1) (n := b) hd1)
      simpa [ha, hb] using h''
    exact Nat.div_le_div_right h'
lemma minLoadOps_mono {a b : Nat} (h : a ≤ b) :
    minLoadOps a ≤ minLoadOps b := by
  exact ceilDiv_mono h


end ProofGlobalLowerBound
