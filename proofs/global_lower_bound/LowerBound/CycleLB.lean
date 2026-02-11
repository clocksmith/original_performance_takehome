import proofs.global_lower_bound.LowerBound.MachineTraceEq

namespace ProofGlobalLowerBound
open ProofCommon
open ProofMachine
open ProofISA

/-!
Bridge lemma: executed load-slot count implies a lower bound on machine cycles.

Key idea (one core):
- Each executed cycle can include at most `LOAD_CAP` load slots (`instrWellFormed`).
- `readOpsMachineFuel` is exactly the concatenation of the per-cycle load-slot lists.
So total executed load slots ≤ `LOAD_CAP * cycleCountMachineFuel`.
-/

lemma runMachineTraceAuxFull_reads_eq (fuel : Nat) (m : Machine) :
    (runMachineTraceAuxFull fuel m).2 = (runMachineTraceAux fuel m).2 := by
  induction fuel generalizing m with
  | zero =>
      simp [runMachineTraceAuxFull, runMachineTraceAux]
  | succ fuel ih =>
      by_cases hrun : !anyRunning m
      · simp [runMachineTraceAuxFull, runMachineTraceAux, hrun]
      · simp [runMachineTraceAuxFull, runMachineTraceAux, hrun, ih, List.append_assoc]

lemma readOpsMachineFuel_eq_full (p : Program) (fuel : Nat) (mem : Memory) :
    readOpsMachineFuel p fuel mem = (runMachineTraceAuxFull fuel (initMachine p mem)).2 := by
  simp [readOpsMachineFuel, runMachineTraceFuel, runMachineTraceAuxFull_reads_eq]

lemma loadOpCountMachineFuel_eq_full (p : Program) (fuel : Nat) (mem : Memory) :
    loadOpCountMachineFuel p fuel mem = (runMachineTraceAuxFull fuel (initMachine p mem)).2.length := by
  simp [loadOpCountMachineFuel, readOpsMachineFuel_eq_full]

lemma stepCoreTrace_reads_len_eq_zero_of_did_false (m : Machine) (core : Core)
    (hdid : (stepCoreTrace m core).2.2.1 = false) :
    (stepCoreTrace m core).2.2.2.2.length = 0 := by
  cases hst : core.state with
  | running =>
      cases hfetch : fetch m.program core.pc with
      | none =>
          simp [stepCoreTrace, hst, hfetch] at hdid
          simp [stepCoreTrace, hst, hfetch]
      | some instr =>
          -- did = res.has_non_debug = instrHasNonDebug instr
          have hnon : instrHasNonDebug instr = false := by
            -- `stepCoreTrace` uses `execInstructionTraceMachine`; `did` is `res.has_non_debug`.
            simp [stepCoreTrace, hst, hfetch, execInstructionTraceMachine, execInstruction_hasNonDebug] at hdid
            exact hdid
          -- `instrHasNonDebug=false` implies *all* non-debug slot lists are empty, in particular `instr.load=[]`.
          have hall :
              (((instr.alu = [] ∧ instr.valu = []) ∧ instr.load = []) ∧ instr.store = []) ∧
                instr.flow = [] := by
            simpa [instrHasNonDebug] using hnon
          rcases hall with ⟨⟨⟨⟨_, _⟩, hloadEmpty⟩, _⟩, _⟩
          -- reads are `instr.load.map ...`, so empty loads means empty reads.
          simp [stepCoreTrace, hst, hfetch, execInstructionTraceMachine, hloadEmpty]
  | paused =>
      simp [stepCoreTrace, hst] at hdid
      simp [stepCoreTrace, hst]
  | stopped =>
      simp [stepCoreTrace, hst] at hdid
      simp [stepCoreTrace, hst]

lemma stepCoreTrace_reads_len_le_of_ok (m : Machine) (core : Core)
    (hok : (stepCoreTrace m core).2.2.2.1 = true) :
    (stepCoreTrace m core).2.2.2.2.length ≤ LOAD_CAP := by
  cases hst : core.state with
  | running =>
      cases hfetch : fetch m.program core.pc with
      | none =>
          simp [stepCoreTrace, hst, hfetch]
      | some instr =>
          -- ok=true implies instrWellFormed, which includes the load cap.
          have hwf : instrWellFormed instr := by
            simp [stepCoreTrace, hst, hfetch, execInstructionTraceMachine] at hok
            exact execInstruction_ok_implies_wellFormed _ _ _ _ _ _ hok
          have hcap : instr.load.length ≤ LOAD_CAP := hwf.2.2.1
          simpa [stepCoreTrace, hst, hfetch, execInstructionTraceMachine] using hcap
  | paused =>
      simp [stepCoreTrace, hst]
  | stopped =>
      simp [stepCoreTrace, hst]

/-!
`stepCoreTrace` depends only on `m.mem`, `m.program`, and the execution flags
`enable_pause`, `enable_debug`, `value_trace` (not on `m.cores`, `m.cycle`, or `m.aborted`).

This lemma lets us replace the synthetic machine values that show up after
unfolding `stepMachineTrace` with the original machine.
-/
lemma stepCoreTrace_congr (m1 m2 : Machine) (core : Core)
    (hmem : m1.mem = m2.mem)
    (hprog : m1.program = m2.program)
    (hpause : m1.enable_pause = m2.enable_pause)
    (hdebug : m1.enable_debug = m2.enable_debug)
    (htrace : m1.value_trace = m2.value_trace) :
    stepCoreTrace m1 core = stepCoreTrace m2 core := by
  cases hst : core.state <;>
    simp [stepCoreTrace, hst, hmem, hprog, hpause, hdebug, htrace, execInstructionTraceMachine]

lemma runMachineTraceAuxFull_aborted_false_implies
    (fuel : Nat) (m : Machine) :
    (runMachineTraceAuxFull fuel m).1.aborted = false → m.aborted = false := by
  induction fuel generalizing m with
  | zero =>
      intro h
      simpa [runMachineTraceAuxFull] using h
  | succ fuel ih =>
      intro h
      by_cases hrun : !anyRunning m
      · simpa [runMachineTraceAuxFull, hrun] using h
      · -- In the stepping case, final `aborted=false` implies the stepped machine has `aborted=false`.
        have htail : (runMachineTraceAuxFull fuel (stepMachineTrace m).1).1.aborted = false := by
          simpa [runMachineTraceAuxFull, hrun] using h
        have hab_step : (stepMachineTrace m).1.aborted = false :=
          ih (m := (stepMachineTrace m).1) htail
        -- If `m.aborted=true`, `stepMachineTrace` returns `m` unchanged, so it cannot produce `aborted=false`.
        by_cases hab : m.aborted = false
        · exact hab
        · have hab' : m.aborted = true := by
            cases h : m.aborted <;> simp [h] at hab ⊢
          have : (stepMachineTrace m).1.aborted = true := by
            simp [stepMachineTrace, hab']
          cases hab_step ▸ this

lemma stepMachineTrace_singleton_reads_bound
    (m : Machine) (core : Core)
    (hcores : m.cores = [core])
    (hab : m.aborted = false)
    (hnoAbort : (stepMachineTrace m).1.aborted = false) :
    (stepMachineTrace m).2.length + LOAD_CAP * m.cycle ≤ LOAD_CAP * (stepMachineTrace m).1.cycle := by
  -- Expand `stepMachineTrace` for a singleton, non-aborted machine.
  have hstep :
      stepMachineTrace m =
        let (core', mem', did, ok, reads) := stepCoreTrace m core
        if !ok then
          ({ m with
              cores := [{ core' with state := .stopped }],
              mem := mem',
              aborted := true }, reads)
        else
          let cycle' := if did then m.cycle + 1 else m.cycle
          ({ m with cores := [core'], mem := mem', cycle := cycle' }, reads) := by
    -- Unfold and evaluate the fold over `[core]`. This introduces a synthetic machine
    -- (with the same mem/program/flags) inside `stepCoreTrace`; rewrite it back to `m`.
    have hcore :
        stepCoreTrace
              { cores := [core], mem := m.mem, program := m.program, cycle := m.cycle,
                enable_pause := m.enable_pause, enable_debug := m.enable_debug, value_trace := m.value_trace }
              core
          =
        stepCoreTrace m core := by
      -- mem/program/flags agree by construction
      exact stepCoreTrace_congr _ _ _ rfl rfl rfl rfl rfl
    -- `simp` evaluates the singleton fold but leaves `stepCoreTrace` applied to a synthetic machine.
    -- Rewrite those occurrences using `hcore`.
    simp [stepMachineTrace, hab, hcores, List.foldl]
    simp [hcore]
  -- From `hnoAbort`, we must be in the `ok=true` branch.
  have hok : (stepCoreTrace m core).2.2.2.1 = true := by
    by_cases hok' : (stepCoreTrace m core).2.2.2.1 = true
    · exact hok'
    · have hok'' : (stepCoreTrace m core).2.2.2.1 = false := by
        cases h : (stepCoreTrace m core).2.2.2.1 <;> simp [h] at hok' ⊢
      have : (stepMachineTrace m).1.aborted = true := by
        simp [hstep, hok'']
      cases hnoAbort ▸ this
  have hlen_ok :
      (stepCoreTrace m core).2.2.2.2.length ≤ LOAD_CAP :=
    stepCoreTrace_reads_len_le_of_ok (m := m) (core := core) hok
  by_cases hdid : (stepCoreTrace m core).2.2.1 = true
  · have hcycle : (stepMachineTrace m).1.cycle = m.cycle + 1 := by
      simp [hstep, hok, hdid]
    have hreads : (stepMachineTrace m).2.length ≤ LOAD_CAP := by
      simpa [hstep, hok] using hlen_ok
    have := Nat.add_le_add_right hreads (LOAD_CAP * m.cycle)
    simpa [hcycle, Nat.mul_add, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using this
  · have hdid' : (stepCoreTrace m core).2.2.1 = false := by
      cases h : (stepCoreTrace m core).2.2.1 <;> simp [h] at hdid ⊢
    have hreads0 : (stepCoreTrace m core).2.2.2.2.length = 0 :=
      stepCoreTrace_reads_len_eq_zero_of_did_false (m := m) (core := core) hdid'
    have hcycle : (stepMachineTrace m).1.cycle = m.cycle := by
      simp [hstep, hok, hdid']
    simp [hstep, hok, hdid', hreads0, hcycle]

lemma runMachineTraceAuxFull_loadCount_le_cycle
    (fuel : Nat) (m : Machine)
    (hcores : m.cores.length = 1)
    (hnoAbort : (runMachineTraceAuxFull fuel m).1.aborted = false) :
    (runMachineTraceAuxFull fuel m).2.length + LOAD_CAP * m.cycle ≤
      LOAD_CAP * (runMachineTraceAuxFull fuel m).1.cycle := by
  induction fuel generalizing m with
  | zero =>
      simp [runMachineTraceAuxFull]
  | succ fuel ih =>
      by_cases hrun : !anyRunning m
      · simp [runMachineTraceAuxFull, hrun]
      · -- Step once, then apply IH on the tail.
        have hab : m.aborted = false :=
          runMachineTraceAuxFull_aborted_false_implies (fuel := Nat.succ fuel) (m := m) hnoAbort
        -- Extract the singleton core (we only prove this bound for one-core machines).
        cases hcs : m.cores with
        | nil =>
            simp [hcs] at hcores
        | cons core rest =>
            cases rest with
            | cons _ _ =>
                simp [hcs] at hcores
            | nil =>
                have hcores' : m.cores = [core] := by simpa [hcs]
                -- Unfold one runner step.
                set sm := stepMachineTrace m with hsm
                set m1 := sm.1 with hm1
                set r1 := sm.2 with hr1
                have htailAbort : (runMachineTraceAuxFull fuel m1).1.aborted = false := by
                  -- `runMachineTraceAuxFull (fuel+1) m` recurses into the tail run.
                  simpa [runMachineTraceAuxFull, hrun, hsm, hm1] using hnoAbort
                have hab1 : m1.aborted = false :=
                  runMachineTraceAuxFull_aborted_false_implies (fuel := fuel) (m := m1) htailAbort
                have hnoAbortStep : (stepMachineTrace m).1.aborted = false := by
                  simpa [hsm, hm1] using hab1
                -- Per-step bound.
                have hstep :
                    r1.length + LOAD_CAP * m.cycle ≤ LOAD_CAP * m1.cycle := by
                  have := stepMachineTrace_singleton_reads_bound
                    (m := m) (core := core) hcores' hab hnoAbortStep
                  simpa [hsm, hr1, hm1] using this
                -- IH on the tail run.
                have htailCores : m1.cores.length = 1 := by
                  -- singleton step preserves core count
                  simp [hm1, hsm, stepMachineTrace, hab, hcores', List.foldl]
                  by_cases h :
                      (stepCoreTrace
                              { cores := [core], mem := m.mem, program := m.program, cycle := m.cycle,
                                enable_pause := m.enable_pause, enable_debug := m.enable_debug,
                                value_trace := m.value_trace }
                              core).2.2.2.1 =
                        false <;> simp [h]
                have htail := ih (m := m1) htailCores htailAbort
                have hlen :
                    (r1 ++ (runMachineTraceAuxFull fuel m1).2).length =
                      r1.length + (runMachineTraceAuxFull fuel m1).2.length := by
                  simp
                -- Name the tail pieces to make the arithmetic readable.
                set tail := runMachineTraceAuxFull fuel m1 with htailrun
                set mfin := tail.1 with hmfin
                set r2 := tail.2 with hr2
                have htail' :
                    r2.length + LOAD_CAP * m1.cycle ≤ LOAD_CAP * mfin.cycle := by
                  simpa [htailrun, hmfin, hr2] using htail
                -- Add `r2.length` to the per-step bound, then chain into the tail bound.
                have hstep' :
                    r1.length + LOAD_CAP * m.cycle + r2.length ≤ LOAD_CAP * m1.cycle + r2.length :=
                  Nat.add_le_add_right hstep r2.length
                have hstep'' :
                    r1.length + r2.length + LOAD_CAP * m.cycle ≤ r2.length + LOAD_CAP * m1.cycle := by
                  -- reassociate/commute to match the tail bound's LHS
                  simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hstep'
                have hcomb : r1.length + r2.length + LOAD_CAP * m.cycle ≤ LOAD_CAP * mfin.cycle :=
                  le_trans hstep'' htail'
                -- Rewrite the goal into the same shape and finish.
                simpa [runMachineTraceAuxFull, hrun, hsm, hm1, hr1, htailrun, hmfin, hr2, hlen,
                  Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hcomb

theorem loadOpCountMachineFuel_le_cycle
    (p : Program) (fuel : Nat) (mem : Memory)
    (hnoAbort : (runMachineFinalFuel p fuel mem).aborted = false) :
    loadOpCountMachineFuel p fuel mem ≤ LOAD_CAP * cycleCountMachineFuel p fuel mem := by
  -- Apply the runner lemma to the initial machine (one core, cycle=0).
  have hcores : (initMachine p mem).cores.length = 1 := by simp [initMachine, initCore]
  have hmain :=
    runMachineTraceAuxFull_loadCount_le_cycle
      (fuel := fuel) (m := initMachine p mem) hcores (by simpa [runMachineFinalFuel] using hnoAbort)
  -- simplify (cycle starts at 0)
  -- and rewrite the LHS as `loadOpCountMachineFuel`.
  have hcount :
      loadOpCountMachineFuel p fuel mem + LOAD_CAP * 0 ≤
        LOAD_CAP * cycleCountMachineFuel p fuel mem := by
    simpa [runMachineFinalFuel, cycleCountMachineFuel, loadOpCountMachineFuel_eq_full] using hmain
  simpa using (Nat.le_of_add_le_add_right hcount)

/-!
### From Words → Load Ops → Cycles

To connect `loadLowerCycles (readWordCountMachine ...)` to actual `Machine.cycle`, we need:
1. Each recorded load slot reads at most `VLEN` words, so
   `minLoadOps (readWordCountMachineFuel ...) ≤ loadOpCountMachineFuel ...`.
2. From this file, `loadOpCountMachineFuel ... ≤ LOAD_CAP * cycleCountMachineFuel ...` (no abort).
3. Therefore `ceilDiv (minLoadOps ...) LOAD_CAP ≤ cycleCountMachineFuel ...`.
-/

lemma stepCoreTrace_reads_bound (m : Machine) (core : Core) :
    ∀ op ∈ (stepCoreTrace m core).2.2.2.2, op.length ≤ VLEN := by
  intro op hop
  cases hst : core.state with
  | running =>
      cases hfetch : fetch m.program core.pc with
      | none =>
          simp [stepCoreTrace, hst, hfetch] at hop
      | some instr =>
          -- reads are `instr.load.map (loadAddrs core1.scratch)`
          simp [stepCoreTrace, hst, hfetch, execInstructionTraceMachine] at hop
          rcases hop with ⟨slot, hslot, hopEq⟩
          -- `op = loadAddrs ... slot`
          simpa [hopEq] using (loadAddrs_length_le core.scratch slot)
  | paused =>
      simp [stepCoreTrace, hst] at hop
  | stopped =>
      simp [stepCoreTrace, hst] at hop

lemma stepMachineTrace_reads_bound_onecore (m : Machine)
    (hcores : m.cores.length = 1) :
    ∀ op ∈ (stepMachineTrace m).2, op.length ≤ VLEN := by
  -- Extract the unique core and unfold the singleton fold.
  cases hcs : m.cores with
  | nil =>
      simp [hcs] at hcores
  | cons core rest =>
      cases rest with
      | cons _ _ =>
          simp [hcs] at hcores
      | nil =>
          have hcores' : m.cores = [core] := by simpa [hcs]
          intro op hop
          by_cases hab : m.aborted
          · simp [stepMachineTrace, hab] at hop
          · -- singleton fold produces exactly this core's reads
            -- Unfold `stepMachineTrace` (singleton fold), then split the `if !okAll` (it doesn't affect `reads`).
            let msyn : Machine :=
              { cores := [core], mem := m.mem, program := m.program, cycle := m.cycle,
                enable_pause := m.enable_pause, enable_debug := m.enable_debug, value_trace := m.value_trace }
            have hreads :
                (stepMachineTrace m).2 = (stepCoreTrace msyn core).2.2.2.2 := by
              by_cases h : (stepCoreTrace msyn core).2.2.2.1 = false
              · simp [stepMachineTrace, hab, hcores', List.foldl, msyn, h]
              · simp [stepMachineTrace, hab, hcores', List.foldl, msyn, h]
            have hop' : op ∈ (stepCoreTrace msyn core).2.2.2.2 := by
              simpa [hreads] using hop
            exact stepCoreTrace_reads_bound (m := msyn) (core := core) op hop'

lemma stepMachineTrace_corelen_one (m : Machine)
    (hcores : m.cores.length = 1) :
    (stepMachineTrace m).1.cores.length = 1 := by
  cases hcs : m.cores with
  | nil =>
      simp [hcs] at hcores
  | cons core rest =>
      cases rest with
      | cons _ _ =>
          simp [hcs] at hcores
      | nil =>
          have hcores' : m.cores = [core] := by simpa [hcs]
          by_cases hab : m.aborted
          · simp [stepMachineTrace, hab, hcores']
          · simp [stepMachineTrace, hab, hcores', List.foldl]
            -- both branches produce a singleton core list
            by_cases h :
                (stepCoreTrace
                        { cores := [core], mem := m.mem, program := m.program, cycle := m.cycle,
                          enable_pause := m.enable_pause, enable_debug := m.enable_debug,
                          value_trace := m.value_trace }
                        core).2.2.2.1 =
                  false <;> simp [h]

lemma runMachineTraceAuxFull_reads_bound_onecore (fuel : Nat) (m : Machine)
    (hcores : m.cores.length = 1) :
    ∀ op ∈ (runMachineTraceAuxFull fuel m).2, op.length ≤ VLEN := by
  induction fuel generalizing m with
  | zero =>
      intro op hop
      simp [runMachineTraceAuxFull] at hop
  | succ fuel ih =>
      intro op hop
      by_cases hrun : !anyRunning m
      · simp [runMachineTraceAuxFull, hrun] at hop
      · -- one step: reads = reads1 ++ reads2
        simp [runMachineTraceAuxFull, hrun] at hop
        rcases hop with hop | hop
        · exact stepMachineTrace_reads_bound_onecore (m := m) hcores op hop
        · -- tail still has one core
          have hcores' : (stepMachineTrace m).1.cores.length = 1 :=
            stepMachineTrace_corelen_one (m := m) hcores
          exact ih (m := (stepMachineTrace m).1) hcores' op hop

lemma readOpsMachineFuel_bound (p : Program) (fuel : Nat) (mem : Memory) :
    ∀ op ∈ readOpsMachineFuel p fuel mem, op.length ≤ VLEN := by
  -- Switch to the "full" runner and apply the one-core bound.
  have hcores : (initMachine p mem).cores.length = 1 := by simp [initMachine, initCore]
  have hbound :=
    runMachineTraceAuxFull_reads_bound_onecore (fuel := fuel) (m := initMachine p mem) hcores
  simpa [readOpsMachineFuel_eq_full] using hbound

lemma loadOps_lower_bound_machineFuel (p : Program) (fuel : Nat) (mem : Memory) :
    minLoadOps (readWordCountMachineFuel p fuel mem) ≤ loadOpCountMachineFuel p fuel mem := by
  have hlen :
      readWordCountMachineFuel p fuel mem ≤ VLEN * loadOpCountMachineFuel p fuel mem := by
    have :=
      length_join_le (readOpsMachineFuel p fuel mem) (readOpsMachineFuel_bound p fuel mem)
    simpa [readWordCountMachineFuel, readWordsMachineFuel, loadOpCountMachineFuel] using this
  -- `minLoadOps words = ceilDiv words VLEN`
  exact ceilDiv_le_of_mul_le (by decide : 0 < VLEN) hlen

theorem loadLowerCycles_readWordCountMachineFuel_le_cycleCountMachineFuel
    (p : Program) (fuel : Nat) (mem : Memory)
    (hnoAbort : (runMachineFinalFuel p fuel mem).aborted = false) :
    ceilDiv (minLoadOps (readWordCountMachineFuel p fuel mem)) LOAD_CAP ≤
      cycleCountMachineFuel p fuel mem := by
  have hmin :
      minLoadOps (readWordCountMachineFuel p fuel mem) ≤ loadOpCountMachineFuel p fuel mem :=
    loadOps_lower_bound_machineFuel p fuel mem
  have hops :
      loadOpCountMachineFuel p fuel mem ≤ LOAD_CAP * cycleCountMachineFuel p fuel mem :=
    loadOpCountMachineFuel_le_cycle p fuel mem hnoAbort
  have hmul :
      minLoadOps (readWordCountMachineFuel p fuel mem) ≤ LOAD_CAP * cycleCountMachineFuel p fuel mem :=
    le_trans hmin hops
  exact ceilDiv_le_of_mul_le (by decide : 0 < LOAD_CAP) hmul

/-!
### `SafeExec` implies "no abort" (straight-line programs)

`CycleLB` currently assumes "no abort" to connect load-op counts to elapsed cycles.
For straight-line programs (no control-flow in `.flow`), the repo's `SafeExec` predicate is
strong enough to show the machine never sets `aborted=true`.
-/

lemma coreEqNoPc_updatePc (c : Core) :
    coreEqNoPc c { c with pc := c.pc + 1 } := by
  unfold coreEqNoPc
  simp

lemma coreEqNoPc_trans {c1 c2 c3 : Core} :
    coreEqNoPc c1 c2 → coreEqNoPc c2 c3 → coreEqNoPc c1 c3 := by
  intro h12 h23
  rcases h12 with ⟨hid12, hscr12, htr12, hst12⟩
  rcases h23 with ⟨hid23, hscr23, htr23, hst23⟩
  exact ⟨hid12.trans hid23, hscr12.trans hscr23, htr12.trans htr23, hst12.trans hst23⟩

theorem runMachineFinalFuel_aborted_false_of_StraightLine_safeExec
    (p : Program) (hstraight : StraightLine p) :
    ∀ mem, SafeExec p mem →
      (runMachineFinalFuel p p.program.length mem).aborted = false := by
  intro mem hsafe
  have hprog_straight : ∀ instr ∈ p.program, instrStraight instr := hstraight
  -- Suffix simulation: if `suf = drop pc p.program` is safe to execute (list-recursive),
  -- then running the singleton machine for `suf.length` steps does not abort.
  have hsim :
      ∀ (mem0 : Memory) (pc : Nat) (suf : List Instruction) (coreS coreM : Core) (mcycle : Nat),
        suf = List.drop pc p.program →
        SafeExecAux suf mem0 coreS →
        coreM.state = .running →
        coreM.pc = Int.ofNat pc →
        coreEqNoPc coreS coreM →
        (runMachineTraceAuxFull suf.length
            { cores := [coreM], mem := mem0, program := p.program, cycle := mcycle,
              enable_pause := false, enable_debug := false, value_trace := fun _ => 0,
              aborted := false }).1.aborted = false := by
    intro mem0 pc suf coreS coreM mcycle hsuf hsafeS hrun hpc hcoreEq
    induction suf generalizing pc coreS coreM mem0 mcycle with
    | nil =>
        simp [runMachineTraceAuxFull]
    | cons instr rest ih =>
        have hget : listGet? p.program pc = some instr := by
          apply listGet?_eq_some_of_drop_eq_cons (l := p.program) (n := pc) (x := instr) (xs := rest)
          simpa [hsuf] using hsuf.symm
        have hrest : rest = List.drop (pc + 1) p.program := by
          calc
            rest = List.drop 1 (instr :: rest) := by simp [List.drop]
            _ = List.drop 1 (List.drop pc p.program) := by simpa [hsuf]
            _ = List.drop (pc + 1) p.program := by
              simpa using (List.drop_drop (l := p.program) (i := 1) (j := pc))
        have hanyTrue :
            anyRunning
                { cores := [coreM], mem := mem0, program := p.program, cycle := mcycle,
                  enable_pause := false, enable_debug := false, value_trace := fun _ => 0,
                  aborted := false } = true := by
          simp [anyRunning, hrun]
        have hany :
            !anyRunning
                { cores := [coreM], mem := mem0, program := p.program, cycle := mcycle,
                  enable_pause := false, enable_debug := false, value_trace := fun _ => 0,
                  aborted := false } = false := by
          simp [hanyTrue]
        have hfetch : fetch p.program coreM.pc = some instr := by
          have : fetch p.program (Int.ofNat pc) = some instr := by
            simp [fetch, hget]
          simpa [hpc] using this
        have hinstr_mem : instr ∈ p.program := by
          have : instr ∈ List.drop pc p.program := by simpa [hsuf.symm]
          exact List.mem_of_mem_drop this
        have hinstr_straight : instrStraight instr := hprog_straight instr hinstr_mem
        -- Unpack safe execution on the head.
        have hs :
            (execInstructionTrace mem0 coreS instr).1.ok = true ∧
              SafeExecAux rest (execInstructionTrace mem0 coreS instr).1.mem
                (execInstructionTrace mem0 coreS instr).1.core := by
          simpa [SafeExecAux] using hsafeS
        have hsok : (execInstructionTrace mem0 coreS instr).1.ok = true := hs.1
        have hsafe_tail :
            SafeExecAux rest (execInstructionTrace mem0 coreS instr).1.mem
              (execInstructionTrace mem0 coreS instr).1.core := hs.2
        -- Machine pre-increments `pc` and uses a syntactic `.running` core record (matches `stepCoreTrace` unfolding).
        let coreM1 : Core :=
          { id := coreM.id, scratch := coreM.scratch, trace_buf := coreM.trace_buf,
            pc := coreM.pc + 1, state := .running }
        have hcoreS_coreM1 : coreEqNoPc coreS coreM1 := by
          have hcoreM_coreM1 : coreEqNoPc coreM coreM1 := by
            unfold coreEqNoPc coreM1
            simp [hrun]
          exact coreEqNoPc_trans hcoreEq hcoreM_coreM1
        have hEq :=
          execInstructionTrace_eq_of_coreEq (mem := mem0) (core1 := coreS) (core2 := coreM1)
            (instr := instr) hinstr_straight hcoreS_coreM1
        have hokM1 : (execInstructionTrace mem0 coreM1 instr).1.ok = true := by
          have : (execInstructionTrace mem0 coreS instr).1.ok =
              (execInstructionTrace mem0 coreM1 instr).1.ok := by
            simpa using hEq.1
          simpa [this] using hsok
        have hmem_eq :
            (execInstructionTrace mem0 coreS instr).1.mem =
              (execInstructionTrace mem0 coreM1 instr).1.mem := by
          simpa using hEq.2.1
        have hcore_eq' :
            coreEqNoPc (execInstructionTrace mem0 coreS instr).1.core
              (execInstructionTrace mem0 coreM1 instr).1.core := by
          simpa using hEq.2.2.1
        have hok_run :
            (execInstruction false false (fun _ => 0) mem0 coreM1 instr).ok = true := by
          simpa [execInstructionTrace] using hokM1
        -- For straight-line, exec preserves state/pc, so the machine keeps running with pc=pc+1.
        have hpc' : (execInstructionTrace mem0 coreM1 instr).1.core.pc = Int.ofNat (pc + 1) := by
          have hpc_pres :=
            (execInstruction_pc_state_eq_of_instrStraight (enablePause := false) (enableDebug := false)
                (valueTrace := fun _ => 0) (mem := mem0) (core := coreM1) (instr := instr)
                hinstr_straight).1
          have hcoreM1_pc : coreM1.pc = Int.ofNat (pc + 1) := by
            simp [coreM1, hpc, int_ofNat_add_one]
          -- `execInstructionTrace` uses the same `execInstruction`.
          simpa [execInstructionTrace, hpc_pres, hcoreM1_pc]
        have hrun' : (execInstructionTrace mem0 coreM1 instr).1.core.state = .running := by
          have hst_pres :=
            (execInstruction_pc_state_eq_of_instrStraight (enablePause := false) (enableDebug := false)
                (valueTrace := fun _ => 0) (mem := mem0) (core := coreM1) (instr := instr)
                hinstr_straight).2
          have : coreM1.state = .running := by rfl
          simpa [execInstructionTrace, hst_pres, this]
        -- Unfold one runner step; the machine does not abort since `ok=true`.
        -- Then apply IH on the tail machine state.
        have htail :
            (runMachineTraceAuxFull rest.length
                (stepMachineTrace
                    { cores := [coreM], mem := mem0, program := p.program, cycle := mcycle,
                      enable_pause := false, enable_debug := false, value_trace := fun _ => 0,
                      aborted := false }).1).1.aborted = false := by
          -- The stepped machine is the non-aborting branch, with updated core/mem.
          -- Rewrite the tail machine into the expected shape and apply IH.
          have hsafe_tail' :
              SafeExecAux rest (execInstructionTrace mem0 coreM1 instr).1.mem
                (execInstructionTrace mem0 coreS instr).1.core := by
            -- only the memory needs rewriting (SafeExec mem = Machine mem)
            simpa [hmem_eq] using hsafe_tail
          have :=
            ih (pc := pc + 1)
              (coreS := (execInstructionTrace mem0 coreS instr).1.core)
              (coreM := (execInstructionTrace mem0 coreM1 instr).1.core)
              (mem0 := (execInstructionTrace mem0 coreM1 instr).1.mem)
              (mcycle :=
                if (execInstructionTrace mem0 coreM1 instr).1.has_non_debug = true then mcycle + 1 else mcycle)
              (by simpa [hrest])
              hsafe_tail'
              (by simpa [hrun'])
              (by simpa [hpc'])
              (by simpa using hcore_eq')
          -- `stepMachineTrace` with singleton core and ok=true produces exactly the machine above.
          simpa [stepMachineTrace, stepCoreTrace, hrun, hfetch, execInstructionTraceMachine,
            execInstructionTrace, coreM1, hok_run] using this
        -- Finish cons-case.
        simpa [runMachineTraceAuxFull, hanyTrue] using htail
  -- Apply the suffix lemma at `pc=0` with the initial machine/core.
  have hinit :
      (runMachineFinalFuel p p.program.length mem).aborted = false := by
    have hsafe0 : SafeExecAux p.program mem (initCore p) := hsafe
    have hrun0 : (initCore p).state = .running := rfl
    have hpc0 : (initCore p).pc = Int.ofNat 0 := by rfl
    have hcoreEq0 : coreEqNoPc (initCore p) (initCore p) := coreEqNoPc_refl (initCore p)
    -- Expand `runMachineFinalFuel` and use the suffix lemma.
    simpa [runMachineFinalFuel, initMachine] using
      hsim (mem0 := mem) (pc := 0) (suf := p.program) (coreS := initCore p) (coreM := initCore p)
        (mcycle := 0) (by simp) hsafe0 hrun0 hpc0 hcoreEq0
  exact hinit

end ProofGlobalLowerBound
