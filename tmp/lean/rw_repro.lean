import proofs.common.Machine

namespace RwRepro

open ProofMachine

variable (enablePause enableDebug : Bool)
variable (valueTrace : Nat → Nat)
variable (mem : Mem) (core : Core) (instr : Instruction)
variable (valu_writes alu_writes : List (Nat × Nat))

-- Demonstrates a robust pattern: `generalize` with `_` avoids brittle matching against `mdata`.
example (hWF : instrWellFormed instr)
    (hdbg :
      (if enableDebug then instr.debug.all (fun slot => execDebugSlot core.scratch valueTrace slot) else true) =
        true)
    (hvalu : execValuSlots core.scratch instr.valu = some valu_writes)
    (halu : execAluSlots core.scratch instr.alu = some alu_writes)
    (hloads :
      List.foldl
          (fun acc slot =>
            match acc, execLoadSlot core.scratch mem slot with
            | some ws, some ws' => some (ws ++ ws')
            | x, x_1 => none)
          (some []) instr.load =
        none) :
    (execInstruction enablePause enableDebug valueTrace mem core instr).core.pc = core.pc := by
  simp (config := { zeta := true }) [execInstruction, hWF, hdbg, hvalu, halu]
  -- Replace the load-fold expression with a name, without having to match the full lambda syntactically.
  generalize hlw : List.foldl _ (some []) instr.load = lw
  -- Transport the explicit `hloads` equation to the new name.
  have hlw_none : lw = none := by
    -- `hlw` is `foldl ... = lw`, so use it to rewrite `hloads`.
    -- Note: rewriting the goal term is brittle; rewriting a hypothesis is fine here.
    -- (We avoid rewriting under the match by doing it at the equation level.)
    -- `simp` can see through `mdata` during `simp` on hypotheses.
    -- First, normalize the LHS of `hloads` to `List.foldl _ (some []) instr.load`.
    -- (This is definitional; `simp` is enough.)
    -- Then rewrite with `hlw`.
    have : List.foldl _ (some []) instr.load = none := by
      simpa using hloads
    -- Now substitute.
    -- We can't `rw` under match reliably; but `rw` on an equation works.
    -- `this` has the same LHS as `hlw`.
    -- From `hlw : LHS = lw` and `this : LHS = none`, conclude `lw = none`.
    -- Do it by transitivity.
    calc
      lw = List.foldl _ (some []) instr.load := by simpa [hlw] using (Eq.symm hlw)
      _ = none := this
  cases lw with
  | none =>
      simp
  | some load_writes =>
      cases hlw_none

end RwRepro

