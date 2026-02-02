#!/usr/bin/env python3
"""
Generate a symbolic scratch evaluator for baselinePrefix.

Reads proofs/baseline_program/BaselinePrefix.lean and writes:
  proofs/baseline_program/BaselinePrefixSymbolic.lean
"""
from __future__ import annotations

import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
PREFIX = ROOT / "proofs" / "baseline_program" / "BaselinePrefix.lean"
OUT = ROOT / "proofs" / "baseline_program" / "BaselinePrefixSymbolic.lean"


def extract_instrs(lines: list[str]) -> list[str]:
    inside = False
    level = 0
    instrs: list[str] = []
    for line in lines:
        if not inside:
            if line.startswith("def baselinePrefix"):
                if "[" in line:
                    inside = True
                    level += line.count("[") - line.count("]")
                    continue
        else:
            level += line.count("[") - line.count("]")
            if level == 0:
                break
            s = line.strip()
            if s:
                instrs.append(s.rstrip(","))
    if not instrs:
        raise SystemExit("No instructions found in baselinePrefix")
    return instrs


def main() -> None:
    instrs = extract_instrs(PREFIX.read_text().splitlines())
    parsed: list[tuple[str, int, int]] = []
    consts: list[tuple[int, int]] = []
    loads: list[tuple[int, int]] = []
    for inst in instrs:
        m = re.match(r"instrLoad \(LoadSlot\.const (\d+) (\d+)\)", inst)
        if m:
            dest = int(m.group(1))
            val = int(m.group(2))
            parsed.append(("const", dest, val))
            consts.append((dest, val))
            continue
        m = re.match(r"instrLoad \(LoadSlot\.load (\d+) (\d+)\)", inst)
        if m:
            dest = int(m.group(1))
            addr = int(m.group(2))
            parsed.append(("load", dest, addr))
            loads.append((dest, addr))
            continue
        raise SystemExit(f"Unknown instruction: {inst}")

    out: list[str] = []
    out.append("import proofs.baseline_program.BaselinePrefix")
    out.append("import proofs.baseline_program.BaselineStructure")
    out.append("import proofs.global_lower_bound.LowerBound")
    out.append("")
    out.append("open ProofISA")
    out.append("open ProofMachine")
    out.append("open ProofGlobalLowerBound")
    out.append("")
    out.append("/-! Auto-generated symbolic prefix scratch evaluation. -/")
    out.append("def prefixScratch (mem : Memory) : Nat → Nat := by")
    out.append("  let s0 := (initCore baselineProgram).scratch")

    svar = "s0"
    step = 0
    for kind, dest, val in parsed:
        step += 1
        snew = f"s{step}"
        if kind == "const":
            out.append(f"  let {snew} := write {svar} {dest} {val}")
        else:
            out.append(f"  let {snew} := write {svar} {dest} (memAt mem ({svar} {val}))")
        svar = snew

    out.append(f"  exact {svar}")
    out.append("")
    out.append("section")
    out.append("  variable (mem : Memory)")
    for dest, val in consts:
        out.append(f"  @[simp] lemma prefixScratch_const_{dest} : prefixScratch mem {dest} = {val} := by")
        out.append("    simp [prefixScratch, write]")
    for dest, addr in loads:
        out.append(f"  @[simp] lemma prefixScratch_load_{dest} : prefixScratch mem {dest} = memAt mem {addr} := by")
        out.append("    simp [prefixScratch, write]")
    out.append("end")

    OUT.write_text("\n".join(out) + "\n")
    print(f"Wrote {OUT}")


if __name__ == "__main__":
    main()
