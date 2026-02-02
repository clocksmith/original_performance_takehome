#!/usr/bin/env python3
"""
Generate a symbolic execution definition for the baseline scalar block.

This reads `blockTemplate` from `proofs/baseline_program/BaselineBlocks.lean`
and emits `proofs/baseline_program/BlockSymbolic.lean`.
"""

from __future__ import annotations

import re
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
BLOCKS = ROOT / "proofs" / "baseline_program" / "BaselineBlocks.lean"
OUT = ROOT / "proofs" / "baseline_program" / "BlockSymbolic.lean"


def extract_block_template(lines: list[str]) -> list[str]:
    capturing = False
    level = 0
    block_lines: list[str] = []
    for line in lines:
        if not capturing:
            if line.startswith("def blockTemplate"):
                if "[" in line:
                    capturing = True
                    for ch in line:
                        if ch == "[":
                            level += 1
                        elif ch == "]":
                            level -= 1
                    continue
        else:
            for ch in line:
                if ch == "[":
                    level += 1
                elif ch == "]":
                    level -= 1
            if level == 0:
                break
            s = line.strip()
            if s:
                block_lines.append(s)
    instrs = [line[:-1] if line.endswith(",") else line for line in block_lines]
    if not instrs:
        raise SystemExit("blockTemplate instructions not found")
    return instrs


def generate_symbolic(instrs: list[str]) -> str:
    smap: dict[int, str] = {}
    svar = "s0"
    memvar = "mem0"
    step = 0
    memstep = 0

    def sexpr(reg: int) -> str:
        return smap.get(reg, f"{svar} {reg}")

    snapshot: list[str] = []
    snapshot.append("def blockTemplateSnapshot (c : Nat) : List Instruction := [")
    for inst in instrs:
        snapshot.append(f"  {inst},")
    snapshot.append("]")
    snapshot.append("")
    snapshot.append("lemma blockTemplateSnapshot_eq (c : Nat) :")
    snapshot.append("    blockTemplateSnapshot c = blockTemplate c := by")
    snapshot.append("  rfl")

    code: list[str] = []
    code.append("def blockSym (s : Nat → Nat) (mem : Memory) (c : Nat) : (Nat → Nat) × Memory := by")
    code.append("  let s0 := s")
    code.append("  let mem0 := mem")

    for inst in instrs:
        if inst.startswith("instrAlu"):
            m = re.match(r"instrAlu AluOp\.([a-z_]+) (\d+) (\d+) (\w+)", inst)
            if not m:
                raise SystemExit(f"alu parse fail: {inst}")
            op, dest, a1, a2 = m.groups()
            dest = int(dest)
            a1 = int(a1)
            if a2.isdigit():
                a2_expr = sexpr(int(a2))
            else:
                # only 'c' appears in blockTemplate
                a2_expr = f"{svar} {a2}"
            expr1 = sexpr(a1)
            expr2 = a2_expr
            expr = f"aluEval AluOp.{op} ({expr1}) ({expr2})"
            step += 1
            snew = f"s{step}"
            code.append(f"  let {snew} := write {svar} {dest} ({expr})")
            svar = snew
            smap[dest] = f"{svar} {dest}"
        elif inst.startswith("instrLoad"):
            m = re.match(r"instrLoad \(LoadSlot\.load (\d+) (\d+)\)", inst)
            if not m:
                raise SystemExit(f"load parse fail: {inst}")
            dest = int(m.group(1))
            addr = int(m.group(2))
            expr = f"memAt {memvar} ({sexpr(addr)})"
            step += 1
            snew = f"s{step}"
            code.append(f"  let {snew} := write {svar} {dest} ({expr})")
            svar = snew
            smap[dest] = f"{svar} {dest}"
        elif inst.startswith("instrStore"):
            m = re.match(r"instrStore \(StoreSlot\.store (\d+) (\d+)\)", inst)
            if not m:
                raise SystemExit(f"store parse fail: {inst}")
            addr = int(m.group(1))
            src = int(m.group(2))
            memstep += 1
            memnew = f"mem{memstep}"
            code.append(f"  let {memnew} := memUpdate {memvar} ({sexpr(addr)}) ({sexpr(src)})")
            memvar = memnew
        elif inst.startswith("instrFlow"):
            if "FlowSlot.select" in inst:
                m = re.match(r"instrFlow \(FlowSlot\.select (\d+) (\d+) (\d+) (\d+)\)", inst)
                if not m:
                    raise SystemExit(f"select parse fail: {inst}")
                dest, cond, a, b = map(int, m.groups())
                expr = f"if {sexpr(cond)} = 0 then {sexpr(b)} else {sexpr(a)}"
                step += 1
                snew = f"s{step}"
                code.append(f"  let {snew} := write {svar} {dest} ({expr})")
                svar = snew
                smap[dest] = f"{svar} {dest}"
            else:
                raise SystemExit(f"unsupported flow: {inst}")
        else:
            raise SystemExit(f"unsupported inst: {inst}")

    code.append(f"  exact ({svar}, {memvar})")

    out: list[str] = []
    out.append("import proofs.baseline_program.BaselineBlocks")
    out.append("import proofs.global_lower_bound.LowerBound")
    out.append("")
    out.append("open ProofISA")
    out.append("open ProofMachine")
    out.append("open ProofGlobalLowerBound")
    out.append("")
    out.extend(snapshot)
    out.append("")
    out.extend(code)
    return "\n".join(out) + "\n"


def main() -> None:
    lines = BLOCKS.read_text().splitlines()
    instrs = extract_block_template(lines)
    OUT.write_text(generate_symbolic(instrs))
    print(f"Wrote {OUT}")


if __name__ == "__main__":
    main()
