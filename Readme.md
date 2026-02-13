# Anthropic's Original Performance Take-Home

This repo is a kernel-optimization challenge with two tracks that run together:
- find a better kernel (lower the verified cycle count), and
- prove stronger lower bounds in Lean.

## Current Status
- Best verified upper bound (UB): **1288** cycles.
- Best formal lower bound (LB) milestone in this repo: **272** cycles.
- Current gap: **1016** cycles.

We treat this as a convergence problem: push UB down and push LB up until they meet.

## Simple Process
1. Generate candidate kernels from `generator/`.
2. Score by real bundle cycles from `generator/schedule_dep.py`.
3. Keep only correctness-valid results (`tests/submission_tests.py`).
4. Prove lower-bound theorems in `proofs/`.
5. Reconcile UB vs LB and choose the next experiments.

## Run and Verify
```bash
python3 tests/submission_tests.py
```

## Repository Map
- `generator/`: kernel generation, scheduling, and optimization knobs.
- `scripts/`: search and analysis utilities.
- `proofs/`: Lean lower-bound development.
- `tests/`: correctness checks.

## Proof Notes
- Lower-bound theorems and assumptions are documented in:
  - `proofs/global_lower_bound/LowerBound.md`
- Do not treat heuristic throughput estimates as formal proofs.

## Guardrails
- Do not modify `tests/submission_tests.py` (or other submission tests).
- Do not modify `problem.py` or `frozen_problem.py`.
- In `perf_takehome.py`, only edit `kernel_builder()`.
