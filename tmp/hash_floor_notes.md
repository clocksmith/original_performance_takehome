# Hash Floor / <1000 Cycles Notes (2026-02-10)

## ISA Caps
- VLEN=8
- Per-cycle caps: VALU=6, ALU=12, LOAD=2, STORE=2, FLOW=1
- Offload expansion: 1 vector op -> 8 scalar ALU ops (`generator/offload.py`).

## Structural VALU Lower Bound (Independent Of Selection Style)
For the current kernel semantics with `idx_shifted=True` and the current lowering in `generator/op_list.py`:

- Hash (`myhash`): 12 vector ops per (round,vec)
  - 3 linear stages -> 3 `multiply_add`
  - 3 bitwise stages -> 3*(shift + op1 + op2)
  - Total: `16 * 32 * 12 = 6144` VALU ops

- Index update (rounds r != 10 and r != 15): 2 vector ops per (round,vec)
  - `tmp = val & 1` and `idx = muladd(idx, 2, tmp)`
  - Total: `14 * 32 * 2 = 896` VALU ops

- Node XOR: 1 vector op per (round,vec)
  - `val = val ^ node`
  - Total: `16 * 32 = 512` VALU ops

So: **pre-offload VALU >= 6144 + 896 + 512 = 7552** before setup and before any uncached address adds.

To achieve <1000 cycles via throughput alone you need `VALU <= 6000`, so you must remove at least `1552` VALU ops via either:
- changing the program (fewer ops), and/or
- offloading to ALU.

Offload-only hard ceiling at 1000 cycles (ignoring all other ALU needs):
- ALU slots available = `1000 * 12 = 12000`
- Max offloaded vector ops <= `floor(12000/8)=1500`

This shows: **offload alone cannot reach <1000**, even before counting any required baseline ALU for selection/pointers/etc.

## Measured 1291 Stream Counts
For `generator/ub_energy_bundle_1291.py` final op stream (ordered ops + budgeted `apply_offload_stream`):
- VALU=7045, ALU=11472, LOAD=2157, FLOW=800, STORE=32
- LB components: ceil(7045/6)=1175 (bind), ceil(2157/2)=1079, ceil(11472/12)=956, FLOW=800, ceil(32/2)=16

Hash breakdown in that final stream:
- Hash VALU=6120, Hash ALU=192
- Hash VALU floor there: ceil(6120/6)=1020 cycles

## Superopt Status (scripts/superopt_myhash.py)
Stage minima (2-reg model, width=32, const-pool-target):
- Linear stages (0,2,4): 1-op exists (muladd)
- Bitwise stages (1,3,5): 2-op UNSAT; 3-op exists

Full-hash 11-op attempts:
- CEGIS 11-op (two-reg, restricted) tends to time out at iter 1.
- Random template search (50k attempts) found no 11-op candidate.
- skeleton_11 (delete one op from canonical 12-op skeleton + hill-search consts): best mismatches=1.
- MITM (width 8/10) with plausible 11-op budgets: no candidate found.

Net: evidence suggests 12 ops is very likely minimal for full 32-bit myhash under these ops, but we do not have a complete UNSAT proof for the full 11-op space.
