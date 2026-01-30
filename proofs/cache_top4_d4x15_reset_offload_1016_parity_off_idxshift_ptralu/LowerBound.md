Feasible 1645-cycle witness (parity offload + idx shift + ALU pointer setup)

Summary
- Strategy: top-4 caching (rounds 0–3, 11–14) + depth-4 caching for X4=15 vectors on round 4.
- Selection: equality-based vselect tree (flow ops only).
- Indexing: internal 1-based indices (idx_shifted) with forest base pointer bias.
- Pointer setup: ALU (flow setup removed).
- Parity offload: val & 1 is offloaded to ALU; VALU count matches 7486.

Counts (setup included)
- totalCycles = 1645
- flowOps = 929
- totalLoadOps = 2066
- storeOps = 32
- totalVALU = 7486
- totalALUOps = 11112

All caps are satisfied at T=1645.
