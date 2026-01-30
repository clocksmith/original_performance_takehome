Feasible 1509-cycle witness (setup included)

Summary
- Strategy: top-4 caching with rounds {0,1,2,11,12,14} (skip rounds 3 and 13), plus depth-4 caching on round 4 for X4=15.
- Selection: equality-based vselect tree.
- Indexing: 1-based (idx_shifted) to drop the +1 in the update.
- Offload: parity op (val & 1) offloaded to ALU (448 ops).

Counts (setup included)
- totalCycles = 1509
- flowOps = 673
- totalLoadOps = 2578
- storeOps = 32
- totalVALU = 7550
- offloadNeeded(1509) = 0
- BASE_ALU_OPS = 8488
- totalALUOps(1509) = 8488

All caps are satisfied at T=1509.
