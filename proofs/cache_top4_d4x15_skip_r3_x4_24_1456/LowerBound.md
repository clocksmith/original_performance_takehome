Feasible 1456-cycle witness (setup included)

Summary
- Strategy: top-4 caching with rounds {0,1,2,11,12,13,14} (skip round 3), plus depth-4 caching on round 4 for X4=24.
- Selection: equality-based vselect tree.
- Indexing: 1-based (idx_shifted) to drop the +1 in the update.
- Offload: parity op (val & 1) offloaded to ALU (448 ops).

Counts (setup included)
- totalCycles = 1456
- flowOps = 904
- totalLoadOps = 2250
- storeOps = 32
- totalVALU = 7509
- offloadNeeded(1456) = 0
- BASE_ALU_OPS = 10336
- totalALUOps(1456) = 10336

All caps are satisfied at T=1456.
