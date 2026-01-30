Feasible 1227-cycle witness (setup excluded)

Summary
- Strategy: top-4 caching (rounds 0–3, 11–14) + depth-4 caching for X4=15 vectors on round 4.
- Selection: equality-based vselect tree (flow ops only).
- Offload: bitwise op1 stages to ALU as needed.

Counts (setup excluded)
- totalCycles = 1227
- flowOps = 929
- totalLoadOps = 1928
- storeOps = 32
- totalVALU = 8273
- offloadNeeded(1227) = 911
- BASE_ALU_OPS = 7432
- totalALUOps(1227) = 14720

All caps are satisfied at T=1227.
