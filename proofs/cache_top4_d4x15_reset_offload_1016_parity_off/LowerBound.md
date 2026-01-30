Feasible 1312-cycle witness (parity offloaded)

Summary
- Strategy: top-4 caching (rounds 0–3, 11–14) + depth-4 caching for X4=15 vectors on round 4.
- Selection: equality-based vselect tree (flow ops only).
- Parity offload: val & 1 is offloaded to ALU; VALU count matches 7870.

Counts (setup included)
- totalCycles = 1312
- flowOps = 993
- totalLoadOps = 2065
- storeOps = 32
- totalVALU = 7870
- totalALUOps = 11047

All caps are satisfied at T=1312.
