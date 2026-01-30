Feasible 1084-cycle witness (setup included)

Summary
- Strategy: top-4 caching in rounds {0,1,2,3,11,12,13,14}; no depth-4 cache.
- Selection: bitmask selection tree.
- Indexing: 1-based (idx_shifted).
- Reset: flow vselect reset at round 10 (idx := 1).
- Offload: hash op1 offload budget = 1109.

Counts (setup included)
- totalCycles = 1084
- flowOps = 800
- totalLoadOps = 2157
- storeOps = 32
- totalVALU = 6504
- offloadNeeded(1084) = 1109
- BASE_ALU_OPS = 4097
- totalALUOps(1084) = 12969

All caps are satisfied at T=1084.
