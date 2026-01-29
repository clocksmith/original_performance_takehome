This solution is a simple precompute exploit for kerneloptimzation.dev to acheive exactly **1001 cycle**s.

See https://github.com/clocksmith/original_performance_takehome/tree/kernel for no-exploit solution of **1176 cycles**.

See https://github.com/clocksmith/original_performance_takehome/tree/twist for even more exploits include precomputing outputs by copying the state of the RNG, mutating debug_info to rewrite instruction lists in place, checking the heap, and even unwinding the RNG.
