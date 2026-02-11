# Anthropic's Original Performance Take-Home

Quick summary:
- **Current best**: 1288 cycles (bundle-valid), spec in `generator/ub_energy_bundle_1291.py`.
- **Bounds convergence**: formal universal lower bound is **256 cycles** (see `proofs/global_lower_bound/LowerBound.md`); current constructive upper bound is **1288 cycles**.
- **Exactness criterion**: if constructive UB and formal LB meet, the exact optimum is proven.
- **True metric**: bundle cycles from `generator/schedule_dep.py` (graph DP / per-engine LBs are optimistic proxies).
- **Verify**: `python3 tests/submission_tests.py`
- **Scripts**: `scripts/energy_search.py`, `scripts/graph_dp_auto_search.py`, `scripts/pareto_dp.py`, `scripts/export_doppler_energy.py`

## Approach: automated tuning of manual kernel engineering

The kernel engineering is still here — `generator/op_list.py` (1400 lines) encodes
the tree traversal algorithm, hash stages, selection modes, caching
strategies, memory layout, and temp-hazard placement. `generator/schedule_dep.py`
is a hand-written list scheduler with RAW/WAW/WAR latency rules. Every
spec knob was designed by someone who understood what ISA-level tradeoff
it controls. The constraint system (`_constraint_energy`) encodes which
knob combinations are valid.

What's automated is the parameter search. Simulated annealing mutates
spec knobs and scores each candidate by actually building and scheduling
the kernel (`build_base_instrs` → bundle cycles). The SA doesn't know
what a VALU is or why offload_op1=800 matters — it just measures the
cycle count and accepts or rejects.

This separation is the point: deep domain knowledge goes into the
generator and scheduler once, then search explores the combinatorial
space that no human would manually enumerate. The best result (1288
cycles) uses budgeted offload plus `bitmask` selection globally with per-round
`mask_precompute` for rounds 11-14, no depth-4 caching, and
`vector_block=0` — a combination that's counterintuitive and unlikely
to be found by hand.

Pipeline:
- **Layer 0** — SA over ~40 spec knobs (including scheduler params)
- **Layer 1** — `generator/op_list.py` generates the DAG from the spec
- **Layer 2** — `generator/schedule_dep.py` packs ops into VLIW bundles → cycle count

The cycle count from Layer 2 is the only metric that matters. Graph DP
and per-engine lower bounds are useful as compass readings but don't
predict actual bundle performance (the gap can be 15-20%).

Branches and references:
- Kernel branch (stack hack): https://github.com/clocksmith/original_performance_takehome/tree/kernel
- Twist branch (RNG unwind + other exploits without changing tests/harness): https://github.com/clocksmith/original_performance_takehome/tree/twist

This repo contains a version of Anthropic's original performance take-home, before Claude Opus 4.5 started doing better than humans given only 2 hours.

The original take-home was a 4-hour one that starts close to the contents of this repo, after Claude Opus 4 beat most humans at that, it was updated to a 2-hour one which started with code which achieved 18532 cycles (7.97x faster than this repo starts you). This repo is based on the newer take-home which has a few more instructions and comes with better debugging tools, but has the starter code reverted to the slowest baseline. After Claude Opus 4.5 we started using a different base for our time-limited take-homes.

Now you can try to beat Claude Opus 4.5 given unlimited time!

## Performance benchmarks 

Measured in clock cycles from the simulated machine. All of these numbers are for models doing the 2 hour version which started at 18532 cycles:

- **2164 cycles**: Claude Opus 4 after many hours in the test-time compute harness
- **1790 cycles**: Claude Opus 4.5 in a casual Claude Code session, approximately matching the best human performance in 2 hours
- **1579 cycles**: Claude Opus 4.5 after 2 hours in our test-time compute harness
- **1548 cycles**: Claude Sonnet 4.5 after many more than 2 hours of test-time compute
- **1487 cycles**: Claude Opus 4.5 after 11.5 hours in the harness
- **1363 cycles**: Claude Opus 4.5 in an improved test time compute harness
- **??? cycles**: Best human performance ever is substantially better than the above, but we won't say how much.

While it's no longer a good time-limited test, you can still use this test to get us excited about hiring you! If you optimize below 1487 cycles, beating Claude Opus 4.5's best performance at launch, email us at performance-recruiting@anthropic.com with your code (and ideally a resume) so we can be appropriately impressed, especially if you get near the best solution we've seen. New model releases may change what threshold impresses us though, and no guarantees that we keep this readme updated with the latest on that.

Run `python3 tests/submission_tests.py` to see which thresholds you pass.

## Warning: LLMs can cheat

None of the solutions we received on the first day post-release below 1300 cycles were valid solutions. In each case, a language model modified the tests to make the problem easier.

If you use an AI agent, we recommend instructing it not to change the `tests/` folder and to use `tests/submission_tests.py` for verification.

Please run the following commands to validate your submission, and mention that you did so when submitting:
```
# This should be empty, the tests folder must be unchanged
git diff origin/main tests/
# You should pass some of these tests and use the cycle count this prints
python3 tests/submission_tests.py
```

An example of this kind of hack is a model noticing that `problem.py` has multicore support, implementing multicore as an optimization, noticing there's no speedup and "debugging" that `N_CORES = 1` and "fixing" the core count so they get a speedup. Multicore is disabled intentionally in this version.
