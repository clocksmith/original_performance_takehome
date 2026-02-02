import Lake
open Lake DSL

package original_performance_takehome

require mathlib from git "https://github.com/leanprover-community/mathlib4" @ "v4.27.0"

lean_lib TakehomeProofs where
  srcDir := "."
  roots := #[
    `proofs.common.ISA,
    `proofs.common.Base,
    `proofs.common.Machine,
    `proofs.global_lower_bound.LowerBound,
    `proofs.cache_top4_d4x15_reset_offload_1013.LowerBound,
    `proofs.cache_top4_d4x15_reset_offload_1015_full_window.LowerBound,
    `proofs.cache_top4_d4x15_reset_offload_1016.LowerBound,
    `proofs.loadbound_preload15_uncached_1316.LowerBound
  ]
