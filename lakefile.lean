import Lake
open Lake DSL

package original_performance_takehome

require mathlib from git "https://github.com/leanprover-community/mathlib4" @ "v4.27.0"

lean_lib TakehomeProofs where
  srcDir := "."
  roots := #[`proofs.b1013.LowerBound, `proofs.b1316.LowerBound]
