import Lake
open Lake DSL

package esc_stage5 where
  -- Use a slightly larger kernel stack if you run into deep simp/ring proofs.
  moreLeanArgs := #[]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.15.0"

@[default_target]
lean_lib ErdosStraus where
  roots := #[`ErdosStraus]
