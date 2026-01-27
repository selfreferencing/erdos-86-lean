import Lake
open Lake DSL

package erdos_straus_stage5 where
  -- Increase kernel recursion limit for some number theory simp chains.
  moreServerArgs := #["-K", "2000000"]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "master"

@[default_target]
lean_lib ErdosStraus where
  roots := #[`ErdosStraus]

lean_lib Zeroless where
  roots := #[`Zeroless]

lean_lib Dyachenko where
  roots := #[`Dyachenko]

lean_lib EGZ where
  roots := #[`EGZ]

lean_lib CoveringSystem where
  roots := #[`CoveringSystem]
