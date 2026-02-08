import Lake
open Lake DSL

package «ESCBarrier» where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`autoImplicit, false⟩
  ]

-- Pin to Aristotle-compatible mathlib version (v4.24.0)
require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "f897ebcf72cd16f89ab4577d0c826cd14afaafc7"

@[default_target]
lean_lib «ESCBarrier» where
  globs := #[.submodules `ESCBarrier]
