import Mathlib

namespace ErdosStraus

/-- Cross-multiplied Erdős–Straus equation.

`ES n x y z` means `4/n = 1/x + 1/y + 1/z` after clearing denominators.
We avoid rationals to keep proofs in `ℕ`.
-/
def ES (n x y z : ℕ) : Prop :=
  4 * x * y * z = n * (x * y + x * z + y * z)

/-- A solution exists for `n` (in positive naturals). -/
def HasSolution (n : ℕ) : Prop :=
  ∃ x y z : ℕ, x > 0 ∧ y > 0 ∧ z > 0 ∧ ES n x y z

/-- Convenience: the Bradford `m` parameter. -/
def m (p x : ℕ) : ℕ := 4 * x - p

/-- The Bradford Type II candidate `y`. -/
def bradfordY (p x d : ℕ) : ℕ :=
  p * (x + d) / (m p x)

/-- The Bradford Type II candidate `z`. -/
def bradfordZ (p x d : ℕ) : ℕ :=
  p * (x + x^2 / d) / (m p x)

end ErdosStraus
