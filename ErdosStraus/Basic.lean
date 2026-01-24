import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Nat.Factors
import Mathlib.Tactic

namespace ErdosStraus

/-- Cross-multiplied Erdős–Straus Diophantine equation.

`EscEq n x y z` means `4/n = 1/x + 1/y + 1/z` after clearing denominators.
-/
def EscEq (n x y z : ℕ) : Prop :=
  4 * x * y * z = n * (x*y + x*z + y*z)

/-- The Erdős–Straus conjecture predicate. -/
def Conjecture (n : ℕ) : Prop :=
  ∃ x y z : ℕ, 0 < x ∧ 0 < y ∧ 0 < z ∧ EscEq n x y z

/-- The six Mordell-hard residue classes modulo 840.

(We keep this as a simple disjunction for now; a later refactor can use `Finset`.)
-/
def MordellHard (p : ℕ) : Prop :=
  p % 840 = 1 ∨ p % 840 = 121 ∨ p % 840 = 169 ∨ p % 840 = 289 ∨ p % 840 = 361 ∨ p % 840 = 529

/-- For `p ≡ 1 (mod 4)`, `x0 p = ⌈p/4⌉ = (p+3)/4`.

We use this arithmetic definition throughout Stage 5.
-/
def x0 (p : ℕ) : ℕ := (p + 3) / 4

/-- `x = x0 p + k` -/
def x_of (p k : ℕ) : ℕ := x0 p + k

/-- `m = 4x - p` -/
def m_of (p k : ℕ) : ℕ := 4 * (x_of p k) - p

/-- Bradford Type II witness predicate:

`HasBradfordII p k` means there exists `d ∣ x^2` with `d ≤ x` and `d ≡ -x (mod m)`
written as `x + d ≡ 0 (mod m)`.

We include `m ≠ 0` for safety when using `Nat.ModEq`.
-/
def HasBradfordII (p k : ℕ) : Prop :=
  let x := x_of p k
  let m := m_of p k
  m ≠ 0 ∧ ∃ d : ℕ, d ∣ x^2 ∧ d ≤ x ∧ Nat.ModEq m (x + d) 0

end ErdosStraus
