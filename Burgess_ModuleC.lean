import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Data.Complex.BigOperators

/-!
# Module C: Weyl sums and exponential sum estimates

This file contains a minimal, self-contained development of Weyl sums as they
appear in the Burgess bound proof skeleton.

We provide:
* a definition `weyl_sum`;
* basic evaluation lemmas for `N = 0, 1` and a `succ` recursion;
* the trivial bound `‖weyl_sum α N‖ ≤ N` (and the corresponding `Complex.abs` bound);
* a placeholder statement for the Weyl differencing inequality.

The analytic number theory content (Weyl differencing / van der Corput) is left
as `sorry`.
-/

namespace Burgess

section WeylSums

open scoped BigOperators

/-- Weyl sum

`weyl_sum α N = ∑_{n=0}^{N-1} exp(2π i α n)`.

We use an explicit `((...) : ℂ) * I` form so simp can easily see the exponent is
purely imaginary (hence has modulus 1).
-/
def weyl_sum (α : ℝ) (N : ℕ) : ℂ :=
  ∑ n in Finset.range N,
    Complex.exp (((2 * Real.pi * α * (n : ℝ) : ℝ) : ℂ) * Complex.I)

@[simp] lemma weyl_sum_zero (α : ℝ) : weyl_sum α 0 = 0 := by
  simp [weyl_sum]

@[simp] lemma weyl_sum_one (α : ℝ) : weyl_sum α 1 = 1 := by
  simp [weyl_sum]

lemma weyl_sum_succ (α : ℝ) (N : ℕ) :
    weyl_sum α (N + 1) =
      weyl_sum α N + Complex.exp (((2 * Real.pi * α * (N : ℝ) : ℝ) : ℂ) * Complex.I) := by
  -- `Finset.sum_range_succ` is the standard recursion for sums over `range`.
  simp [weyl_sum, Finset.sum_range_succ]

/-- For real `x`, `exp(x * I)` lies on the unit circle. -/
lemma norm_exp_ofReal_mul_I (x : ℝ) :
    ‖Complex.exp (((x : ℂ) * Complex.I))‖ = 1 := by
  -- `‖exp z‖ = Real.exp z.re`, and `((x : ℂ) * I).re = 0` for real `x`.
  simpa [Complex.norm_exp, Complex.mul_I_re]

lemma norm_exp_two_pi_mul_I (t : ℝ) :
    ‖Complex.exp (((2 * Real.pi * t : ℝ) : ℂ) * Complex.I)‖ = 1 := by
  simpa [mul_assoc, mul_comm, mul_left_comm] using
    (norm_exp_ofReal_mul_I (x := 2 * Real.pi * t))

/-- Termwise unit-norm for the Weyl sum summand. -/
lemma norm_weyl_term (α : ℝ) (n : ℕ) :
    ‖Complex.exp (((2 * Real.pi * α * (n : ℝ) : ℝ) : ℂ) * Complex.I)‖ = 1 := by
  -- Reduce to the previous lemma with `t = α * n`.
  simpa [mul_assoc, mul_left_comm, mul_comm] using
    (norm_exp_two_pi_mul_I (t := α * (n : ℝ)))

/-- Trivial bound: the Weyl sum has norm at most `N`.

This is just the triangle inequality plus `‖exp(iθ)‖ = 1`.
-/
theorem norm_weyl_sum_le (α : ℝ) (N : ℕ) : ‖weyl_sum α N‖ ≤ (N : ℝ) := by
  classical
  -- Apply the general lemma `norm_sum_le_of_le`.
  have hterm : ∀ n ∈ Finset.range N,
      ‖Complex.exp (((2 * Real.pi * α * (n : ℝ) : ℝ) : ℂ) * Complex.I)‖ ≤ (1 : ℝ) := by
    intro n hn
    -- Each term has norm exactly 1.
    simpa [norm_weyl_term α n]
  -- Now bound the sum.
  have := norm_sum_le_of_le (s := Finset.range N) (f := fun n : ℕ =>
      Complex.exp (((2 * Real.pi * α * (n : ℝ) : ℝ) : ℂ) * Complex.I))
      (n := fun _ => (1 : ℝ)) hterm
  -- Simplify the right-hand side: `∑ _ in range N, 1 = N`.
  have hsum : (∑ _ in Finset.range N, (1 : ℝ)) = (N : ℝ) := by
    simp
  have h' : ‖∑ n in Finset.range N,
      Complex.exp (((2 * Real.pi * α * (n : ℝ) : ℝ) : ℂ) * Complex.I)‖ ≤ (N : ℝ) := by
    simpa [hsum] using this
  simpa [weyl_sum] using h'

/-- The same trivial bound, but stated using `Complex.abs` instead of `‖·‖`.

Mathlib has `Complex.norm_eq_abs : ‖z‖ = Complex.abs z`.
-/
theorem abs_weyl_sum_le (α : ℝ) (N : ℕ) : Complex.abs (weyl_sum α N) ≤ (N : ℝ) := by
  -- Rewrite `Complex.abs` as a norm.
  simpa [Complex.norm_eq_abs] using (norm_weyl_sum_le α N)

/-- **Weyl differencing inequality** (placeholder).

The statement matches the skeleton in the global prompt. A full proof would
require substantial additional infrastructure (finite differencing identities,
trigonometric bounds, etc.), and is left as future work.
-/
theorem weyl_differencing (α : ℝ) (N H : ℕ) (hH : H ≤ N) :
    Complex.abs (weyl_sum α N) ^ 2 ≤ (N : ℝ) * ((N : ℝ) / (H : ℝ) + 1) +
      2 * ∑ h in Finset.Icc 1 H, ((N - h : ℕ) : ℝ) * ‖Real.cos (2 * Real.pi * α * h)‖ := by
  -- TODO: Formalize Weyl differencing / van der Corput.
  sorry

end WeylSums

end Burgess
