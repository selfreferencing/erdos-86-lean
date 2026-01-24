import Mathlib.NumberTheory.DirichletCharacter.Basic
import Mathlib.NumberTheory.DirichletCharacter.Bounds
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Finset.Interval

/-!
# Pólya–Vinogradov (Module B for Burgess)

This file isolates the Pólya–Vinogradov inequality needed as an input for the Burgess method.

Mathlib already provides:
* `DirichletCharacter.norm_le_one` : `‖χ a‖ ≤ 1` for any `a : ZMod n`
* `norm_sum_le_of_le` : triangle-inequality style bound for finite sums

We use these to prove a "trivial" bound on character sums with no `sorry`,
and then state the real Pólya–Vinogradov inequality as a TODO lemma.
-/

open scoped BigOperators

namespace Burgess

/-- Character sum over the (closed) interval `Icc M (M+N-1)`, i.e. `[M, M+N)` in ℕ-notation. -/
noncomputable def charSum {q : ℕ} (χ : DirichletCharacter ℂ q) (M N : ℕ) : ℂ :=
  ∑ n ∈ Finset.Icc M (M + N - 1), χ n

/-- Partial sum `∑_{n < N} χ(n)` (implemented as `Finset.range N`). -/
noncomputable def partialSum {q : ℕ} (χ : DirichletCharacter ℂ q) (N : ℕ) : ℂ :=
  ∑ n ∈ Finset.range N, χ n

section TrivialBounds

variable {q : ℕ}

/-- A fully formal trivial bound: the norm of any partial sum is ≤ its length. -/
theorem norm_partialSum_le (χ : DirichletCharacter ℂ q) (N : ℕ) :
    ‖partialSum χ N‖ ≤ (N : ℝ) := by
  classical
  -- Bound each term by 1 using `DirichletCharacter.norm_le_one`.
  have h : ∀ n ∈ Finset.range N, ‖χ n‖ ≤ (1 : ℝ) := by
    intro n _
    exact DirichletCharacter.norm_le_one χ (n : ZMod q)
  -- Apply triangle inequality
  calc ‖partialSum χ N‖
      = ‖∑ n ∈ Finset.range N, χ n‖ := rfl
    _ ≤ ∑ n ∈ Finset.range N, ‖χ n‖ := norm_sum_le _ _
    _ ≤ ∑ _ ∈ Finset.range N, (1 : ℝ) := Finset.sum_le_sum h
    _ = (N : ℝ) := by simp

/-- Same trivial bound for interval sums (length `N`). -/
theorem norm_charSum_le (χ : DirichletCharacter ℂ q) (M N : ℕ) :
    ‖charSum χ M N‖ ≤ (N : ℝ) := by
  classical
  have h : ∀ n ∈ Finset.Icc M (M + N - 1), ‖χ n‖ ≤ (1 : ℝ) := by
    intro n _
    exact DirichletCharacter.norm_le_one χ (n : ZMod q)
  calc ‖charSum χ M N‖
      = ‖∑ n ∈ Finset.Icc M (M + N - 1), χ n‖ := rfl
    _ ≤ ∑ n ∈ Finset.Icc M (M + N - 1), ‖χ n‖ := norm_sum_le _ _
    _ ≤ ∑ _ ∈ Finset.Icc M (M + N - 1), (1 : ℝ) := Finset.sum_le_sum h
    _ = ((Finset.Icc M (M + N - 1)).card : ℝ) := by simp
    _ ≤ (N : ℝ) := by
        -- card(Icc M (M+N-1)) ≤ N
        simp only [Nat.cast_le]
        by_cases hN : N = 0
        · simp [hN]
        · have hpos : N > 0 := Nat.pos_of_ne_zero hN
          have : (Finset.Icc M (M + N - 1)).card = N := by
            rw [Nat.card_Icc]
            omega
          omega

end TrivialBounds

/-
## TODO: Pólya–Vinogradov

Classical statement: for any non-principal Dirichlet character χ mod q,
  max_{M,N} ‖∑_{M ≤ n < M+N} χ(n)‖ ≤ C * √q * log q
for some absolute constant C. (See standard references in analytic number theory.)

For Burgess, you typically want the uniform-constant form below.
-/

/-- Pólya-Vinogradov inequality: For non-principal χ mod q, character sums are O(√q log q).

    Proof strategy (not yet implemented):
    1. Use Gauss sums: express χ(n) via Fourier inversion using τ(χ)
    2. Bound |τ(χ)| = √q for primitive characters
    3. Express interval sums via geometric series of additive characters
    4. Apply harmonic sum bound to get O(log q) factor
    5. Combine: |S(χ)| ≤ |τ(χ)| * O(log q) = O(√q log q)
-/
theorem polya_vinogradov_exists_const :
    ∃ C : ℝ, 0 < C ∧
      ∀ {q : ℕ} (χ : DirichletCharacter ℂ q), χ ≠ 1 →
        ∀ (M N : ℕ), ‖charSum χ M N‖ ≤ C * Real.sqrt (q : ℝ) * Real.log (q : ℝ) := by
  sorry

/-- Alternative form with explicit constant (weaker but sometimes more useful) -/
theorem polya_vinogradov (q : ℕ) (hq : q ≥ 2) (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    (M N : ℕ) :
    ‖charSum χ M N‖ ≤ 2 * Real.sqrt (q : ℝ) * Real.log (q : ℝ) := by
  sorry

end Burgess
