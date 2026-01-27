import Mathlib

/-!
# Dyachenko ED2 Parameter Existence

The core number-theory theorem: for every prime p ≡ 1 (mod 4), there exist
A, α, b', c' with:
  - A in the window [(p+3)/4, (3p-3)/4]
  - A = α * b' * c'
  - (4A - p) ∣ (b' + c')

## Available Mathlib facts

- `Nat.Prime.sq_add_sq`: p ≡ 1 (mod 4) → ∃ a b, a² + b² = p
- `ZMod.exists_sq_eq_neg_one_iff`: -1 is a square in ZMod p iff p % 4 ≠ 3
- `Fintype.exists_ne_map_eq_of_card_lt`: pigeonhole principle
- Standard divisibility, gcd, and modular arithmetic from Mathlib

## Proved infrastructure (stated as axioms here)

The ED2 window lemma (Dyachenko Proposition 9.25): any g × g rectangle
in ℤ² contains a point of the kernel lattice L = {(u,v) : g ∣ u*b' + v*c'}.
-/

/-- Window lemma: a g×g rectangle contains a kernel lattice point.
    This is proved in WindowLattice.lean; stated here as axiom for context. -/
axiom ed2_window_lemma
    (g : ℕ) (hg : 0 < g)
    (b' c' : ℤ)
    (H W : ℕ) (hH : g ≤ H) (hW : g ≤ W)
    (u₀ v₀ : ℤ) :
    ∃ u v : ℤ,
      u₀ ≤ u ∧ u < u₀ + H ∧
      v₀ ≤ v ∧ v < v₀ + W ∧
      (g : ℤ) ∣ (u * b' + v * c')

/-- The core existence theorem.

    For every prime p ≡ 1 (mod 4), there exist A in the window and a
    factorization A = α*b'*c' such that (4A - p) divides (b' + c').

    This implies the Erdos-Straus conjecture for p via the construction
    d = α*b'², which gives d ∣ A² and (4A-p) ∣ (d+A).

    Possible proof routes:
    1. Use Fermat two-square p = a²+b² to build A and factor it so that
       the sum condition holds for some choice of α.
    2. Use ed2_window_lemma with the lattice density argument from
       Dyachenko Section 9: choose A, set g = 4A-p, apply the window
       lemma to find (u,v) with g ∣ (u*1 + v*1) = u+v, then decode
       (u,v) into b', c' with A = α*b'*c'.
    3. Counting/pigeonhole over the A-window: the window has width
       (p-3)/2, and for each A, divisors of A give multiple factorizations
       to try.
-/
theorem dyachenko_ed2_params
    (p : ℕ) (hp : Nat.Prime p) (hp4 : p % 4 = 1) :
    ∃ A α d' b' c' : ℕ,
      (p + 3) / 4 ≤ A ∧
      A ≤ (3 * p - 3) / 4 ∧
      0 < α ∧ 0 < b' ∧
      A = α * b' * c' ∧
      (4 * A - p) ∣ (b' + c') := by
  sorry
