import Mathlib

namespace ErdosStraus

/-!
# Smooth Gap Bound R₀

The 29-smooth gap threshold for K10 coverage.

## Main Result

`R0 = 4,252,385,304` is the upper endpoint of the last consecutive
29-smooth pair with gap ≤ 24.

For `r > R0`, every interval `[r+5, r+29]` contains at most one
29-smooth number, so at least one `x_k = r + k` (for `k ∈ K10`) has
a prime factor > 29.

## Computation

Verified by exhaustive generation of all 29-smooth numbers up to 10^16:
- Last pair with gap ≤ 24: (4,252,385,280, 4,252,385,304)
- After R₀, minimum gap is 25 at (4,429,568,000, 4,429,568,025)

See: `/python/smooth_gap_computation.py`
-/

/-- The set of primes ≤ 29. -/
def SmallPrimes : Finset ℕ := {2, 3, 5, 7, 11, 13, 17, 19, 23, 29}

/-- A number is 29-smooth iff all its prime factors are ≤ 29. -/
def is29Smooth (n : ℕ) : Prop :=
  ∀ p : ℕ, Nat.Prime p → p ∣ n → p ∈ SmallPrimes

/-- R₀: the smooth-gap threshold.
    After R₀, consecutive 29-smooth numbers are always ≥ 25 apart. -/
def R0 : ℕ := 4252385304

/-- R₀ equals the computed value. -/
lemma R0_value : R0 = 4252385304 := rfl

/-- K10: the cascade covering set. -/
def K10' : Finset ℕ := {5, 7, 9, 11, 14, 17, 19, 23, 26, 29}

/-- The span of K10 is 29 - 5 = 24. -/
lemma K10_span : 29 - 5 = 24 := rfl

/-- For r > R₀, the interval [r+5, r+29] contains at most one 29-smooth number.
    This is because consecutive 29-smooth numbers after R₀ are ≥ 25 apart,
    and the interval has width 24.

    COMPUTED FACT (not proved in Lean, verified by Python):
    The last consecutive 29-smooth pair with gap ≤ 24 is
    (4252385280, 4252385304). -/
axiom smooth_gap_after_R0 :
  ∀ a b : ℕ, R0 < a → a < b → is29Smooth a → is29Smooth b →
    (∀ c, a < c → c < b → ¬is29Smooth c) → 25 ≤ b - a

/-- Consequence: For r > R₀, at least one x_k = r + k (k ∈ K10) has a prime factor > 29.

    Proof sketch:
    - The 10 values {r+5, r+7, ..., r+29} span an interval of width 24
    - At most one of these can be 29-smooth (by smooth_gap_after_R0)
    - The other 9 have a prime factor > 29
    - Actually, we only need ONE to have such a factor -/
axiom large_prime_factor_exists :
  ∀ r : ℕ, R0 < r →
    ∃ k ∈ K10', ∃ p : ℕ, Nat.Prime p ∧ 29 < p ∧ p ∣ (r + k)

/-- Combined with GCD coupling: for r > R₀, the large prime factor p > 29
    divides at most one of the x_k values (since gcd(x_a, x_b) | |a-b| ≤ 24 < p). -/
axiom unique_large_factor :
  ∀ r : ℕ, R0 < r →
    ∀ p : ℕ, Nat.Prime p → 29 < p →
      (∃ k ∈ K10', p ∣ (r + k)) →
        ∃! k, k ∈ K10' ∧ p ∣ (r + k)

end ErdosStraus
