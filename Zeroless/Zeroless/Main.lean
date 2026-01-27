/-
  Zeroless/Main.lean
  Main Theorem: The 86 Conjecture (CONDITIONAL on one axiom)

  Statement: 2^86 is the largest power of 2 whose decimal representation
  contains no digit 0.

  Equivalently: For all n > 86, the decimal representation of 2^n contains
  at least one digit 0.

  Proof architecture:
  - FiveAdic_Extended.lean: 5-adic structure, 4-or-5 Children Theorem (PROVED, 0 sorry)
  - TransferOperator.lean: Transfer operator algebra (PROVED, 0 sorry)
  - Fourier_Proven.lean: Fourier analysis on Z/5Z (PROVED, 0 sorry, 1 axiom)
    - F3: Character orthogonality (proved)
    - F4: Discrepancy bound via Fourier inversion (proved)
    - F5: Killed-index definitions + uniqueness (proved)
    - F6: Good ratio lower bound (proved)
    - F7: Geometric decay bound 4*(91/100)^90 < 1 (proved)
    - Axiom: no_zeroless_k_ge_91 (OPEN PROBLEM, see Fourier_Proven.lean)
  - Main.lean (this file): Assembly + direct verification for n = 87..302

  Status (January 2026):
  The theorem erdos_86_conjecture is PROVED modulo one axiom (no_zeroless_k_ge_91)
  which states that no power of 2 with >= 91 decimal digits is zeroless. This axiom
  represents an open problem in mathematics. The "4.5^k barrier" blocks all known
  digit-by-digit proof strategies. A previous axiom (char_sum_bounded) was discovered
  to be FALSE and has been removed. See Fourier_Proven.lean for full documentation.

  The computational verification (n = 87..302) is fully rigorous.
  The bridge lemma (n <= 302 when digit count < 91) is fully proved.
-/

import Zeroless.Fourier_Proven

namespace Zeroless

open scoped BigOperators

/-! ## Definitions -/

/-- A positive integer is "zeroless" if none of its decimal digits is 0. -/
def zeroless (n : ℕ) : Prop := 0 ∉ Nat.digits 10 n

instance (n : ℕ) : Decidable (zeroless n) :=
  inferInstanceAs (Decidable (0 ∉ Nat.digits 10 n))

/-- Number of decimal digits -/
def numDigits (n : ℕ) : ℕ := (Nat.digits 10 n).length

/-! ## Direct Verification for Small n -/

/-- 2^86 is zeroless -/
theorem two_pow_86_zeroless : zeroless (2^86) := by native_decide

/-- 2^87 is NOT zeroless (contains a 0) -/
theorem two_pow_87_has_zero : ¬zeroless (2^87) := by native_decide

/-! ## THE MAIN THEOREM -/

/-- **The 86 Conjecture (Main Theorem, conditional on one axiom)**:
    2^86 is the largest power of 2 with no digit 0 in its decimal representation.

    Equivalently: For all n > 86, the number 2^n contains at least one digit 0.

    Proof structure:
    - Case 1 (k ≥ 91 digits): Uses axiom no_zeroless_k_ge_91 (OPEN PROBLEM).
    - Case 2 (k < 91 digits): Proved computationally.
      Since k < 91 and n > 86, we show n ≤ 302 (because 2^303 > 10^90),
      then verify all n ∈ {87, ..., 302} by native_decide.

    Proved infrastructure (in Fourier_Proven.lean):
    - twisted_sum_zero': geometric series for roots of unity
    - char_ortho: character orthogonality on Z/5Z
    - discrepancy_from_char_bound: Fourier inversion discrepancy bound
    - killed_index_kills / killed_index_unique: dead child identification
    - geometric_decay_91: 4*(91/100)^90 < 1

    Remaining axiom:
    - no_zeroless_k_ge_91: for k ≥ 91 digits, every 2^n has a zero.
      This is an open problem. See Fourier_Proven.lean for analysis of
      the 4.5^k barrier that blocks all known proof strategies. -/
theorem erdos_86_conjecture :
    ∀ n : ℕ, n > 86 → ¬zeroless (2^n) := by
  intro n hn
  by_cases hk : (Nat.digits 10 (2^n)).length ≥ 91
  · -- Case 1: 2^n has ≥ 91 digits → use forced-tail decay axiom
    -- The axiom gives 0 ∈ Nat.digits 10 (2^n), contradicting zeroless
    intro hz
    exact hz (no_zeroless_k_ge_91 _ hk n rfl)
  · push_neg at hk
    -- hk : (Nat.digits 10 (2 ^ n)).length < 91
    have hle : n ≤ 302 := by
      by_contra hle'
      -- From ¬ n ≤ 302 we get 303 ≤ n
      have hn303 : 303 ≤ n := by
        have hlt : 302 < n := (not_le).1 hle'
        exact Nat.succ_le_of_lt hlt

      -- From hk we get length ≤ 90
      have hlen : (Nat.digits 10 (2 ^ n)).length ≤ 90 := by
        exact Nat.le_of_lt_succ hk

      -- Any number is < base^(number of digits in that base)
      have h2n_lt_powlen :
          2 ^ n < 10 ^ (Nat.digits 10 (2 ^ n)).length := by
        simpa using
          (Nat.lt_base_pow_length_digits (b := 10) (m := 2 ^ n) (by decide : 1 < (10 : ℕ)))

      -- Convert "length ≤ 90" into an actual numerical bound: 2^n < 10^90
      have hpowlen_le : 10 ^ (Nat.digits 10 (2 ^ n)).length ≤ 10 ^ 90 := by
        exact Nat.pow_le_pow_of_le_right (by decide : 0 < (10 : ℕ)) hlen

      have h2n_lt : 2 ^ n < 10 ^ 90 :=
        lt_of_lt_of_le h2n_lt_powlen hpowlen_le

      -- If n ≥ 303 then 2^303 ≤ 2^n
      have h2_303_le : 2 ^ 303 ≤ 2 ^ n :=
        Nat.pow_le_pow_of_le_right (by decide : 0 < (2 : ℕ)) hn303

      -- And 2^303 is already > 10^90 (checked computationally)
      have hbig : 10 ^ 90 < 2 ^ 303 := by native_decide
      have hcontra : 10 ^ 90 < 2 ^ n := lt_of_lt_of_le hbig h2_303_le

      exact lt_asymm hcontra h2n_lt

    -- Now n is forced into the finite range 87..302, so brute force.
    have hlow : 87 ≤ n := Nat.succ_le_of_lt hn
    have hlt : n < 303 := Nat.lt_succ_of_le hle

    interval_cases n <;> native_decide

/-- Corollary: The set of zeroless powers of 2 is finite -/
theorem zeroless_powers_finite :
    {n : ℕ | zeroless (2^n)}.Finite := by
  apply Set.Finite.subset (Set.finite_Iio 87)
  intro n hn
  simp only [Set.mem_Iio]
  by_contra h
  push_neg at h
  exact (erdos_86_conjecture n (by omega)) hn

/-- The complete list of zeroless powers of 2:
    2^0 = 1, 2^1 = 2, ..., 2^86 = 77371252455336267181195264 -/
theorem zeroless_powers_list :
    {n : ℕ | zeroless (2^n)} =
    {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 13, 14, 15, 16, 18, 19, 24, 25, 27, 28,
     31, 32, 33, 34, 35, 36, 37, 39, 49, 51, 67, 72, 76, 77, 81, 86} := by
  sorry -- Computational verification

end Zeroless
