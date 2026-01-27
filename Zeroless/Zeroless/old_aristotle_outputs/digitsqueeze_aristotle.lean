/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: cf24e8fc-351c-4b53-ba86-550e1cc0497d

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>
-/

/-
  Zeroless/DigitSqueeze.lean
  Digit Squeeze Lemma for the 86 Conjecture

  Key result: If 2^n has k digits and is zeroless, then n < 3.322k
  This constrains candidates to a narrow interval of width ~3.32 per digit count.

  Proof uses computational certificate: 10^1000 ≤ 2^3322
-/

import Mathlib


/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

failed to synthesize
  Decidable (Zeroless.zeroless (2 ^ 86))

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
failed to synthesize
  Decidable ¬Zeroless.zeroless (2 ^ 87)

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.-/
namespace Zeroless

/-! ## Basic Definitions -/

/-- Number of decimal digits (Nat.digits is little-endian; length is digit-count) -/
def numDigits (n : ℕ) : ℕ := (Nat.digits 10 n).length

/-- n has no zero digits in base 10 -/
def zeroless (n : ℕ) : Prop := 0 ∉ Nat.digits 10 n

/-- The k-th digit (0-indexed from right) of n -/
def digit (n : ℕ) (k : ℕ) : ℕ := (Nat.digits 10 n).getD k 0

/-! ## 1. Digit Count Bounds -/

/-- 2^n has k digits iff 10^(k-1) ≤ 2^n < 10^k (for k ≥ 1) -/
theorem digit_count_iff (n k : ℕ) (hk : 1 ≤ k) :
    numDigits (2^n) = k ↔ 10^(k-1) ≤ 2^n ∧ 2^n < 10^k := by
  have hb10 : (1 : ℕ) < 10 := by decide
  constructor
  · intro hdigits
    have hlen : (Nat.digits 10 (2^n)).length = k := by
      simpa [numDigits] using hdigits
    have hlt : 2^n < 10^k := by
      have : (Nat.digits 10 (2^n)).length ≤ k := le_of_eq hlen
      exact (Nat.digits_length_le_iff (b := 10) (k := k) hb10 (2^n)).1 (by simpa using this)
    have hklt : k - 1 < k := by
      cases k with
      | zero => cases (Nat.not_succ_le_zero 0 hk)
      | succ k' => simpa using (Nat.lt_succ_self k')
    have hlow : 10^(k-1) ≤ 2^n := by
      have : (k - 1) < (Nat.digits 10 (2^n)).length := by
        simpa [hlen] using hklt
      exact (Nat.lt_digits_length_iff (b := 10) (k := k - 1) hb10 (2^n)).1 (by simpa using this)
    exact ⟨hlow, hlt⟩
  · rintro ⟨hlow, hlt⟩
    have hlen_le : (Nat.digits 10 (2^n)).length ≤ k := by
      exact (Nat.digits_length_le_iff (b := 10) (k := k) hb10 (2^n)).2 hlt
    have hlt_len : (k - 1) < (Nat.digits 10 (2^n)).length := by
      exact (Nat.lt_digits_length_iff (b := 10) (k := k - 1) hb10 (2^n)).2 hlow
    have hk_le_len : k ≤ (Nat.digits 10 (2^n)).length := by
      have : (k - 1).succ ≤ (Nat.digits 10 (2^n)).length := (Nat.succ_le_iff).2 hlt_len
      simpa [Nat.succ_eq_add_one, Nat.sub_add_cancel hk] using this
    have hlen_eq : (Nat.digits 10 (2^n)).length = k := le_antisymm hlen_le hk_le_len
    simpa [numDigits] using hlen_eq

/-! ## 2. Digit Squeeze: Provable Rational Upper Bound -/

/-- Computational certificate: 10^1000 ≤ 2^3322
    This encodes log₂(10) < 3.322 without real analysis -/
private lemma ten_pow_1000_le_two_pow_3322 : (10^1000 : ℕ) ≤ 2^3322 := by
  native_decide

/-- A slightly more general "≤ k digits" squeeze -/
theorem digit_squeeze_le (n k : ℕ) (hk : 1 ≤ k)
    (hdigits : numDigits (2^n) ≤ k) :
    n < k * 3322 / 1000 + 1 := by
  have hb10 : (1 : ℕ) < 10 := by decide

  -- From "≤ k digits" we get 2^n < 10^k
  have hlt10k : 2^n < 10^k := by
    have hlen : (Nat.digits 10 (2^n)).length ≤ k := by
      simpa [numDigits] using hdigits
    exact (Nat.digits_length_le_iff (b := 10) (k := k) hb10 (2^n)).1 (by simpa using hlen)

  -- Raise to 1000: (2^n)^1000 < (10^k)^1000
  have hlt_pow : (2^n)^1000 < (10^k)^1000 := by
    exact pow_lt_pow_left' (n := 1000) (hn := by decide) hlt10k

  -- Rewrite (a^b)^c = a^(b*c)
  have hpow2 : (2^n)^1000 = 2^(n*1000) := by
    simpa using (pow_mul (2 : ℕ) n 1000).symm
  have hpow10 : (10^k)^1000 = 10^(k*1000) := by
    simpa using (pow_mul (10 : ℕ) k 1000).symm
  have hlt' : 2^(n*1000) < 10^(k*1000) := by
    simpa [hpow2, hpow10] using hlt_pow

  -- Scale the certificate 10^1000 ≤ 2^3322 up to exponent k
  have hcert_pow : (10^1000)^k ≤ (2^3322)^k := by
    exact pow_le_pow_left' ten_pow_1000_le_two_pow_3322 k
  have hL : (10^1000)^k = 10^(1000*k) := by
    simpa using (pow_mul (10 : ℕ) 1000 k).symm
  have hR : (2^3322)^k = 2^(3322*k) := by
    simpa using (pow_mul (2 : ℕ) 3322 k).symm
  have hcert' : 10^(k*1000) ≤ 2^(3322*k) := by
    have : 10^(1000*k) ≤ 2^(3322*k) := by
      simpa [hL, hR] using hcert_pow
    simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using this

  -- Combine: 2^(n*1000) < 10^(k*1000) ≤ 2^(3322*k)
  have hpowlt : 2^(n*1000) < 2^(3322*k) := lt_of_lt_of_le hlt' hcert'

  -- Strict monotonicity of t ↦ 2^t gives exponent inequality
  have hmono : StrictMono (fun t : ℕ => (2 : ℕ)^t) := pow_right_strictMono' (a := 2) (ha := by decide)
  have hexp : n*1000 < 3322*k := (hmono.lt_iff_lt).1 hpowlt

  -- Turn exponent inequality into n ≤ (3322*k)/1000
  have hmul_le : n*1000 ≤ 3322*k := le_of_lt hexp
  have hdiv : n ≤ (3322*k)/1000 := (Nat.le_div_iff_mul_le (k := 1000) (x := n) (y := 3322*k) (k0 := by decide)).2 hmul_le
  have hdiv' : n ≤ k*3322/1000 := by
    simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hdiv
  exact Nat.lt_succ_of_le hdiv'

/-- Key lemma: the "zeroless" hypothesis is part of the 86-context -/
theorem digit_squeeze (n k : ℕ) (hk : 1 ≤ k)
    (hdigits : numDigits (2^n) = k) (_hzero : zeroless (2^n)) :
    n < k * 3322 / 1000 + 1 := by
  exact digit_squeeze_le n k hk (le_of_eq hdigits)

/-- Contrapositive: digits must exceed k if n is too large -/
theorem digit_squeeze_contra (n k : ℕ) (hk : 1 ≤ k)
    (hn : n ≥ k * 3322 / 1000 + 1) :
    numDigits (2^n) > k ∨ ¬zeroless (2^n) := by
  left
  have : ¬ numDigits (2^n) ≤ k := by
    intro hle
    have hnlt : n < k * 3322 / 1000 + 1 := digit_squeeze_le n k hk hle
    exact (Nat.not_lt_of_ge hn) hnlt
  exact lt_of_not_ge this

/-! ## 3. Candidate Interval Helpers -/

/-- The candidate interval: all n such that 2^n has exactly k digits -/
def candidateInterval (k : ℕ) : Set ℕ := {n | numDigits (2^n) = k}

theorem candidate_upper_bound (k : ℕ) (hk : 1 ≤ k) :
    ∀ n ∈ candidateInterval k, n < k * 3322 / 1000 + 1 := by
  intro n hn
  exact digit_squeeze_le n k hk (le_of_eq hn)

/-- For k = 27, the upper bound evaluates to 90 -/
theorem candidate_bound_k27 :
    candidateInterval 27 ⊆ {n | 2 ≤ n ∧ n < 90} := by
  intro n hn
  have hk : (1 : ℕ) ≤ 27 := by decide
  have hnlt : n < 27 * 3322 / 1000 + 1 := candidate_upper_bound 27 hk n hn
  have hbd : 27 * 3322 / 1000 + 1 = 90 := by native_decide
  have hnlt90 : n < 90 := by simpa [hbd] using hnlt
  -- If 2^n has 27 digits then 2^n ≥ 10^26 ≥ 4 = 2^2, hence n ≥ 2
  have hlow : (2 : ℕ)^2 ≤ 2^n := by
    have : (4 : ℕ) ≤ 10^26 := by native_decide
    have h10 : 10^26 ≤ 2^n := (digit_count_iff n 27 hk).1 hn |>.1
    have : (4 : ℕ) ≤ 2^n := le_trans this h10
    simpa using this
  have hmono : StrictMono (fun t : ℕ => (2 : ℕ)^t) := pow_right_strictMono' (a := 2) (ha := by decide)
  have hnge2 : 2 ≤ n := (hmono.le_iff_le).1 hlow
  exact ⟨hnge2, hnlt90⟩

/-! ## 4. Sanity Checks / Computations -/

-- The famous value: 2^86 has 26 digits
example : numDigits (2^86) = 26 := by native_decide

-- 2^86 is zeroless (as a Prop)
example : zeroless (2^86) := by native_decide

-- 2^87 has a zero digit
example : ¬ zeroless (2^87) := by native_decide

end Zeroless