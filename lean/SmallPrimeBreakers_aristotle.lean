/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 3e791fda-f4e7-4823-b8b7-d80779527a5f

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>
-/

import Mathlib


namespace ErdosStraus

/-- "Non-quadratic residue" in `ZMod n` meaning: not a square. -/
def IsNQR {n : ℕ} (a : ZMod n) : Prop :=
  ¬ IsSquare a

/-- The Type II witness predicate used in the Bradford/Type-II setup. -/
def TypeIIWitness (x m : ℕ) : Prop :=
  ∃ d : ℕ, d ∣ x^2 ∧ d ≤ x ∧ (x + d) % m = 0

/-
  Small-prime computations (decidable because `ZMod n` is finite).
-/

/-- 3 is a non-square mod 31. -/
lemma nqr_3_31 : IsNQR (3 : ZMod 31) := by
  unfold IsNQR
  native_decide

/-- 3 is a non-square mod 79. -/
lemma nqr_3_79 : IsNQR (3 : ZMod 79) := by
  unfold IsNQR
  native_decide

/-- 7 is a non-square mod 23. -/
lemma nqr_7_23 : IsNQR (7 : ZMod 23) := by
  unfold IsNQR
  native_decide

/-- Correction: 5 is actually a square mod 59 (since 8² = 64 ≡ 5). -/
lemma square_5_59 : IsSquare (5 : ZMod 59) := by
  refine ⟨(8 : ZMod 59), ?_⟩
  norm_num

/-- Hence 5 is *not* a non-square mod 59. -/
lemma not_nqr_5_59 : ¬ IsNQR (5 : ZMod 59) := by
  unfold IsNQR
  intro h
  exact h square_5_59

/-- A correct replacement "small-prime NQR" at modulus 59: 11 is a non-square mod 59. -/
lemma nqr_11_59 : IsNQR (11 : ZMod 59) := by
  unfold IsNQR
  native_decide

/-
  Bridge lemma (this is the "key insight" part of your development).
  Mathlib does not contain the Erdős–Straus/Type-II machinery, so we
  package it as a typeclass assumption that your project can instantiate
  with the theorem you already proved.
-/

/-- In your project: if `x` has a prime divisor `q` which is NQR mod `m`,
then a Type II witness exists at modulus `m`. -/
class HasTypeIIWitnessFromNQRFactor : Prop :=
  (witness_of_prime_factor :
    ∀ {x m q : ℕ},
      Nat.Prime m → Nat.Prime q → q ∣ x → IsNQR (q : ZMod m) →
      TypeIIWitness x m)

section Breakers

variable [HasTypeIIWitnessFromNQRFactor]

/-- If 3 ∣ x₇, then (m = 31) has a Type II witness. -/
lemma k7_witness_of_three_divides (x₇ : ℕ) (hx : 0 < x₇) (h3 : 3 ∣ x₇) :
    ∃ d, d ∣ x₇^2 ∧ d ≤ x₇ ∧ (x₇ + d) % 31 = 0 := by
  -- `hx` is unused here, but kept to match your intended signature.
  have hm : Nat.Prime 31 := by decide
  have hq : Nat.Prime 3 := by decide
  simpa [TypeIIWitness] using
    (HasTypeIIWitnessFromNQRFactor.witness_of_prime_factor
      (x := x₇) (m := 31) (q := 3) hm hq h3 nqr_3_31)

/-- If 3 ∣ x₁₉, then (m = 79) has a Type II witness. -/
lemma k19_witness_of_three_divides (x₁₉ : ℕ) (hx : 0 < x₁₉) (h3 : 3 ∣ x₁₉) :
    ∃ d, d ∣ x₁₉^2 ∧ d ≤ x₁₉ ∧ (x₁₉ + d) % 79 = 0 := by
  have hm : Nat.Prime 79 := by decide
  have hq : Nat.Prime 3 := by decide
  simpa [TypeIIWitness] using
    (HasTypeIIWitnessFromNQRFactor.witness_of_prime_factor
      (x := x₁₉) (m := 79) (q := 3) hm hq h3 nqr_3_79)

/-- If 7 ∣ x₅, then (m = 23) has a Type II witness. -/
lemma k5_witness_of_seven_divides (x₅ : ℕ) (hx : 0 < x₅) (h7 : 7 ∣ x₅) :
    ∃ d, d ∣ x₅^2 ∧ d ≤ x₅ ∧ (x₅ + d) % 23 = 0 := by
  have hm : Nat.Prime 23 := by decide
  have hq : Nat.Prime 7 := by decide
  simpa [TypeIIWitness] using
    (HasTypeIIWitnessFromNQRFactor.witness_of_prime_factor
      (x := x₅) (m := 23) (q := 7) hm hq h7 nqr_7_23)

/-
  Corrected version of the "k=14 breaker":
  5 is QR mod 59, so it cannot serve as an NQR breaker.
  Use 11 (or 13) instead.
-/

/-- If 11 ∣ x₁₄, then (m = 59) has a Type II witness. -/
lemma k14_witness_of_eleven_divides (x₁₄ : ℕ) (hx : 0 < x₁₄) (h11 : 11 ∣ x₁₄) :
    ∃ d, d ∣ x₁₄^2 ∧ d ≤ x₁₄ ∧ (x₁₄ + d) % 59 = 0 := by
  have hm : Nat.Prime 59 := by decide
  have hq : Nat.Prime 11 := by decide
  simpa [TypeIIWitness] using
    (HasTypeIIWitnessFromNQRFactor.witness_of_prime_factor
      (x := x₁₄) (m := 59) (q := 11) hm hq h11 nqr_11_59)

end Breakers

end ErdosStraus