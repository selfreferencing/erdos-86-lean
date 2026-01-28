/-
  ErdosStraus/ED2/ThueLemma.lean

  Thue's lemma (pigeonhole version).

  For a prime `p` and `r : ZMod p` with `r ≠ 0`, we build a finite set
  `S = {0,1,...,⌊√(p-1)⌋}` and use the map
    f : S × S → ZMod p,  f(a,b) = a + r*b.
  Since |S×S| > p, pigeonhole gives two distinct pairs with the same image.
  Taking differences yields integers `x,y` with small norm and the desired
  divisibility.

  ## Sorry status
  None (all 4 original sorrys filled by Aristotle/Harmonic).

  Source: GPT skeleton (January 2026), proofs by Aristotle (Harmonic)
-/

import Mathlib.Tactic
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.Fintype.Pigeonhole

open scoped BigOperators

namespace ThueLemma

/-- Thue's lemma: existence of a small nontrivial relation `y ≡ r*x [ZMOD p]`
with `x^2+y^2 ≤ 2*(p-1)`.  We write the congruence as an integer divisibility
statement using `ZMod.intCast_zmod_eq_zero_iff_dvd`.
Proof by Aristotle (Harmonic). -/
theorem thue_lemma
    {p : ℕ} (hp : Nat.Prime p) {r : ZMod p} (hr : r ≠ 0) :
    ∃ x y : ℤ,
      0 < x ^ 2 + y ^ 2 ∧
      x ^ 2 + y ^ 2 ≤ (2 * (p - 1) : ℤ) ∧
      (p : ℤ) ∣ (y - (r.val : ℤ) * x) := by
  classical
  letI : NeZero p := ⟨hp.ne_zero⟩
  let m : ℕ := Nat.sqrt (p - 1)
  let S : Type := Fin (m + 1)
  let f : S × S → ZMod p := fun ab =>
    ((ab.1 : ℕ) : ZMod p) + r * ((ab.2 : ℕ) : ZMod p)
  -- Cardinality inequality: p < (m+1)²
  have hcard : Fintype.card (ZMod p) < Fintype.card (S × S) := by
    have h_p_le_m2_plus_2m : p ≤ m ^ 2 + 2 * m := by
      have h_p_le_m2_plus_2m_plus_1 : p ≤ m ^ 2 + 2 * m + 1 := by
        linarith [Nat.sub_add_cancel hp.pos, Nat.lt_succ_sqrt (p - 1)]
      rcases h_p_le_m2_plus_2m_plus_1.eq_or_lt with h | h
      · exact absurd ⟨m + 1, by linarith⟩ hp.not_isSquare
      · omega
    have h_p_lt_m_plus_1_sq : p < (m + 1) ^ 2 := by linarith
    convert h_p_lt_m_plus_1_sq using 1
    · exact ZMod.card p
    · norm_num [sq]; rw [Fintype.card_fin]
  obtain ⟨ab₁, ab₂, hne, hEq⟩ :=
    Fintype.exists_ne_map_eq_of_card_lt f hcard
  let a₁ : S := ab₁.1
  let b₁ : S := ab₁.2
  let a₂ : S := ab₂.1
  let b₂ : S := ab₂.2
  have hEq' :
      ((a₁ : ℕ) : ZMod p) + r * ((b₁ : ℕ) : ZMod p)
        = ((a₂ : ℕ) : ZMod p) + r * ((b₂ : ℕ) : ZMod p) := by
    simpa [f, a₁, b₁, a₂, b₂] using hEq
  let x : ℤ := (b₁ : ℤ) - (b₂ : ℤ)
  let y : ℤ := (a₂ : ℤ) - (a₁ : ℤ)
  refine ⟨x, y, ?_, ?_, ?_⟩
  · -- Nontriviality: 0 < x² + y²
    have hxy_ne_zero : x ≠ 0 ∨ y ≠ 0 := by
      exact not_and_or.mp fun h => hne <|
        Prod.ext (Fin.ext <| by linarith) (Fin.ext <| by linarith)
    cases hxy_ne_zero <;> positivity
  · -- Size bound: x² + y² ≤ 2*(p-1)
    have h_bounds : 0 ≤ (a₁ : ℤ) ∧ (a₁ : ℤ) ≤ m ∧
        0 ≤ (a₂ : ℤ) ∧ (a₂ : ℤ) ≤ m ∧
        0 ≤ (b₁ : ℤ) ∧ (b₁ : ℤ) ≤ m ∧
        0 ≤ (b₂ : ℤ) ∧ (b₂ : ℤ) ≤ m := by
      exact ⟨Nat.cast_nonneg _, Nat.cast_le.mpr <| Fin.is_le _,
        Nat.cast_nonneg _, Nat.cast_le.mpr <| Fin.is_le _,
        Nat.cast_nonneg _, Nat.cast_le.mpr <| Fin.is_le _,
        Nat.cast_nonneg _, Nat.cast_le.mpr <| Fin.is_le _⟩
    have hm_sq : (m : ℤ) ^ 2 ≤ p - 1 := by
      exact le_tsub_of_add_le_right (by
        norm_cast; linarith [Nat.sqrt_le (p - 1), Nat.sub_add_cancel hp.pos])
    nlinarith only [hm_sq, h_bounds]
  · -- Divisibility: p ∣ (y - r.val * x)
    have hz0 : ((y - (r.val : ℤ) * x : ℤ) : ZMod p) = 0 := by
      simp [y, x]
      linear_combination -hEq'
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd (y - (r.val : ℤ) * x) p).1 hz0

end ThueLemma
