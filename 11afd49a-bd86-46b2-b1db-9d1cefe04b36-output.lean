/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 11afd49a-bd86-46b2-b1db-9d1cefe04b36

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem thue_lemma
    {p : ℕ} (hp : Nat.Prime p) {r : ZMod p} (hr : r ≠ 0) :
    ∃ x y : ℤ,
      0 < x ^ 2 + y ^ 2 ∧
      x ^ 2 + y ^ 2 ≤ (2 * (p - 1) : ℤ) ∧
      (p : ℤ) ∣ (y - (r.val : ℤ) * x)
-/

import Mathlib


open scoped BigOperators

/-!
# Thue's Lemma (Pigeonhole Version)

For a prime `p` and `r : ZMod p` with `r ≠ 0`, there exist integers `x, y`
with `0 < x² + y²`, `x² + y² ≤ 2(p-1)`, and `p ∣ (y - r.val * x)`.

Proof sketch: Let `m = √(p-1)`, `S = Fin(m+1)`. The map `f(a,b) = a + r*b`
from `S × S → ZMod p` has `|S×S| = (m+1)² > p` (since a prime is not a
perfect square), so pigeonhole gives a collision. Taking differences gives
the result.

There are 4 sorrys to fill.
-/

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
  -- Sorry 1: Cardinality inequality for pigeonhole.
  -- Need: p < (m+1)², i.e., a prime cannot be a perfect square,
  -- and Nat.sqrt gives (m+1)² ≥ p.
  -- Use: ZMod.card p = p, Fintype.card_prod, Fintype.card_fin,
  -- Nat.lt_succ_sqrt_self or Nat.succ_le_succ_sqrt, and
  -- Nat.Prime.not_sq (a prime is not a perfect square).
  have hcard : Fintype.card (ZMod p) < Fintype.card (S × S) := by
    -- Since $p$ is a prime number, we know that $p \leq m^2 + 2m$ where $m = \sqrt{p-1}$.
    have h_p_le_m2_plus_2m : p ≤ m^2 + 2 * m := by
      -- Since $p$ is a prime number, we know that $p \leq m^2 + 2m + 1$ where $m = \sqrt{p-1}$.
      have h_p_le_m2_plus_2m_plus_1 : p ≤ m^2 + 2 * m + 1 := by
        linarith [ Nat.sub_add_cancel hp.pos, Nat.lt_succ_sqrt ( p - 1 ) ];
      cases h_p_le_m2_plus_2m_plus_1.eq_or_lt <;> simp_all +decide [ Nat.pow_succ' ];
      · exact hp.not_isSquare <| ⟨ m + 1, by linarith ⟩;
      · linarith [ Nat.sub_add_cancel hp.pos ];
    -- Since $p$ is a prime number, we know that $p \leq m^2 + 2m$ where $m = \sqrt{p-1}$. Therefore, $p < (m+1)^2$.
    have h_p_lt_m_plus_1_sq : p < (m + 1) ^ 2 := by
      linarith;
    convert h_p_lt_m_plus_1_sq using 1;
    · exact ZMod.card p;
    · norm_num [ sq ];
      rw [ Fintype.card_fin ]
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
  · -- Sorry 2: Show 0 < x² + y² (nontriviality).
    -- From hne : ab₁ ≠ ab₂, get a₁ ≠ a₂ ∨ b₁ ≠ b₂.
    -- Then x ≠ 0 ∨ y ≠ 0, so x² + y² > 0.
    -- Use: Prod.mk.inj_iff, sub_eq_zero, sq_nonneg.
    -- Since $a_1 \neq a_2$ or $b_1 \neq b_2$, we have $x \neq 0$ or $y \neq 0$.
    have hxy_ne_zero : x ≠ 0 ∨ y ≠ 0 := by
      exact not_and_or.mp fun h => hne <| Prod.ext ( Fin.ext <| by linarith ) ( Fin.ext <| by linarith ) ;
    cases hxy_ne_zero <;> positivity
  · -- Sorry 3: Show x² + y² ≤ 2*(p-1).
    -- Since a₁, a₂, b₁, b₂ : Fin(m+1), values are ≤ m.
    -- So |x| ≤ m and |y| ≤ m, hence x² ≤ m² and y² ≤ m².
    -- Thus x² + y² ≤ 2*m². And m² ≤ p-1 by Nat.sqrt_le_self.
    -- Use: Fin.is_lt, Nat.lt_succ_iff, Int.natAbs_le,
    -- sq_le_sq', Nat.sqrt_le'.
    -- Since $a₁, a₂, b₁, b₂ \in \{0, 1, 2, \ldots, m\}$, we have $0 \leq a₁, a₂, b₁, b₂ \leq m$.
    have h_bounds : 0 ≤ (a₁ : ℤ) ∧ (a₁ : ℤ) ≤ m ∧ 0 ≤ (a₂ : ℤ) ∧ (a₂ : ℤ) ≤ m ∧ 0 ≤ (b₁ : ℤ) ∧ (b₁ : ℤ) ≤ m ∧ 0 ≤ (b₂ : ℤ) ∧ (b₂ : ℤ) ≤ m := by
      exact ⟨ Nat.cast_nonneg _, Nat.cast_le.mpr <| Fin.is_le _, Nat.cast_nonneg _, Nat.cast_le.mpr <| Fin.is_le _, Nat.cast_nonneg _, Nat.cast_le.mpr <| Fin.is_le _, Nat.cast_nonneg _, Nat.cast_le.mpr <| Fin.is_le _ ⟩;
    -- Since $m = \lfloor \sqrt{p-1} \rfloor$, we have $m^2 \leq p-1$.
    have hm_sq : (m : ℤ)^2 ≤ p - 1 := by
      exact le_tsub_of_add_le_right ( by norm_cast; linarith [ Nat.sqrt_le ( p - 1 ), Nat.sub_add_cancel hp.pos ] );
    nlinarith only [ hm_sq, h_bounds ]
  · -- Sorry 4: Show (p : ℤ) ∣ (y - r.val * x).
    -- From hEq', rearrange in ZMod p to get
    -- ((y - r.val * x : ℤ) : ZMod p) = 0.
    -- Use: ZMod.natCast_zmod_eq_zero_iff_dvd or
    -- ZMod.intCast_zmod_eq_zero_iff_dvd,
    -- ZMod.natCast_zmod_val, Int.cast_sub, Int.cast_mul.
    have hz0 : ((y - (r.val : ℤ) * x : ℤ) : ZMod p) = 0 := by
      -- Substitute the definitions of y and x into the expression.
      simp [y, x];
      -- Rearrange hEq' to get the desired equality.
      linear_combination -hEq'
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd (y - (r.val : ℤ) * x) p).1 hz0