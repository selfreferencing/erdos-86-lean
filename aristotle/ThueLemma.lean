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
    sorry
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
    sorry
  · -- Sorry 3: Show x² + y² ≤ 2*(p-1).
    -- Since a₁, a₂, b₁, b₂ : Fin(m+1), values are ≤ m.
    -- So |x| ≤ m and |y| ≤ m, hence x² ≤ m² and y² ≤ m².
    -- Thus x² + y² ≤ 2*m². And m² ≤ p-1 by Nat.sqrt_le_self.
    -- Use: Fin.is_lt, Nat.lt_succ_iff, Int.natAbs_le,
    -- sq_le_sq', Nat.sqrt_le'.
    sorry
  · -- Sorry 4: Show (p : ℤ) ∣ (y - r.val * x).
    -- From hEq', rearrange in ZMod p to get
    -- ((y - r.val * x : ℤ) : ZMod p) = 0.
    -- Use: ZMod.natCast_zmod_eq_zero_iff_dvd or
    -- ZMod.intCast_zmod_eq_zero_iff_dvd,
    -- ZMod.natCast_zmod_val, Int.cast_sub, Int.cast_mul.
    have hz0 : ((y - (r.val : ℤ) * x : ℤ) : ZMod p) = 0 := by
      sorry
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd (y - (r.val : ℤ) * x) p).1 hz0
