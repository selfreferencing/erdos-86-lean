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
  4 sorrys remaining:
  1. `hcard` — cardinality inequality p < (m+1)^2
  2. `?pos` — nontriviality 0 < x^2 + y^2
  3. `?bound` — size bound x^2 + y^2 ≤ 2*(p-1)
  4. `hz0` — ZMod algebra for divisibility

  Source: GPT skeleton (January 2026, Part 5 of Dyachenko formalization)
-/

import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.Fintype.Pigeonhole

open scoped BigOperators

namespace ThueLemma

/-- Thue's lemma: existence of a small nontrivial relation `y ≡ r*x [ZMOD p]`
with `x^2+y^2 ≤ 2*(p-1)`.  We write the congruence as an integer divisibility
statement using `ZMod.intCast_zmod_eq_zero_iff_dvd`. -/
theorem thue_lemma
    {p : ℕ} (hp : Nat.Prime p) {r : ZMod p} (hr : r ≠ 0) :
    ∃ x y : ℤ,
      0 < x^2 + y^2 ∧
      x^2 + y^2 ≤ (2 * (p - 1) : ℤ) ∧
      (p : ℤ) ∣ (y - (r.val : ℤ) * x) := by
  classical
  -- `ZMod p` is finite only when `p ≠ 0`.
  letI : NeZero p := ⟨hp.ne_zero⟩

  -- Let `m = ⌊√(p-1)⌋` and `S = {0,1,...,m}` as `Fin (m+1)`.
  let m : ℕ := Nat.sqrt (p - 1)
  let S : Type := Fin (m + 1)

  -- Define the map `f(a,b) = a + r*b`.
  let f : S × S → ZMod p := fun ab =>
    ((ab.1 : ℕ) : ZMod p) + r * ((ab.2 : ℕ) : ZMod p)

  -- Cardinality inequality for pigeonhole: `card (ZMod p) < card (S×S)`.
  have hcard : Fintype.card (ZMod p) < Fintype.card (S × S) := by
    -- Rewrite cards using the provided API:
    --   * `ZMod.card` : `Fintype.card (ZMod p) = p`
    --   * `Fintype.card_prod` and `Fintype.card_fin` : `card (S×S) = (m+1)*(m+1)`
    --
    -- So it suffices to prove `p < (m+1)^2`.
    --
    -- Suggested route:
    -- 1. From `Nat.succ_le_succ_sqrt' (p-1)` get
    --        p = (p-1)+1 ≤ ((p-1).sqrt + 1)^2 = (m+1)^2.
    -- 2. Rule out equality `p = (m+1)^2` using primality: a prime can't be a
    --    nontrivial square (if `p = k*k` with `k>1`, then `k ∣ p` and `k ≠ 1,p`).
    --
    -- Finally use simp:
    --   `simp [S, ZMod.card, Fintype.card_prod]` to turn it into a nat inequality.
    sorry

  -- Apply the pigeonhole principle.
  obtain ⟨ab₁, ab₂, hne, hEq⟩ :=
    Fintype.exists_ne_map_eq_of_card_lt f hcard

  -- Name components.
  let a₁ : S := ab₁.1
  let b₁ : S := ab₁.2
  let a₂ : S := ab₂.1
  let b₂ : S := ab₂.2

  have hEq' :
      ((a₁ : ℕ) : ZMod p) + r * ((b₁ : ℕ) : ZMod p)
        = ((a₂ : ℕ) : ZMod p) + r * ((b₂ : ℕ) : ZMod p) := by
    simpa [f, a₁, b₁, a₂, b₂] using hEq

  -- Define the integer differences.
  -- From `a₁ + r*b₁ = a₂ + r*b₂` we get `a₂ - a₁ = r*(b₁ - b₂)`, i.e. `y = r*x`.
  let x : ℤ := (b₁ : ℤ) - (b₂ : ℤ)
  let y : ℤ := (a₂ : ℤ) - (a₁ : ℤ)

  refine ⟨x, y, ?pos, ?bound, ?dvd⟩

  · -- Show `0 < x^2 + y^2` (nontriviality).
    --
    -- From `hne : ab₁ ≠ ab₂`, deduce `(a₁ ≠ a₂) ∨ (b₁ ≠ b₂)`.
    -- Then show `x ≠ 0 ∨ y ≠ 0` by rewriting `x=0` as `b₁=b₂` and `y=0` as `a₁=a₂`.
    -- Finally use that squares are nonneg and sum of squares is zero iff both are zero.
    --
    -- Useful facts:
    -- * `Prod.ext` / `Prod.mk.inj_iff` to unpack `hne`.
    -- * `sub_eq_zero` to turn `x = 0` into `b₁ = b₂` (after coercions).
    -- * `sq_nonneg`, `add_eq_zero_iff` style lemmas for `Int`.
    sorry

  · -- Show the size bound: `x^2 + y^2 ≤ 2*(p-1)`.
    --
    -- Main subgoals:
    -- 1. Because `a₁ a₂ b₁ b₂ : Fin (m+1)`, we have `(aᵢ : ℕ) ≤ m` and `(bᵢ : ℕ) ≤ m`.
    --    (`Fin.is_lt` gives `< m+1`; turn into `≤ m` by `Nat.lt_succ_iff`.)
    -- 2. Deduce `|x| ≤ m` and `|y| ≤ m` for `x = b₁-b₂`, `y = a₂-a₁` in `ℤ`.
    -- 3. Conclude `x^2 ≤ m^2`, `y^2 ≤ m^2`, hence `x^2+y^2 ≤ 2*m^2`.
    -- 4. Use `Nat.sqrt_le' (p-1)` to get `m^2 ≤ (p-1)` and finish.
    --
    -- Converting nat bounds to int bounds:
    -- `Int.ofNat_le`, `Int.ofNat_natAbs`, or `zify`/`norm_cast`.
    sorry

  · -- Show the divisibility: `p ∣ (y - r*x)` (with `r` represented by `r.val`).
    --
    -- Strategy:
    -- 1. From `hEq'` rearrange in `ZMod p` to get
    --      ((y : ℤ) : ZMod p) - ((r.val : ℤ) : ZMod p) * ((x : ℤ) : ZMod p) = 0.
    -- 2. Rewrite that as `((y - (r.val:ℤ)*x : ℤ) : ZMod p) = 0` using
    --    `Int.cast_sub`, `Int.cast_mul`.
    -- 3. Convert to divisibility via `ZMod.intCast_zmod_eq_zero_iff_dvd`.
    have hz0 : ((y - (r.val : ℤ) * x : ℤ) : ZMod p) = 0 := by
      -- After rewriting `hEq'` as `... - ... = 0`, use `simp [x, y]` and
      -- `ZMod.natCast_zmod_val` to replace `r` by `r.val`.
      sorry
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd (y - (r.val : ℤ) * x) p).1 hz0

end ThueLemma
