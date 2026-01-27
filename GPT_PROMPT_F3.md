# Lean 4 Task: Prove `counting_by_characters` (Fourier counting on Fin 5)

## Environment
- **Lean**: `leanprover/lean4:v4.24.0`
- **Mathlib**: commit `f897ebcf72cd16f89ab4577d0c826cd14afaafc7`

## Task

Prove the Fourier counting identity on Fin 5: the number of elements in a Finset with a given function value equals the average plus a correction from character sums. Return only the Lean 4 code.

## What to prove

```lean
import Mathlib

namespace Zeroless

open scoped BigOperators

noncomputable section

/-- A fixed primitive 5th root of unity -/
noncomputable def ω : ℂ := Complex.exp (2 * Real.pi * Complex.I / 5)

/-- ω^5 = 1 -/
theorem omega_pow_five : ω ^ 5 = 1 := by
  simpa [ω] using (Complex.isPrimitiveRoot_exp 5 (by norm_num)).pow_eq_one

/-- For ℓ ≢ 0 (mod 5): ∑_{j=0}^4 ω^{ℓj} = 0 -/
theorem twisted_sum_zero (ℓ : ZMod 5) (hℓ : ℓ ≠ 0) :
    (∑ j : Fin 5, ω ^ (ℓ.val * j.val)) = 0 := by
  sorry -- assumed proved (from TransferOperator.lean)

/-- ∑_{j=0}^4 ω^0 = 5 -/
theorem char_sum_at_zero :
    (∑ j : Fin 5, ω ^ (0 * j.val)) = 5 := by
  simp

/-- CHARACTER ORTHOGONALITY: ∑_{ℓ : Fin 5} ω^{ℓ · (a - b)} = if a = b then 5 else 0.
    Here a, b : Fin 5 and ℓ ranges over ZMod 5. -/
theorem char_ortho (a b : Fin 5) :
    (∑ ℓ : ZMod 5, (ω ^ (ℓ.val * a.val)) * (ω ^ (ℓ.val * b.val))⁻¹) =
      if a = b then 5 else 0 := by
  sorry

end

end Zeroless
```

## Mathematical content

This is the **character orthogonality** relation for the cyclic group Z/5Z.

For any primitive 5th root ω:
∑_{ℓ=0}^{4} ω^{ℓ(a-b)} = 5 if a ≡ b (mod 5), 0 otherwise.

Proof: If a = b, each term is ω^0 = 1, sum = 5.
If a ≠ b, let d = a - b ≠ 0. Then ∑_ℓ ω^{ℓd} = 0 by `twisted_sum_zero` (since ω^d is a nontrivial 5th root).

## Step-by-step proof strategy for `char_ortho`

1. Split on `a = b`:
   - If `a = b`: every term is `ω^{ℓ·0} = 1`, sum = 5.
   - If `a ≠ b`: rewrite as `∑_ℓ ω^{ℓ(a-b)}` and use `twisted_sum_zero`.

2. Key manipulations:
   - `ω^{ℓa} * (ω^{ℓb})⁻¹ = ω^{ℓa} * ω^{-(ℓb)} = ω^{ℓ(a-b)}`
   - For inverse: `(ω^n)⁻¹ = ω^{5-n}` or use `inv_eq_of_mul_eq_one` with `ω^5 = 1`.
   - Actually, since ω ∈ ℂ× and |ω| = 1, `(ω^n)⁻¹ = conj(ω^n) = ω^{-n}`.

3. For the a ≠ b case, need to show `a.val - b.val` (modular) gives a nonzero element of ZMod 5.

## Recommended proof

```lean
theorem char_ortho (a b : Fin 5) :
    (∑ ℓ : ZMod 5, (ω ^ (ℓ.val * a.val)) * (ω ^ (ℓ.val * b.val))⁻¹) =
      if a = b then 5 else 0 := by
  split
  case isTrue hab =>
    subst hab
    simp [mul_inv_cancel₀ (pow_ne_zero _ (by
      simp [ω, Complex.exp_ne_zero]))]
  case isFalse hab =>
    -- Rewrite ω^{ℓa} * (ω^{ℓb})⁻¹ = ω^{ℓ(a-b)}
    -- Use twisted_sum_zero with (a-b) mod 5 ≠ 0
    sorry -- explicit calculation using twisted_sum_zero
```

### Alternative approach (more explicit)

```lean
theorem char_ortho (a b : Fin 5) :
    (∑ ℓ : ZMod 5, (ω ^ (ℓ.val * a.val)) * (ω ^ (ℓ.val * b.val))⁻¹) =
      if a = b then 5 else 0 := by
  -- Key: ω^m * (ω^n)⁻¹ = ω^(m-n) using ω^5=1
  have hω5 : ω ^ 5 = 1 := omega_pow_five
  have hω_ne : ω ≠ 0 := by
    simp [ω, Complex.exp_ne_zero]
  -- Rewrite each term
  conv_lhs =>
    ext ℓ
    rw [← zpow_natCast ω, ← zpow_natCast ω, ← zpow_neg, ← zpow_add]
  -- Now sum is ∑_ℓ ω^{ℓa - ℓb} = ∑_ℓ ω^{ℓ(a-b)}
  sorry -- continue with twisted_sum_zero
```

### Simplest possible approach

Since `Fin 5` has 5 elements and `ZMod 5` has 5 elements, the cleanest approach might be:

```lean
theorem char_ortho (a b : Fin 5) :
    (∑ ℓ : ZMod 5, (ω ^ (ℓ.val * a.val)) * (ω ^ (ℓ.val * b.val))⁻¹) =
      if a = b then 5 else 0 := by
  -- Convert: ω^m * (ω^n)⁻¹ = ω^{m + (5 - n) mod 5 × 5}... too messy
  -- Better: just case-split on all 25 combinations
  fin_cases a <;> fin_cases b <;> simp [ω, mul_comm] <;>
    (try ring_nf) <;> (try norm_num)
  -- If this doesn't close, use native_decide on each
  all_goals sorry
```

Actually, the 25-case approach is fragile. Better to use the algebraic structure.

### Most robust approach

```lean
theorem char_ortho (a b : Fin 5) :
    (∑ ℓ : ZMod 5, (ω ^ (ℓ.val * a.val)) * (ω ^ (ℓ.val * b.val))⁻¹) =
      if a = b then 5 else 0 := by
  -- Step 1: Rewrite product as single power
  have key : ∀ ℓ : ZMod 5,
      ω ^ (ℓ.val * a.val) * (ω ^ (ℓ.val * b.val))⁻¹ =
      ω ^ (ℓ.val * a.val) * ω ^ (5 * ℓ.val - ℓ.val * b.val) := by
    intro ℓ
    -- (ω^n)⁻¹ = ω^{5k - n} for appropriate k
    sorry
  -- Step 2: Use twisted_sum_zero
  sorry
```

## Key difficulty

The main subtlety is handling `(ω^n)⁻¹` cleanly. Since ω^5 = 1:
- `(ω^n)⁻¹ = ω^{5-n}` when `n < 5`
- `(ω^n)⁻¹ = ω^{-n}` using `zpow`
- Or: `ω^a * (ω^b)⁻¹ = ω^{a-b}` using `zpow_sub`

The `zpow` approach is cleanest: work with `ℤ`-powers.

## API pitfalls

1. **`zpow_natCast`**: converts `ω ^ (n : ℕ)` to `ω ^ ((n : ℤ) : ℤ)`.
2. **`zpow_neg`**: `x ^ (-n) = (x ^ n)⁻¹`.
3. **`zpow_add`**: `x ^ (a + b) = x ^ a * x ^ b`.
4. **`Complex.exp_ne_zero`**: `Complex.exp z ≠ 0` for all z.
5. **`twisted_sum_zero`**: already proved in TransferOperator.lean.
6. **`Fin.val` vs `ZMod.val`**: Both give ℕ values in [0,5). They're different types.
7. **`Fintype.sum_congr`**: use to rewrite under `∑`.

## Constraints
- Must compile with Lean 4.24.0 + specified Mathlib
- Return the complete theorem with proof
- May assume `twisted_sum_zero` is available (proved in TransferOperator.lean)
