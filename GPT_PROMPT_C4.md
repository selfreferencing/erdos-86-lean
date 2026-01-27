# Lean 4 Task: Prove `ne_zero_iff_cast_ne_zero` (nonzero small nat iff nonzero in ZMod 5)

## Environment
- **Lean**: `leanprover/lean4:v4.24.0`
- **Mathlib**: commit `f897ebcf72cd16f89ab4577d0c826cd14afaafc7`

## Task

Prove that for `b : ℕ` with `b < 5`, `b ≠ 0 ↔ (b : ZMod 5) ≠ 0`. This connects the natural number condition to the `ZMod 5` condition. Return only the Lean 4 code.

## What to prove

```lean
import Mathlib

lemma ne_zero_iff_cast_ne_zero (b : ℕ) (hb : b < 5) :
    b ≠ 0 ↔ (b : ZMod 5) ≠ 0 := by
  sorry
```

## Mathematical content

Since `b < 5`, casting `b` to `ZMod 5` and checking if it's zero is the same as checking if `b = 0` in `ℕ`. This is because `(b : ZMod 5) = 0 ↔ 5 ∣ b` (by `ZMod.natCast_zmod_eq_zero_iff_dvd`), and when `b < 5`, `5 ∣ b ↔ b = 0`.

## Step-by-step proof strategy

1. Use `ZMod.natCast_zmod_eq_zero_iff_dvd` to get `(b : ZMod 5) = 0 ↔ 5 ∣ b`.
2. Show `5 ∣ b ↔ b = 0` using `hb : b < 5`:
   - Forward: if `5 ∣ b` and `b < 5` then `b = 0` (by `Nat.eq_zero_of_dvd_of_lt` or `omega`)
   - Backward: if `b = 0` then `5 ∣ 0` trivially.
3. Combine to get `(b : ZMod 5) = 0 ↔ b = 0`, then negate both sides.

## Useful Mathlib lemmas

- `ZMod.natCast_zmod_eq_zero_iff_dvd` : `((x : ℕ) : ZMod n) = 0 ↔ n ∣ x`
- `Nat.eq_zero_of_dvd_of_lt` : `n ∣ m → m < n → m = 0` (if it exists)
- `Nat.le_of_dvd` : `0 < m → n ∣ m → n ≤ m`
- `not_congr` : converts `(A ↔ B) → (¬A ↔ ¬B)`

## Recommended proof

```lean
lemma ne_zero_iff_cast_ne_zero (b : ℕ) (hb : b < 5) :
    b ≠ 0 ↔ (b : ZMod 5) ≠ 0 := by
  rw [not_iff_not.symm.mpr (ZMod.natCast_zmod_eq_zero_iff_dvd b 5)]
  -- Now: b ≠ 0 ↔ ¬(5 ∣ b)
  push_neg
  -- Now: b = 0 ↔ 5 ∣ b  (negated form, or we work with the original)
  sorry -- fill in
```

Actually, a cleaner approach:

```lean
lemma ne_zero_iff_cast_ne_zero (b : ℕ) (hb : b < 5) :
    b ≠ 0 ↔ (b : ZMod 5) ≠ 0 := by
  constructor
  · intro hne habs
    rw [ZMod.natCast_zmod_eq_zero_iff_dvd] at habs
    -- habs : 5 ∣ b
    -- From hb : b < 5, this forces b = 0
    omega
  · intro hne habs
    subst habs
    simp at hne
```

Or even simpler with `not_congr`:

```lean
lemma ne_zero_iff_cast_ne_zero (b : ℕ) (hb : b < 5) :
    b ≠ 0 ↔ (b : ZMod 5) ≠ 0 := by
  have key : (b : ZMod 5) = 0 ↔ b = 0 := by
    rw [ZMod.natCast_zmod_eq_zero_iff_dvd]
    constructor
    · intro h; omega
    · intro h; subst h; simp
  exact key.not.symm
```

Or the most direct version:

```lean
  constructor
  · intro hb0 hcast
    apply hb0
    rwa [ZMod.natCast_zmod_eq_zero_iff_dvd] at hcast
    -- now hcast : 5 ∣ b, need b = 0
    -- but this needs more work since rwa gives 5 ∣ b not b = 0
  ...
```

The cleanest approach is probably:

```lean
lemma ne_zero_iff_cast_ne_zero (b : ℕ) (hb : b < 5) :
    b ≠ 0 ↔ (b : ZMod 5) ≠ 0 := by
  rw [Ne, Ne, ZMod.natCast_zmod_eq_zero_iff_dvd]
  constructor
  · intro hne hdvd; exact hne (by omega)
  · intro hne heq; exact hne (heq ▸ dvd_zero 5)
```

## API pitfalls

1. **`ZMod.natCast_zmod_eq_zero_iff_dvd`**: gives `((x : ℕ) : ZMod n) = 0 ↔ n ∣ x`. Note: it's `n ∣ x`, not `x ∣ n`.
2. **`not_congr`** or **`.not`**: converts `(A ↔ B)` to `(¬A ↔ ¬B)`. In Lean 4 / Mathlib, use `Iff.not` or `not_congr`.
3. **`omega`** works on `ℕ` and can deduce `b = 0` from `5 ∣ b` and `b < 5`.
4. **`simp` on `(0 : ZMod 5)`**: `simp` should handle `((0 : ℕ) : ZMod 5) = 0`.
5. **Do NOT use `decide`** when free variables are present. `decide` only works on closed terms.

## Constraints
- Must compile with Lean 4.24.0 + specified Mathlib
- Return the complete lemma with proof
