# Lean 4 Task: Prove `val_of_small_nat` (casting small naturals to ZMod preserves value)

## Environment
- **Lean**: `leanprover/lean4:v4.24.0`
- **Mathlib**: commit `f897ebcf72cd16f89ab4577d0c826cd14afaafc7`

## Task

Prove that if `lo < q` and `b < 5` and `q = 5^k`, then `((lo + b * q : ℕ) : ZMod (5^(k+1))).val = lo + b * q`. In other words, casting a natural number smaller than the modulus into `ZMod N` and extracting `.val` gives back the original number. Return only the Lean 4 code.

## What to prove

```lean
import Mathlib

lemma val_of_small_nat (k : ℕ) (lo b : ℕ) (hlo : lo < 5^k) (hb : b < 5) :
    ((lo + b * 5^k : ℕ) : ZMod (5^(k+1))).val = lo + b * 5^k := by
  sorry
```

## Mathematical content

Since `lo < 5^k` and `b < 5`, we have:
- `b * 5^k ≤ 4 * 5^k`
- `lo + b * 5^k < 5^k + 4 * 5^k = 5 * 5^k = 5^(k+1)`

So `lo + b * 5^k < 5^(k+1)`. For any `n : ℕ` with `n < N`, we have `((n : ℕ) : ZMod N).val = n` because `ZMod.val_natCast` gives `.val = n % N` and `Nat.mod_eq_of_lt` gives `n % N = n` when `n < N`.

## Step-by-step proof strategy

1. Show `lo + b * 5^k < 5^(k+1)`:
   - From `hb : b < 5` get `b * 5^k < 5 * 5^k` (by `Nat.mul_lt_mul_right`)
   - From `hlo : lo < 5^k` and above get `lo + b * 5^k < 5^k + 5 * 5^k` (by `Nat.add_lt_add`)
   - But we actually need `lo + b * 5^k < 5 * 5^k`, which is `lo + b * 5^k < 5^(k+1)`.
   - Better: `lo + b * 5^k ≤ (5^k - 1) + 4 * 5^k = 5 * 5^k - 1 < 5 * 5^k = 5^(k+1)`.
   - Or: use `calc` or `omega` after establishing the right inequalities.
   - Actually the cleanest approach: show `b * 5^k + lo < 5 * 5^k` using `b ≤ 4` and `lo < 5^k`, then rewrite `5 * 5^k = 5^(k+1)`.

2. Apply `ZMod.val_natCast`:
   ```lean
   rw [ZMod.val_natCast]
   ```
   This gives `.val = (lo + b * 5^k) % 5^(k+1)`.

3. Apply `Nat.mod_eq_of_lt`:
   ```lean
   exact Nat.mod_eq_of_lt h
   ```
   where `h : lo + b * 5^k < 5^(k+1)`.

## Useful Mathlib lemmas

- `ZMod.val_natCast` : `((n : ℕ) : ZMod m).val = n % m` (when `m ≠ 0`, which holds for `5^(k+1)`)
- `Nat.mod_eq_of_lt` : `n < m → n % m = n`
- `pow_succ` or `pow_succ'` : `a^(n+1) = a^n * a` or `a * a^n`
- `Nat.mul_lt_mul_right` : for showing `b * q < 5 * q` from `b < 5`

## Recommended proof

```lean
lemma val_of_small_nat (k : ℕ) (lo b : ℕ) (hlo : lo < 5^k) (hb : b < 5) :
    ((lo + b * 5^k : ℕ) : ZMod (5^(k+1))).val = lo + b * 5^k := by
  have hlt : lo + b * 5^k < 5^(k+1) := by
    have hq : 0 < 5^k := Nat.pos_of_ne_zero (by positivity)
    calc lo + b * 5^k
        < 5^k + b * 5^k := by omega
      _ = (1 + b) * 5^k := by ring
      _ ≤ 5 * 5^k := by omega
      _ = 5^(k+1) := by ring
  rw [ZMod.val_natCast]
  exact Nat.mod_eq_of_lt hlt
```

Note: `omega` can handle the linear arithmetic here. The `calc` might be replaced by a direct `omega` if it's powerful enough with the hypotheses. You may also try:

```lean
  have hlt : lo + b * 5^k < 5^(k+1) := by
    have : 5^(k+1) = 5 * 5^k := by ring
    omega
  rw [ZMod.val_natCast]
  exact Nat.mod_eq_of_lt hlt
```

But be careful: `omega` might struggle with `5^k` since it's exponential. If `omega` fails, use explicit `calc` chains with `Nat.mul_lt_mul_right` and `Nat.add_lt_add`.

## API pitfalls

1. **`ZMod.val_natCast`** requires the modulus to be nonzero. `5^(k+1)` is always nonzero, but you might need `NeZero (5^(k+1))` instance. This should be inferred automatically since `5^(k+1) > 0`.
2. **`pow_succ`**: In recent Mathlib, `pow_succ` gives `a^(n+1) = a^n * a`. Use `pow_succ'` for `a * a^n` if needed. Or just use `ring` to show `5 * 5^k = 5^(k+1)`.
3. **Do NOT use `linarith` or `omega` on ZMod** -- but here we're working entirely in `ℕ`, so `omega` is fine for the bound proof.
4. **`omega` and exponents**: `omega` handles linear arithmetic but may not simplify `5^(k+1)`. If needed, first establish `5^(k+1) = 5 * 5^k` by `ring` or `pow_succ`, then `omega` can handle the rest.

## Constraints
- Must compile with Lean 4.24.0 + specified Mathlib
- Return the complete lemma with proof
