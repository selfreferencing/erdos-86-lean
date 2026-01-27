# Lean 4 Task: Prove `numDigits_ge_27_of_ge_87` (digit count lower bound)

## Environment
- **Lean**: `leanprover/lean4:v4.24.0`
- **Mathlib**: commit `f897ebcf72cd16f89ab4577d0c826cd14afaafc7`

## Task

Prove that for all n ≥ 87, the number 2^n has at least 27 decimal digits. Return only the Lean 4 code.

## What to prove

```lean
import Mathlib

namespace Zeroless

def numDigits (n : ℕ) : ℕ := (Nat.digits 10 n).length

theorem numDigits_ge_27_of_ge_87 (n : ℕ) (hn : n ≥ 87) :
    numDigits (2^n) ≥ 27 := by
  sorry

end Zeroless
```

## Mathematical content

2^86 ≈ 7.74 × 10^25 has 26 digits. 2^87 ≈ 1.55 × 10^26 has 27 digits. Since 2^n is strictly increasing, for n ≥ 87, 2^n ≥ 2^87 ≥ 10^26, which means 2^n has at least 27 digits.

Formally: numDigits(m) ≥ k iff m ≥ 10^(k-1). So numDigits(2^n) ≥ 27 iff 2^n ≥ 10^26.

## Step-by-step proof strategy

1. Show `10^26 ≤ 2^87` (by `native_decide` or `norm_num`).
2. Show `2^87 ≤ 2^n` (from `n ≥ 87` and monotonicity of `2^·`).
3. Conclude `10^26 ≤ 2^n`.
4. Convert to `numDigits (2^n) ≥ 27` using the digit-count characterization.

## Useful Mathlib lemmas

- `Nat.pow_le_pow_right` : `0 < a → m ≤ n → a^m ≤ a^n` (or use `pow_le_pow_right`)
- The digit-count characterization: `numDigits m ≥ k ↔ m ≥ 10^(k-1)` (for m ≥ 1)
  This follows from `Nat.lt_digits_length_iff` in Mathlib:
  `k < (Nat.digits b n).length ↔ b^k ≤ n` (for b > 1)
  So `(Nat.digits 10 n).length ≥ 27 ↔ 10^26 ≤ n` (since 26 < length iff 10^26 ≤ n).
- `Nat.lt_digits_length_iff` : `(b : ℕ) → 1 < b → (k < (Nat.digits b n).length ↔ b^k ≤ n)`

## Recommended proof

```lean
theorem numDigits_ge_27_of_ge_87 (n : ℕ) (hn : n ≥ 87) :
    numDigits (2^n) ≥ 27 := by
  -- Step 1: 10^26 ≤ 2^87
  have h_cert : (10 : ℕ)^26 ≤ 2^87 := by native_decide
  -- Step 2: 2^87 ≤ 2^n
  have h_mono : (2 : ℕ)^87 ≤ 2^n := Nat.pow_le_pow_right (by norm_num) hn
  -- Step 3: 10^26 ≤ 2^n
  have h_lower : (10 : ℕ)^26 ≤ 2^n := le_trans h_cert h_mono
  -- Step 4: Convert to digit count
  -- numDigits(2^n) ≥ 27 ↔ 26 < numDigits(2^n) ↔ 10^26 ≤ 2^n
  show (Nat.digits 10 (2^n)).length ≥ 27
  have h10 : (1 : ℕ) < 10 := by decide
  have hlen : 26 < (Nat.digits 10 (2^n)).length := by
    exact (Nat.lt_digits_length_iff h10 (2^n)).2 h_lower
  omega
```

### Alternative: More direct
```lean
theorem numDigits_ge_27_of_ge_87 (n : ℕ) (hn : n ≥ 87) :
    numDigits (2^n) ≥ 27 := by
  unfold numDigits
  suffices h : 26 < (Nat.digits 10 (2^n)).length from by omega
  rw [Nat.lt_digits_length_iff (by decide : (1 : ℕ) < 10)]
  calc (10 : ℕ)^26 ≤ 2^87 := by native_decide
    _ ≤ 2^n := Nat.pow_le_pow_right (by norm_num) hn
```

## API pitfalls

1. **`Nat.lt_digits_length_iff`**: States `k < (Nat.digits b n).length ↔ b^k ≤ n` for `1 < b`. Note: it's `k < length`, not `k ≤ length`. So `26 < length` gives `length ≥ 27`.
2. **`Nat.pow_le_pow_right`**: Needs `0 < base` and `exp1 ≤ exp2`. The naming might be `pow_le_pow_right` in some versions.
3. **`native_decide`** handles `10^26 ≤ 2^87` efficiently (comparing two ~26-digit numbers).
4. **`numDigits` vs `(Nat.digits 10 n).length`**: They're definitionally equal, so `unfold numDigits` or `show` can convert between them.
5. **`norm_num`** can prove `0 < 2` or `1 < 10`.
6. **Do not use `decide`** for `10^26 ≤ 2^87` (too slow for kernel evaluation); use `native_decide`.

## Constraints
- Must compile with Lean 4.24.0 + specified Mathlib
- Return the complete theorem with proof
