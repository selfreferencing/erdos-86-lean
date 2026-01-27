# Lean 4 Task: Prove `erdos_86_conjecture` (Main Theorem Assembly)

## Environment
- **Lean**: `leanprover/lean4:v4.24.0`
- **Mathlib**: commit `f897ebcf72cd16f89ab4577d0c826cd14afaafc7`

## Task

Assemble the main theorem from direct verification (F1) and the theoretical bound (F7). Return only the Lean 4 code.

## What to prove

```lean
import Mathlib

namespace Zeroless

def numDigits (n : ℕ) : ℕ := (Nat.digits 10 n).length

def zeroless (n : ℕ) : Prop := 0 ∉ Nat.digits 10 n

instance : DecidablePred zeroless := fun n =>
  decidable_of_iff (∀ d ∈ Nat.digits 10 n, d ≠ 0)
    ⟨fun h hm => h 0 hm rfl, fun h d hd hd0 => h (hd0 ▸ hd)⟩

-- ASSUMED PROVED (F1):
axiom direct_verify_87_to_300 :
    ∀ n : ℕ, 87 ≤ n → n ≤ 300 → ¬zeroless (2^n)

-- ASSUMED PROVED (F2):
axiom numDigits_ge_27_of_ge_87 :
    ∀ n : ℕ, n ≥ 87 → numDigits (2^n) ≥ 27

-- ASSUMED PROVED (from DigitSqueeze.lean):
axiom digit_squeeze_le (n k : ℕ) (hk : 1 ≤ k) (hdigits : numDigits (2^n) ≤ k) :
    n < k * 3322 / 1000 + 1

-- ASSUMED PROVED (F7 or axiom):
axiom no_zeroless_k_ge_91 (k : ℕ) (hk : k ≥ 91) :
    ∀ n : ℕ, numDigits (2^n) = k → ¬zeroless (2^n)

-- THE MAIN THEOREM:
theorem erdos_86_conjecture :
    ∀ n : ℕ, n > 86 → ¬zeroless (2^n) := by
  sorry

end Zeroless
```

## Mathematical content

The proof splits into two cases based on n:

**Case 1: 87 ≤ n ≤ 300**
By `direct_verify_87_to_300` (computational verification).

**Case 2: n > 300**
Then numDigits(2^n) ≥ 91 (since n > 300 implies 2^n > 2^300 > 10^90).
Apply `no_zeroless_k_ge_91` with k = numDigits(2^n).

The key step in Case 2 is showing numDigits(2^n) ≥ 91 for n > 300.

## Step-by-step proof strategy

```lean
theorem erdos_86_conjecture :
    ∀ n : ℕ, n > 86 → ¬zeroless (2^n) := by
  intro n hn
  by_cases h300 : n ≤ 300
  · -- Case 1: n ∈ {87, ..., 300}
    exact direct_verify_87_to_300 n (by omega) h300
  · -- Case 2: n > 300
    push_neg at h300
    -- Show numDigits(2^n) ≥ 91
    have hk : numDigits (2^n) ≥ 91 := by
      -- 10^90 ≤ 2^301 ≤ 2^n, so numDigits ≥ 91
      sorry
    -- Apply the theoretical bound
    exact no_zeroless_k_ge_91 (numDigits (2^n)) hk n rfl
```

## The missing piece: `numDigits_ge_91_of_gt_300`

```lean
theorem numDigits_ge_91_of_gt_300 (n : ℕ) (hn : n > 300) :
    numDigits (2^n) ≥ 91 := by
  -- 10^90 ≤ 2^301 (by native_decide or certificate)
  -- 2^301 ≤ 2^n (by monotonicity, since n ≥ 301)
  -- So 10^90 ≤ 2^n, which means numDigits(2^n) ≥ 91
  have h_cert : (10 : ℕ)^90 ≤ 2^301 := by native_decide
  have h_mono : (2 : ℕ)^301 ≤ 2^n := by
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have h_lower : (10 : ℕ)^90 ≤ 2^n := le_trans h_cert h_mono
  show (Nat.digits 10 (2^n)).length ≥ 91
  have h10 : (1 : ℕ) < 10 := by decide
  have hlen : 90 < (Nat.digits 10 (2^n)).length := by
    exact (Nat.lt_digits_length_iff h10 (2^n)).2 h_lower
  omega
```

## Alternative main proof (if no_zeroless_k_ge_91 is not available)

If the theoretical bound is not proved but direct verification extends further:

```lean
-- If we can verify up to n = 6643:
axiom direct_verify_87_to_6643 :
    ∀ n : ℕ, 87 ≤ n → n ≤ 6643 → ¬zeroless (2^n)

-- Then for n > 6643, numDigits(2^n) ≥ 2001:
theorem numDigits_ge_2001_of_gt_6643 (n : ℕ) (hn : n > 6643) :
    numDigits (2^n) ≥ 2001 := by
  sorry -- Same approach: 10^2000 ≤ 2^6644 by native_decide, then monotonicity

-- And no_zeroless_k_ge_2001 is MUCH easier to prove (forced-tail bound is astronomical)
```

## Recommended complete proof

```lean
theorem erdos_86_conjecture :
    ∀ n : ℕ, n > 86 → ¬zeroless (2^n) := by
  intro n hn
  by_cases h300 : n ≤ 300
  · exact direct_verify_87_to_300 n (by omega) h300
  · push_neg at h300
    have h91 : numDigits (2^n) ≥ 91 := by
      suffices h : 90 < (Nat.digits 10 (2^n)).length by omega
      rw [Nat.lt_digits_length_iff (by decide : (1 : ℕ) < 10)]
      calc (10 : ℕ)^90
          ≤ 2^301 := by native_decide
        _ ≤ 2^n := Nat.pow_le_pow_right (by norm_num) (by omega)
    exact no_zeroless_k_ge_91 (numDigits (2^n)) h91 n rfl
```

## Corollary: zeroless powers are finite

```lean
theorem zeroless_powers_finite :
    {n : ℕ | zeroless (2^n)}.Finite := by
  apply Set.Finite.subset (Set.finite_Iio 87)
  intro n hn
  simp only [Set.mem_Iio]
  by_contra h
  push_neg at h
  exact hn (erdos_86_conjecture n h)
```

## API pitfalls

1. **`by_cases`**: Use `by_cases h300 : n ≤ 300` to split.
2. **`push_neg`**: Converts `¬(n ≤ 300)` to `300 < n` (i.e., `n > 300`).
3. **`omega`**: Handles `n > 86` ∧ `n ≤ 300` → `87 ≤ n`.
4. **`Nat.pow_le_pow_right`**: Needs `0 < base` and `exp1 ≤ exp2`.
5. **`native_decide`**: For `10^90 ≤ 2^301` (comparing ~91-digit numbers). Fast.
6. **`rfl`**: For `numDigits (2^n) = numDigits (2^n)` (the k = numDigits argument).
7. **`Set.Finite.subset` + `Set.finite_Iio`**: For the finiteness corollary.

## Constraints
- Must compile with Lean 4.24.0 + specified Mathlib
- Return the complete main theorem with proof
- May assume F1 (direct_verify_87_to_300) and F7 (no_zeroless_k_ge_91)
- The main theorem should have NO sorry
