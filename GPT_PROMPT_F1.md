# Lean 4 Task: Prove `direct_verify_87_to_300` (computational verification)

## Environment
- **Lean**: `leanprover/lean4:v4.24.0`
- **Mathlib**: commit `f897ebcf72cd16f89ab4577d0c826cd14afaafc7`

## Task

Prove that for every n from 87 to 300, the number 2^n contains a digit 0 in base 10. Return only the Lean 4 code.

## What to prove

```lean
import Mathlib

namespace Zeroless

def zeroless (n : ℕ) : Prop := 0 ∉ Nat.digits 10 n

instance : DecidablePred zeroless := fun n =>
  decidable_of_iff (∀ d ∈ Nat.digits 10 n, d ≠ 0)
    ⟨fun h hm => h 0 hm rfl, fun h d hd hd0 => h (hd0 ▸ hd)⟩

theorem direct_verify_87_to_300 :
    ∀ n : ℕ, 87 ≤ n → n ≤ 300 → ¬zeroless (2^n) := by
  sorry

end Zeroless
```

## Mathematical content

This is a pure computation. For each n from 87 to 300, compute 2^n in base 10 and verify it contains a digit 0. Since `zeroless` has a `Decidable` instance, this can be dispatched by `native_decide` or `decide`.

## Proof strategy

### Approach 1: Single native_decide (if Lean can handle the range)
```lean
theorem direct_verify_87_to_300 :
    ∀ n : ℕ, 87 ≤ n → n ≤ 300 → ¬zeroless (2^n) := by
  intro n h1 h2
  interval_cases n <;> native_decide
```

The `interval_cases n` tactic, given `87 ≤ n` and `n ≤ 300`, generates 214 goals (one per value). Each is closed by `native_decide`.

### Approach 2: omega + native_decide (if interval_cases is slow)
```lean
theorem direct_verify_87_to_300 :
    ∀ n : ℕ, 87 ≤ n → n ≤ 300 → ¬zeroless (2^n) := by
  intro n h1 h2
  -- Generate all cases
  omega_nat  -- or: interval_cases n
  all_goals native_decide
```

### Approach 3: Finset-based (avoids per-case overhead)
```lean
theorem direct_verify_87_to_300 :
    ∀ n : ℕ, 87 ≤ n → n ≤ 300 → ¬zeroless (2^n) := by
  intro n h1 h2
  have hmem : n ∈ Finset.Icc 87 300 := Finset.mem_Icc.2 ⟨h1, h2⟩
  have : ∀ m ∈ Finset.Icc 87 300, ¬zeroless (2^m) := by native_decide
  exact this n hmem
```

The `Finset.Icc 87 300` approach is cleanest: it checks all 214 values in one `native_decide` call. This uses the `DecidablePred` instance on `zeroless`.

### Approach 4: Split into chunks (if 214 values is too many for one call)
```lean
private theorem dv_87_150 : ∀ n ∈ Finset.Icc 87 150, ¬zeroless (2^n) := by native_decide
private theorem dv_151_225 : ∀ n ∈ Finset.Icc 151 225, ¬zeroless (2^n) := by native_decide
private theorem dv_226_300 : ∀ n ∈ Finset.Icc 226 300, ¬zeroless (2^n) := by native_decide

theorem direct_verify_87_to_300 :
    ∀ n : ℕ, 87 ≤ n → n ≤ 300 → ¬zeroless (2^n) := by
  intro n h1 h2
  by_cases h150 : n ≤ 150
  · exact dv_87_150 n (Finset.mem_Icc.2 ⟨h1, h150⟩)
  · push_neg at h150
    by_cases h225 : n ≤ 225
    · exact dv_151_225 n (Finset.mem_Icc.2 ⟨by omega, h225⟩)
    · push_neg at h225
      exact dv_226_300 n (Finset.mem_Icc.2 ⟨by omega, h2⟩)
```

## API pitfalls

1. **`interval_cases`** requires both `h1 : 87 ≤ n` and `h2 : n ≤ 300` to be in context. It generates one goal per value.
2. **`native_decide`** compiles to native code and runs the decision procedure. It handles bignum arithmetic efficiently.
3. **`Finset.Icc 87 300`** is `{87, 88, ..., 300}` as a `Finset ℕ`. Use `Finset.mem_Icc` to convert between `n ∈ Finset.Icc a b` and `a ≤ n ∧ n ≤ b`.
4. **Performance**: `native_decide` on `∀ m ∈ Finset.Icc 87 300, ...` checks all 214 values. The largest computation is 2^300 (a 91-digit number). This should complete in seconds.
5. **If compilation is too slow**: Split into smaller chunks (Approach 4).
6. **`decide` vs `native_decide`**: `decide` uses the kernel; `native_decide` compiles to native code. For bignums, `native_decide` is much faster.

## Constraints
- Must compile with Lean 4.24.0 + specified Mathlib
- Return the complete theorem with proof
- Prefer Approach 3 (Finset-based) for cleanliness
- Fall back to Approach 4 (chunks) if needed for performance
