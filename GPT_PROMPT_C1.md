# Lean 4 Task: Prove `five_q_zero` and `q_sq_zero`

## Environment
- **Lean**: `leanprover/lean4:v4.24.0`
- **Mathlib**: commit `f897ebcf72cd16f89ab4577d0c826cd14afaafc7`

## Task

Prove two small lemmas about `ZMod (5^(k+1))`. Return only the Lean 4 code.

```lean
import Mathlib

namespace Zeroless

/-- 5 * 5^k = 0 in ZMod (5^(k+1)) -/
lemma five_q_zero (k : ℕ) :
    (5 : ZMod (5^(k+1))) * (5^k : ZMod (5^(k+1))) = 0 := by
  sorry

/-- (5^k)^2 = 0 in ZMod (5^(k+1)) when k ≥ 1 -/
lemma q_sq_zero (k : ℕ) (hk : k ≥ 1) :
    (5^k : ZMod (5^(k+1))) * (5^k : ZMod (5^(k+1))) = 0 := by
  sorry

end Zeroless
```

## Hints

### `five_q_zero`

`5 * 5^k = 5^(k+1)` as natural numbers, and `(n : ZMod n) = 0` by `ZMod.natCast_self_equiv` or via `ZMod.natCast_zmod_eq_zero_iff_dvd`.

Approach:
```lean
  have : ((5 * 5^k : ℕ) : ZMod (5^(k+1))) = 0 := by
    rw [show 5 * 5^k = 5^(k+1) from by ring]
    exact_mod_cast ZMod.natCast_self (5^(k+1))
  simpa [Nat.cast_mul] using this
```

Or even simpler: show `5^(k+1) ∣ 5 * 5^k` (they're equal!) and use `ZMod.natCast_zmod_eq_zero_iff_dvd`.

### `q_sq_zero`

`5^k * 5^k = 5^(2k)`. Since `k ≥ 1` implies `k+1 ≤ 2k`, we get `5^(k+1) ∣ 5^(2k)`.

Approach:
```lean
  have hle : k + 1 ≤ 2 * k := by omega
  have hdvd : 5^(k+1) ∣ 5^k * 5^k := by
    rw [← pow_add]
    exact Nat.pow_dvd_pow 5 (by omega : k + 1 ≤ k + k)
  have : ((5^k * 5^k : ℕ) : ZMod (5^(k+1))) = 0 :=
    (ZMod.natCast_zmod_eq_zero_iff_dvd _ _).mpr hdvd
  simpa [Nat.cast_mul] using this
```

## API pitfalls
- `ZMod.natCast_self` : `(n : ZMod n) = 0`
- `ZMod.natCast_zmod_eq_zero_iff_dvd` : `((x : ℕ) : ZMod n) = 0 ↔ n ∣ x`
- `Nat.pow_dvd_pow` : `m ≤ n → b^m ∣ b^n`
- Use `Nat.cast_mul` to push `↑(a * b) = ↑a * ↑b`
- `omega` works for `k + 1 ≤ 2 * k` from `k ≥ 1`

## Constraints
- Must compile with Lean 4.24.0 + specified Mathlib
- Return both lemmas in a single code block
