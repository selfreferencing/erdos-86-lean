# Lean 4 Task: Prove `m_pow_eq` (nilpotent binomial in ZMod)

## Environment
- **Lean**: `leanprover/lean4:v4.24.0`
- **Mathlib**: commit `f897ebcf72cd16f89ab4577d0c826cd14afaafc7`

## Task

Prove that `(m k)^j = 1 + j * 3 * 5^k` in `ZMod (5^(k+1))`, using the already-proved `s_eq_three`. Return only the Lean 4 code for the two auxiliary lemmas and the main lemma.

## Definitions (from the project)

```lean
import Mathlib

namespace Zeroless

/-- Period for k trailing zeroless digits: T_k = 4 · 5^(k-1) -/
def T (k : ℕ) : ℕ := 4 * 5^(k-1)

/-- The multiplier: m_k = 2^{T_k} mod 5^{k+1} -/
noncomputable def m (k : ℕ) : ZMod (5^(k+1)) :=
  (2 : ZMod (5^(k+1)))^(T k)
```

## Available proved theorem

```lean
-- Already proved in the file (by Aristotle). You may use it as an axiom:
axiom s_eq_three (k : ℕ) (hk : k ≥ 1) :
    (m k : ZMod (5^(k+1))) = 1 + 3 * 5^k
```

## What to prove

Three things, in order:

### 1. Helper: binomial with nilpotent element

```lean
/-- If a^2 = 0 in a commutative semiring, then (1+a)^n = 1 + n*a -/
private lemma one_add_pow_of_sq_zero
    {R : Type*} [CommSemiring R] (a : R) (ha : a^2 = 0) (n : ℕ) :
    (1 + a)^n = 1 + (n : R) * a := by
  sorry
```

**Hint**: Induction on `n`. The key step is `a * a = 0` (from `ha` via `pow_two`). Then:
```
(1+a)^(n+1) = (1 + n*a)*(1+a) = 1 + n*a + a + n*a*a = 1 + (n+1)*a
```

### 2. Square-zero lemma for 5^k

```lean
/-- (3 * 5^k)^2 = 0 in ZMod (5^(k+1)) when k ≥ 1 -/
private lemma three_mul_pow_k_sq_zero (k : ℕ) (hk : k ≥ 1) :
    ((3 : ZMod (5^(k+1))) * (5^k : ZMod (5^(k+1))))^2 = 0 := by
  sorry
```

**Hint**: Show `5^(k+1) ∣ 9 * 5^(2*k)`. Since `k ≥ 1` implies `k+1 ≤ 2*k`, we get `5^(k+1) ∣ 5^(2*k)`, hence `5^(k+1) ∣ 9 * 5^(2*k)`. Use `ZMod.natCast_zmod_eq_zero_iff_dvd` to convert to ZMod.

Key steps:
- `(3 * 5^k)^2 = 9 * 5^(2*k)` (by `ring` or `pow_mul`)
- `k + 1 ≤ 2 * k` (by `omega` from `hk`)
- `5^(k+1) ∣ 5^(2*k)` (by `Nat.pow_dvd_pow 5 ‹k+1 ≤ 2*k›`)
- Cast to ZMod using `ZMod.natCast_zmod_eq_zero_iff_dvd`

### 3. The power formula

```lean
/-- (m k)^j = 1 + j * 3 * 5^k in ZMod (5^(k+1)) -/
lemma m_pow_eq (k : ℕ) (hk : k ≥ 1) (j : ℕ) :
    (m k : ZMod (5^(k+1)))^j = 1 + (j : ZMod (5^(k+1))) * 3 * (5^k : ZMod (5^(k+1))) := by
  sorry
```

**Hint**: Rewrite `m k` using `s_eq_three`, then apply `one_add_pow_of_sq_zero` with `a = 3 * 5^k`. The `ring` tactic should handle the remaining algebraic rearrangement.

```lean
  rw [s_eq_three k hk]
  have hsq := three_mul_pow_k_sq_zero k hk
  have := one_add_pow_of_sq_zero (3 * (5^k : ZMod (5^(k+1)))) hsq j
  -- Now rearrange: (1 + 3*5^k)^j = 1 + j * (3*5^k) vs goal 1 + j*3*5^k
  convert this using 1
  ring
```

## API pitfalls to avoid

1. **`linarith` and `omega` do NOT work on `ZMod`** - use `ring` or `linear_combination` instead
2. **`(3 : ZMod 5) ≠ 0` cannot be proved by `decide`** when free variables are present. Use `ZMod.natCast_zmod_eq_zero_iff_dvd` instead.
3. **`ZMod.natCast_zmod_eq_zero_iff_dvd`**: `((x : ℕ) : ZMod n) = 0 ↔ n ∣ x`
4. **`Nat.pow_dvd_pow`**: `∀ (b : ℕ), m ≤ n → b^m ∣ b^n`

## Constraints
- Must compile with Lean 4.24.0 + the specified Mathlib commit
- Return all three lemmas as a single code block
- You may use `axiom s_eq_three` (it's proved in the actual file)

end Zeroless
