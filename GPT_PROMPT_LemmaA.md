# Lean 4 Task: Prove `nat_add_mul_div`

## Environment
- **Lean**: `leanprover/lean4:v4.24.0`
- **Mathlib**: commit `f897ebcf72cd16f89ab4577d0c826cd14afaafc7`

## Task

Prove this standalone lemma. It does NOT depend on any project-specific definitions. Return only the Lean 4 code.

```lean
import Mathlib

/-- If lo < q, then (lo + b * q) / q = b -/
lemma nat_add_mul_div (lo q b : ℕ) (hlo : lo < q) (hq : 0 < q) :
    (lo + b * q) / q = b := by
  sorry
```

## Mathematical content

This is elementary: since `lo < q`, the Euclidean division of `lo + b * q` by `q` gives quotient `b` and remainder `lo`.

## Useful Mathlib lemmas

- `Nat.add_mul_div_right` : `∀ (a b : ℕ) {c : ℕ}, 0 < c → (a + b * c) / c = a / c + b`
- `Nat.div_eq_of_lt` : `∀ {a b : ℕ}, a < b → a / b = 0`
- `Nat.add_mul_div_left` : `∀ (a b : ℕ) {c : ℕ}, 0 < c → (a + c * b) / c = a / c + b`

So the proof could be as simple as:
```lean
  rw [Nat.add_mul_div_right lo b hq, Nat.div_eq_of_lt hlo, zero_add]
```

Or even just `omega` might work.

## Constraints
- Must compile with Lean 4.24.0 + the specified Mathlib commit
- Return ONLY the complete lemma with proof (no sorry)
