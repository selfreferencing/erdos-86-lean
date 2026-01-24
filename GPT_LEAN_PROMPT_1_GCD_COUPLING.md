# TASK: Write Lean 4 Code for GCD Coupling Lemma

## Context

We are proving the Erdős-Straus conjecture for Mordell-hard primes. A key lemma is the GCD coupling lemma.

## The Lemma

For integers a, b and any r:
```
gcd(r + a, r + b) | |a - b|
```

**Proof idea:** (r + a) - (r + b) = a - b, so any common divisor divides the difference.

## Consequence

For K10 = {5, 7, 9, 11, 14, 17, 19, 23, 26, 29}:
- Define x_k = r + k
- Then gcd(x_a, x_b) | |a - b|
- Since max difference in K10 is 29 - 5 = 24, any prime > 24 divides at most one x_k

## Your Task

Write Lean 4 code that:

1. Proves the basic GCD lemma:
```lean
lemma gcd_shift_divides_diff (r a b : ℤ) :
    (Int.gcd (r + a) (r + b)) ∣ |a - b| := by
  sorry
```

2. Proves the corollary for primes:
```lean
lemma prime_divides_at_most_one_shift (r : ℤ) (p : ℕ) (hp : Nat.Prime p) (hp24 : p > 24)
    (a b : ℕ) (ha : a ∈ K10) (hb : b ∈ K10) (hab : a ≠ b)
    (hpa : (p : ℤ) ∣ r + a) (hpb : (p : ℤ) ∣ r + b) : False := by
  sorry
```

## Imports You'll Need

```lean
import Mathlib.Data.Int.GCD
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic
```

## Output Format

Provide complete, compilable Lean 4 code with:
- All necessary imports
- The lemma statements
- Complete proofs (no `sorry`)
- Any helper lemmas needed

## Constraints

- Use Mathlib conventions
- Keep proofs as simple as possible
- Add brief comments explaining non-obvious steps
