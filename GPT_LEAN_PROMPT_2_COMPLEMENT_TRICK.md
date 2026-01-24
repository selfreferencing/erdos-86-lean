# TASK: Write Lean 4 Code for Complement Trick Lemma

## Context

We are proving the Erdős-Straus conjecture. The Type II witness condition is:
- d | x², d ≤ x, d ≡ -x (mod m)

The "complement trick" allows us to drop the "d ≤ x" constraint.

## The Lemma

**Setup:** Let x, m be positive integers with gcd(x, m) = 1.

**Claim:** If d | x² and d ≡ -x (mod m), then d' = x²/d also satisfies:
- d' | x²
- d' ≡ -x (mod m)
- One of {d, d'} is ≤ x

**Proof idea:**
- d · d' = x², so d' | x²
- d ≡ -x (mod m) implies d' ≡ x² · d⁻¹ ≡ x² · (-x)⁻¹ ≡ -x (mod m)
- If d > x, then d' = x²/d < x

## Your Task

Write Lean 4 code that proves:

```lean
/-- If d | x² with d ≡ -x (mod m), then d' = x²/d also satisfies d' ≡ -x (mod m) -/
lemma complement_same_residue (x m d : ℕ) (hm : 0 < m) (hx : 0 < x)
    (hgcd : Nat.gcd x m = 1) (hd_div : d ∣ x^2) (hd_pos : 0 < d)
    (hd_cong : d % m = (m - x % m) % m) :
    let d' := x^2 / d
    d' % m = (m - x % m) % m := by
  sorry

/-- One of d or x²/d is ≤ x -/
lemma complement_size_bound (x d : ℕ) (hx : 0 < x) (hd_div : d ∣ x^2) (hd_pos : 0 < d) :
    d ≤ x ∨ x^2 / d ≤ x := by
  sorry

/-- Combined: we can always find a witness ≤ x if any witness exists -/
lemma witness_exists_small (x m : ℕ) (hm : 0 < m) (hx : 0 < x) (hgcd : Nat.gcd x m = 1)
    (h : ∃ d, d ∣ x^2 ∧ 0 < d ∧ d % m = (m - x % m) % m) :
    ∃ d, d ∣ x^2 ∧ d ≤ x ∧ d % m = (m - x % m) % m := by
  sorry
```

## Imports You'll Need

```lean
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic
```

## Output Format

Provide complete, compilable Lean 4 code with:
- All necessary imports
- The lemma statements
- Complete proofs (no `sorry`)
- Any helper lemmas needed

## Note on -x mod m

In natural numbers, -x mod m is represented as (m - x % m) % m. Make sure the congruence condition is stated correctly for ℕ.
