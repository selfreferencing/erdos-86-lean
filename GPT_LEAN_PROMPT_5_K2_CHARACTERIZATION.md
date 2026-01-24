# TASK: Write Lean 4 Code for k=2 Characterization

## Context

For the Erdős-Straus conjecture on Mordell-hard primes:
- k=2 means m₂ = 11
- x₂ = (p + 11) / 4 = r + 2
- For Mordell-hard primes, p ≡ 1 (mod 3), so x₂ ≡ 0 (mod 3) - i.e., **3 always divides x₂**
- Target is -x₂ mod 11

## Unconditional Success Cases

For certain p mod 11, small fixed divisors work:

| p mod 11 | -x₂ mod 11 | Witness d |
|----------|------------|-----------|
| 7 | 1 | d = 1 |
| 10 | 3 | d = 3 |
| 8 | 9 | d = 9 |

Since 3 | x₂ always, we have 3 | x₂² and 9 | x₂², so d = 3 and d = 9 are always available.

## Higher 3-Power Cases

| p mod 11 | -x₂ mod 11 | Witness d | Condition |
|----------|------------|-----------|-----------|
| 2 | 5 ≡ 3³ | d = 27 | v₃(x₂) ≥ 2 |
| 6 | 4 ≡ 3⁴ | d = 81 | v₃(x₂) ≥ 2 |

## Your Task

Write Lean 4 code:

```lean
/-- For Mordell-hard primes, 3 divides x₂ -/
lemma three_divides_x2 (p : ℕ) (hp : Nat.Prime p) (hp_mod3 : p % 3 = 1) :
    3 ∣ (p + 11) / 4 := by
  sorry

/-- Powers of 3 mod 11 -/
lemma three_pow_mod11 :
    (3^1 % 11 = 3) ∧ (3^2 % 11 = 9) ∧ (3^3 % 11 = 5) ∧ (3^4 % 11 = 4) ∧ (3^5 % 11 = 1) := by
  native_decide

/-- k=2 works when p ≡ 7 (mod 11) via d=1 -/
lemma k2_works_p7 (p : ℕ) (hp : Nat.Prime p) (hp_mod : p % 11 = 7) :
    let x₂ := (p + 11) / 4
    ∃ d, d ∣ x₂^2 ∧ d ≤ x₂ ∧ (x₂ + d) % 11 = 0 := by
  sorry

/-- k=2 works when p ≡ 10 (mod 11) via d=3 -/
lemma k2_works_p10 (p : ℕ) (hp : Nat.Prime p) (hp_mod3 : p % 3 = 1) (hp_mod11 : p % 11 = 10) :
    let x₂ := (p + 11) / 4
    ∃ d, d ∣ x₂^2 ∧ d ≤ x₂ ∧ (x₂ + d) % 11 = 0 := by
  sorry

/-- k=2 works when p ≡ 8 (mod 11) via d=9 -/
lemma k2_works_p8 (p : ℕ) (hp : Nat.Prime p) (hp_mod3 : p % 3 = 1) (hp_mod11 : p % 11 = 8) :
    let x₂ := (p + 11) / 4
    ∃ d, d ∣ x₂^2 ∧ d ≤ x₂ ∧ (x₂ + d) % 11 = 0 := by
  sorry

/-- k=2 works when p ≡ 2 (mod 11) and v₃(x₂) ≥ 2 via d=27 -/
lemma k2_works_p2_v3 (p : ℕ) (hp : Nat.Prime p) (hp_mod3 : p % 3 = 1)
    (hp_mod11 : p % 11 = 2) (hv3 : 9 ∣ (p + 11) / 4) :
    let x₂ := (p + 11) / 4
    ∃ d, d ∣ x₂^2 ∧ d ≤ x₂ ∧ (x₂ + d) % 11 = 0 := by
  sorry

/-- k=2 works when p ≡ 6 (mod 11) and v₃(x₂) ≥ 2 via d=81 -/
lemma k2_works_p6_v3 (p : ℕ) (hp : Nat.Prime p) (hp_mod3 : p % 3 = 1)
    (hp_mod11 : p % 11 = 6) (hv3 : 9 ∣ (p + 11) / 4) :
    let x₂ := (p + 11) / 4
    ∃ d, d ∣ x₂^2 ∧ d ≤ x₂ ∧ (x₂ + d) % 11 = 0 := by
  sorry
```

## Imports

```lean
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Parity
import Mathlib.Tactic
```

## Output Format

Provide complete, compilable Lean 4 code with all proofs.
