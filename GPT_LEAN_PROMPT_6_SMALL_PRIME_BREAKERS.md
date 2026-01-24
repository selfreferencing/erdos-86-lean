# TASK: Write Lean 4 Code for Small-Prime Obstruction Breaker Lemmas

## Context

For the Erdős-Straus conjecture, we have K10 = {5, 7, 9, 11, 14, 17, 19, 23, 26, 29}.

For each k, m_k = 4k + 3. The "obstruction" at k fails (i.e., a witness exists) when x_k has a prime factor that is a non-quadratic residue (NQR) mod m_k.

## The Breaker Lemmas

Certain small primes are NQR at specific moduli:

| Small Prime | k values where it's NQR | m_k values |
|-------------|-------------------------|------------|
| 3 | k = 7, 19 | m = 31, 79 |
| 5 | k = 14 | m = 59 |
| 7 | k = 5 | m = 23 |

So:
- **3 | x_k for k ∈ {7, 19}** → witness exists at that k
- **5 | x_14** → witness exists at k = 14
- **7 | x_5** → witness exists at k = 5

## Your Task

Write Lean 4 code that proves these "breaker" lemmas:

```lean
/-- Legendre symbol computation: 3 is NQR mod 31 -/
lemma legendre_3_31 : (3 : ZMod 31).IsNQR := by
  native_decide  -- or explicit computation

/-- Legendre symbol computation: 3 is NQR mod 79 -/
lemma legendre_3_79 : (3 : ZMod 79).IsNQR := by
  native_decide

/-- Legendre symbol computation: 5 is NQR mod 59 -/
lemma legendre_5_59 : (5 : ZMod 59).IsNQR := by
  native_decide

/-- Legendre symbol computation: 7 is NQR mod 23 -/
lemma legendre_7_23 : (7 : ZMod 23).IsNQR := by
  native_decide

/-- If 3 | x_7, then k=7 has a Type II witness -/
lemma k7_witness_of_three_divides (x₇ : ℕ) (hx : 0 < x₇) (h3 : 3 ∣ x₇) :
    ∃ d, d ∣ x₇^2 ∧ d ≤ x₇ ∧ (x₇ + d) % 31 = 0 := by
  sorry

/-- If 3 | x_19, then k=19 has a Type II witness -/
lemma k19_witness_of_three_divides (x₁₉ : ℕ) (hx : 0 < x₁₉) (h3 : 3 ∣ x₁₉) :
    ∃ d, d ∣ x₁₉^2 ∧ d ≤ x₁₉ ∧ (x₁₉ + d) % 79 = 0 := by
  sorry

/-- If 5 | x_14, then k=14 has a Type II witness -/
lemma k14_witness_of_five_divides (x₁₄ : ℕ) (hx : 0 < x₁₄) (h5 : 5 ∣ x₁₄) :
    ∃ d, d ∣ x₁₄^2 ∧ d ≤ x₁₄ ∧ (x₁₄ + d) % 59 = 0 := by
  sorry

/-- If 7 | x_5, then k=5 has a Type II witness -/
lemma k5_witness_of_seven_divides (x₅ : ℕ) (hx : 0 < x₅) (h7 : 7 ∣ x₅) :
    ∃ d, d ∣ x₅^2 ∧ d ≤ x₅ ∧ (x₅ + d) % 23 = 0 := by
  sorry
```

## Key Insight

If q is NQR mod m, and q | x, then q | x² and the residue class of q mod m can be used to construct a witness. Specifically, we need to find d such that d ≡ -x (mod m). Since q is NQR and the divisors of x² generate residues including NQR classes, we can reach the target.

## Imports

```lean
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic
```

## Output Format

Provide complete, compilable Lean 4 code. If `native_decide` doesn't work for Legendre symbols, use explicit computations or `decide` with appropriate instances.
