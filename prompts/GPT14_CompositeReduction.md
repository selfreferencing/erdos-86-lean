# GPT Prompt 14: CompositeReduction.lean

## Task
Write a Lean 4 file proving that for odd composite numbers not divisible by 3, the Erdős-Straus equation 4/n = 1/x + 1/y + 1/z has a solution in positive integers.

## Background

The Erdős-Straus conjecture (1948) states that for every integer n ≥ 2, there exist positive integers x, y, z such that:

```
4/n = 1/x + 1/y + 1/z
```

We've already handled:
- **Even numbers** (EvenNumbers.lean)
- **Multiples of 3** (MultiplesOf3.lean)
- **All primes** (NonMordellHardPrimes.lean + our K13 cascade for Mordell-hard)

**Remaining**: Odd composites not divisible by 3.

These are numbers n = p₁^a₁ · p₂^a₂ · ... where all prime factors pᵢ ≥ 5.

## Key Insight

Odd composites not divisible by 3 are of the form:
- n ≡ 1 (mod 6), or
- n ≡ 5 (mod 6)

For these, we can use **direct constructions** based on residue class mod 840.

## Classical Constructions

### Method 1: Factor-Based Construction

If n = a · b with 1 < a ≤ b, sometimes:
```
4/n = 4/(ab) = 1/x + 1/y + 1/z
```
can be derived from knowledge of 4/a or 4/b.

### Method 2: Residue Class Construction

For n ≡ r (mod 840) where r is not in Mordell-hard classes, the Bradford Type II construction for some k ∈ {0, 1, 2, ..., 29} works.

**Key fact**: The residue class of n mod 840 determines which construction applies, regardless of whether n is prime or composite.

### Method 3: Direct Construction for n ≡ 1 (mod 4)

For odd n ≡ 1 (mod 4), we have n + 3 ≡ 0 (mod 4), so (n+3)/4 is an integer.

If (n+3)/4 has a divisor d with d ≡ -((n+3)/4) (mod 3), then:
```
4/n = 1/((n+3)/4) + 1/(d · n/3) + 1/(((n+3)/4)/d · n)
```
(This is the k=0 Bradford Type II construction.)

### Method 4: Exhaustive Small Cases

For small odd composites not divisible by 3:
| n | Factorization | Solution (x, y, z) |
|---|---------------|-------------------|
| 25 | 5² | (7, 100, 700) |
| 35 | 5·7 | (9, 252, 2520) |
| 49 | 7² | (13, 196, 9604) |
| 55 | 5·11 | (14, 385, ...) |

## Requirements

1. **Use standard definition**:
```lean
def HasErdosStrausSolution (n : ℕ) : Prop :=
  ∃ x y z : ℕ, 0 < x ∧ 0 < y ∧ 0 < z ∧
  4 * x * y * z = n * (y * z + x * z + x * y)
```

2. **Prove the main theorem**:
```lean
theorem oddComposite_has_solution (n : ℕ) (hn : 2 ≤ n)
    (hodd : ¬ 2 ∣ n) (hcomp : ¬ Nat.Prime n) (h3 : ¬ 3 ∣ n) :
    HasErdosStrausSolution n
```

3. **Strategy**:
   - Use residue class mod 840
   - Show all non-Mordell-hard residue classes have solutions
   - Since n is composite and not divisible by 2 or 3, its residue class mod 840 is restricted
   - Use `native_decide` for finite case checks

## Lean 4 + Mathlib Template

```lean
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

namespace ErdosStraus

def HasErdosStrausSolution (n : ℕ) : Prop :=
  ∃ x y z : ℕ, 0 < x ∧ 0 < y ∧ 0 < z ∧
  4 * x * y * z = n * (y * z + x * z + x * y)

def MordellHardClasses : Finset ℕ := {1, 121, 169, 289, 361, 529}

/-- The residue classes mod 840 that are coprime to 6 (odd and not divisible by 3). -/
def OddNonMult3Classes : Finset ℕ :=
  (Finset.range 840).filter (fun r => r % 2 = 1 ∧ r % 3 ≠ 0)

/-- For odd n not divisible by 3, use Bradford construction based on n mod 840. -/
lemma oddNonMult3_residue_has_solution (r : ℕ) (hr : r ∈ OddNonMult3Classes) :
    ∀ n, n % 840 = r → 2 ≤ n → HasErdosStrausSolution n := by
  sorry -- Case analysis on r, using Bradford constructions

/-- Small odd composites not divisible by 3. -/
lemma solution_25 : HasErdosStrausSolution 25 := by
  use 7, 100, 700
  norm_num

lemma solution_35 : HasErdosStrausSolution 35 := by
  use 9, 252, 2520
  norm_num

lemma solution_49 : HasErdosStrausSolution 49 := by
  use 13, 196, 9604
  norm_num

/-- Odd composites not divisible by 3 have Erdős-Straus solutions. -/
theorem oddComposite_has_solution (n : ℕ) (hn : 2 ≤ n)
    (hodd : ¬ 2 ∣ n) (hcomp : ¬ Nat.Prime n) (h3 : ¬ 3 ∣ n) :
    HasErdosStrausSolution n := by
  -- n is odd, composite, ≥ 4, not divisible by 3
  -- So n ≥ 25 (smallest such is 5² = 25)
  -- Use residue class argument
  have hr : n % 840 ∈ OddNonMult3Classes := by
    simp [OddNonMult3Classes]
    constructor
    · -- n is odd
      intro h2
      exact hodd h2
    · -- n not divisible by 3
      intro h3'
      exact h3 h3'
  exact oddNonMult3_residue_has_solution (n % 840) hr n rfl hn

end ErdosStraus
```

## Key Mathematical Fact

Every odd composite not divisible by 3 has n mod 840 ∈ OddNonMult3Classes.

For each such residue class r:
- Either r is NOT Mordell-hard (so k ∈ {0,1,2} works by classical results)
- Or r IS Mordell-hard, but then r ∈ {1, 121, 169, 289, 361, 529}

But wait: Mordell-hard classes are specifically about PRIMES. For composites, the construction is different.

**Actual key fact**: For composites, the existence of small factors often provides direct constructions that don't rely on the Mordell classification.

## Output Requirements

- Complete Lean 4 file that compiles with Mathlib
- Handle small cases (25, 35, 49, 55, ...) explicitly
- Use `sorry` for the general residue class argument if needed
- Structure should be clear even if some proofs are incomplete
