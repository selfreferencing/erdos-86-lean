# TASK: Write Lean 4 Code for Mod 210 Case Split Setup

## Context

For Mordell-hard primes p, we have p ≡ 1, 121, 169, 289, 361, or 529 (mod 840).

Since 840 = 4 × 210, and x_5 = (p + 23)/4, we can compute x_5 mod 210:

| p mod 840 | x_5 mod 210 |
|-----------|-------------|
| 1 | 6 |
| 121 | 36 |
| 169 | 48 |
| 289 | 78 |
| 361 | 96 |
| 529 | 138 |

## Key Fact: 210 = 2 × 3 × 5 × 7

So x_5 mod 210 determines divisibility by 2, 3, 5, 7 for x_5.

## Your Task

Write Lean 4 code that:

1. Defines Mordell-hard residue classes
2. Computes x_5 mod 210 for each class
3. Extracts divisibility information

```lean
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

/-- The Mordell-hard residue classes mod 840 -/
def MordellHardClasses : Finset ℕ := {1, 121, 169, 289, 361, 529}

/-- A prime p is Mordell-hard iff p mod 840 is in MordellHardClasses -/
def isMordellHard (p : ℕ) : Prop := p % 840 ∈ MordellHardClasses

/-- Compute x_5 = (p + 23) / 4 mod 210 given p mod 840 -/
def x5_mod210 (p_mod840 : ℕ) : ℕ := ((p_mod840 + 23) / 4) % 210

/-- The six x_5 residue classes for Mordell-hard primes -/
lemma mordellHard_x5_classes :
    x5_mod210 1 = 6 ∧
    x5_mod210 121 = 36 ∧
    x5_mod210 169 = 48 ∧
    x5_mod210 289 = 78 ∧
    x5_mod210 361 = 96 ∧
    x5_mod210 529 = 138 := by
  native_decide

/-- x_5 mod 210 set for Mordell-hard primes -/
def MordellHard_x5_residues : Finset ℕ := {6, 36, 48, 78, 96, 138}

/-- For Mordell-hard p, x_5 mod 210 is in the restricted set -/
lemma mordellHard_x5_in_residues (p : ℕ) (hp : isMordellHard p) :
    ((p + 23) / 4) % 210 ∈ MordellHard_x5_residues := by
  sorry

/-- 3 divides x_5 for all Mordell-hard primes (since all residues are divisible by 3) -/
lemma three_divides_x5_mordellHard (p : ℕ) (hp : isMordellHard p) :
    3 ∣ (p + 23) / 4 := by
  sorry

/-- Divisibility by 2 for each case -/
lemma x5_divisibility_by_2 :
    2 ∣ 6 ∧ 2 ∣ 36 ∧ 2 ∣ 48 ∧ 2 ∣ 78 ∧ 2 ∣ 96 ∧ 2 ∣ 138 := by
  native_decide

/-- Divisibility by 3 for each case -/
lemma x5_divisibility_by_3 :
    3 ∣ 6 ∧ 3 ∣ 36 ∧ 3 ∣ 48 ∧ 3 ∣ 78 ∧ 3 ∣ 96 ∧ 3 ∣ 138 := by
  native_decide

/-- For each Mordell-hard residue class, determine which small primes divide x_5 -/
structure X5DivisibilityData where
  p_mod840 : ℕ
  x5_mod210 : ℕ
  div_by_2 : Bool
  div_by_3 : Bool
  div_by_5 : Bool
  div_by_7 : Bool

def mordellHardDivisibilityTable : List X5DivisibilityData := [
  ⟨1, 6, true, true, false, false⟩,
  ⟨121, 36, true, true, false, false⟩,
  ⟨169, 48, true, true, false, false⟩,
  ⟨289, 78, true, true, false, false⟩,
  ⟨361, 96, true, true, false, false⟩,
  ⟨529, 138, true, true, false, false⟩
]
```

## Note

This setup allows case-splitting on the 6 Mordell-hard residue classes, with known divisibility by small primes for each case.

## Output Format

Provide complete, compilable Lean 4 code.
