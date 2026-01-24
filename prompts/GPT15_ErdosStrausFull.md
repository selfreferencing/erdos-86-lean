# GPT Prompt 15: ErdosStrausFull.lean

## Task
Write a Lean 4 file that assembles the complete proof of the Erdős-Straus conjecture by combining all component lemmas.

## Background

The Erdős-Straus conjecture (1948) states that for every integer n ≥ 2, there exist positive integers x, y, z such that:

```
4/n = 1/x + 1/y + 1/z
```

## Available Component Theorems

You have access to these proven results from other files:

### From EvenNumbers.lean:
```lean
theorem even_has_solution (n : ℕ) (heven : 2 ∣ n) (hn : 2 ≤ n) :
    HasErdosStrausSolution n
```

### From MultiplesOf3.lean:
```lean
theorem mult3_has_solution (n : ℕ) (h3 : 3 ∣ n) (hn : 0 < n) :
    HasErdosStrausSolution n
```

### From NonMordellHardPrimes.lean:
```lean
theorem nonMordellHard_has_solution (p : ℕ) (hp : Nat.Prime p)
    (hnonMH : p % 840 ∉ MordellHardClasses) :
    HasErdosStrausSolution p
```

### From K10CoverageMain.lean (our main result):
```lean
theorem mordellHard_has_solution (p : ℕ) (hp : Nat.Prime p)
    (hMH : p % 840 ∈ MordellHardClasses) :
    HasErdosStrausSolution p
```

### From CompositeReduction.lean:
```lean
theorem oddComposite_has_solution (n : ℕ) (hn : 2 ≤ n)
    (hodd : ¬ 2 ∣ n) (hcomp : ¬ Nat.Prime n) (h3 : ¬ 3 ∣ n) :
    HasErdosStrausSolution n
```

## The Main Theorem

```lean
/-- The Erdős-Straus Conjecture: For all n ≥ 2, the equation
    4/n = 1/x + 1/y + 1/z has a solution in positive integers. -/
theorem erdos_straus_conjecture (n : ℕ) (hn : 2 ≤ n) :
    HasErdosStrausSolution n
```

## Proof Strategy

The proof is a complete case analysis:

```
n ≥ 2
├── Case 1: 2 ∣ n (even)
│   └── Apply even_has_solution
├── Case 2: 2 ∤ n (odd)
    ├── Case 2a: 3 ∣ n
    │   └── Apply mult3_has_solution
    └── Case 2b: 3 ∤ n
        ├── Case 2b-i: n is prime
        │   ├── n % 840 ∈ MordellHardClasses
        │   │   └── Apply mordellHard_has_solution
        │   └── n % 840 ∉ MordellHardClasses
        │       └── Apply nonMordellHard_has_solution
        └── Case 2b-ii: n is composite
            └── Apply oddComposite_has_solution
```

## Lean 4 + Mathlib Template

```lean
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Parity
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

-- Import component files (adjust paths as needed)
-- import EvenNumbers
-- import MultiplesOf3
-- import NonMordellHardPrimes
-- import K10CoverageMain
-- import CompositeReduction

namespace ErdosStraus

/-- A positive integer n has an Erdős-Straus solution if 4/n = 1/x + 1/y + 1/z
    for some positive integers x, y, z. -/
def HasErdosStrausSolution (n : ℕ) : Prop :=
  ∃ x y z : ℕ, 0 < x ∧ 0 < y ∧ 0 < z ∧
  4 * x * y * z = n * (y * z + x * z + x * y)

def MordellHardClasses : Finset ℕ := {1, 121, 169, 289, 361, 529}

-- Component theorems (would be imported in real file)
axiom even_has_solution : ∀ n, 2 ∣ n → 2 ≤ n → HasErdosStrausSolution n
axiom mult3_has_solution : ∀ n, 3 ∣ n → 0 < n → HasErdosStrausSolution n
axiom nonMordellHard_has_solution : ∀ p, Nat.Prime p → p % 840 ∉ MordellHardClasses → HasErdosStrausSolution p
axiom mordellHard_has_solution : ∀ p, Nat.Prime p → p % 840 ∈ MordellHardClasses → HasErdosStrausSolution p
axiom oddComposite_has_solution : ∀ n, 2 ≤ n → ¬(2 ∣ n) → ¬Nat.Prime n → ¬(3 ∣ n) → HasErdosStrausSolution n

/-- **The Erdős-Straus Conjecture**: For all n ≥ 2, the equation
    4/n = 1/x + 1/y + 1/z has a solution in positive integers x, y, z. -/
theorem erdos_straus_conjecture (n : ℕ) (hn : 2 ≤ n) :
    HasErdosStrausSolution n := by
  -- Case 1: n is even
  by_cases heven : 2 ∣ n
  · exact even_has_solution n heven hn
  -- n is odd from here
  -- Case 2: n is divisible by 3
  by_cases h3 : 3 ∣ n
  · exact mult3_has_solution n h3 (by omega)
  -- n is odd and not divisible by 3
  -- Case 3: n is prime
  by_cases hprime : Nat.Prime n
  · -- Check if Mordell-hard
    by_cases hMH : n % 840 ∈ MordellHardClasses
    · exact mordellHard_has_solution n hprime hMH
    · exact nonMordellHard_has_solution n hprime hMH
  -- Case 4: n is odd, composite, not divisible by 3
  · exact oddComposite_has_solution n hn heven hprime h3

/-- Corollary: The conjecture in rational form. -/
theorem erdos_straus_rational (n : ℕ) (hn : 2 ≤ n) :
    ∃ x y z : ℕ, 0 < x ∧ 0 < y ∧ 0 < z ∧
    (4 : ℚ) / n = 1 / x + 1 / y + 1 / z := by
  obtain ⟨x, y, z, hx, hy, hz, heq⟩ := erdos_straus_conjecture n hn
  use x, y, z, hx, hy, hz
  -- Convert integer equation to rational equation
  field_simp
  -- 4 * x * y * z = n * (y * z + x * z + x * y) implies the rational version
  linarith [heq]

end ErdosStraus
```

## Key Points

1. **The proof is pure case analysis** - no new mathematics, just combining lemmas
2. **Case split order matters** - check even first, then mult-of-3, then prime/composite
3. **Decidability**: `2 ∣ n`, `3 ∣ n`, `Nat.Prime n`, and `n % 840 ∈ MordellHardClasses` are all decidable
4. **Use `by_cases`** for each decision point
5. **The axioms would be imports** in the real file - listed as axioms here for standalone compilation

## Output Requirements

- Complete Lean 4 file that compiles with Mathlib
- Clear case analysis structure
- Comments explaining each case
- Include the rational form corollary if possible
- This is the **crown jewel** - the main theorem statement should be prominent
