# GPT Prompt 11: EvenNumbers.lean

## Task
Write a Lean 4 file proving that for all even n ≥ 2, the Erdős-Straus equation 4/n = 1/x + 1/y + 1/z has a solution in positive integers.

## Background

The Erdős-Straus conjecture (1948) states that for every integer n ≥ 2, there exist positive integers x, y, z such that:

```
4/n = 1/x + 1/y + 1/z
```

Equivalently, in integer form (clearing denominators):

```
4xyz = n(yz + xz + xy)
```

This file handles the **easy case**: even numbers.

## Classical Constructions

### Case n = 2
- x = 1, y = 2, z = 2
- Verify: 4/2 = 2 and 1/1 + 1/2 + 1/2 = 1 + 0.5 + 0.5 = 2 ✓

### Case n = 2m where m ≥ 1

**Construction**: x = m, y = 2m, z = 2m

**Verification**:
- 4xyz = 4 · m · 2m · 2m = 16m³
- n(yz + xz + xy) = 2m(4m² + 2m² + 2m²) = 2m · 8m² = 16m³ ✓

Alternative construction for odd m: x = m, y = m+1, z = m(m+1)

## Requirements

1. **Define the solution predicate**:
```lean
def HasErdosStrausSolution (n : ℕ) : Prop :=
  ∃ x y z : ℕ, 0 < x ∧ 0 < y ∧ 0 < z ∧
  4 * x * y * z = n * (y * z + x * z + x * y)
```

2. **Prove the main theorem**:
```lean
theorem even_has_solution (n : ℕ) (heven : 2 ∣ n) (hn : 2 ≤ n) :
    HasErdosStrausSolution n
```

3. **Use explicit witness constructions** with the `use` tactic

4. **Verify algebraic identities** with `ring`, `linarith`, or `omega`

5. **Handle edge cases** (n = 2) explicitly if needed

## Lean 4 + Mathlib Template

```lean
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Parity
import Mathlib.Tactic

namespace ErdosStraus

/-- A positive integer n has an Erdős-Straus solution if 4/n = 1/x + 1/y + 1/z
    for some positive integers x, y, z. Equivalently: 4xyz = n(yz + xz + xy). -/
def HasErdosStrausSolution (n : ℕ) : Prop :=
  ∃ x y z : ℕ, 0 < x ∧ 0 < y ∧ 0 < z ∧
  4 * x * y * z = n * (y * z + x * z + x * y)

/-- For n = 2, the solution is x=1, y=2, z=2. -/
lemma solution_2 : HasErdosStrausSolution 2 := by
  use 1, 2, 2
  norm_num

/-- For even n = 2m with m ≥ 1, use x=m, y=2m, z=2m. -/
theorem even_has_solution (n : ℕ) (heven : 2 ∣ n) (hn : 2 ≤ n) :
    HasErdosStrausSolution n := by
  obtain ⟨m, rfl⟩ := heven
  -- n = 2m, need m ≥ 1
  have hm : 0 < m := by omega
  use m, 2*m, 2*m
  constructor; exact hm
  constructor; omega
  constructor; omega
  -- Verify: 4 * m * (2m) * (2m) = (2m) * ((2m)*(2m) + m*(2m) + m*(2m))
  -- 4 * m * 2m * 2m = 16m³
  -- 2m * (4m² + 2m² + 2m²) = 2m * 8m² = 16m³
  ring

end ErdosStraus
```

## Output Requirements

- Complete Lean 4 file that compiles with Mathlib
- All proofs complete (no `sorry`)
- Include helpful comments
- Export the main theorem for use in other files
