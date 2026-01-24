# GPT Prompt 12: MultiplesOf3.lean

## Task
Write a Lean 4 file proving that for all n divisible by 3 (with n ≥ 3), the Erdős-Straus equation 4/n = 1/x + 1/y + 1/z has a solution in positive integers.

## Background

The Erdős-Straus conjecture (1948) states that for every integer n ≥ 2, there exist positive integers x, y, z such that:

```
4/n = 1/x + 1/y + 1/z
```

Equivalently, in integer form:

```
4xyz = n(yz + xz + xy)
```

This file handles multiples of 3.

## Classical Construction

### For n = 3m (any m ≥ 1)

**Construction**: x = m, y = 4m, z = 12m

**Verification**:
```
4/n = 4/(3m)

1/x + 1/y + 1/z = 1/m + 1/(4m) + 1/(12m)
                = 12/(12m) + 3/(12m) + 1/(12m)
                = 16/(12m)
                = 4/(3m) ✓
```

**In integer form**:
- 4xyz = 4 · m · 4m · 12m = 192m³
- n(yz + xz + xy) = 3m(48m² + 12m² + 4m²) = 3m · 64m² = 192m³ ✓

### Special case n = 3
- x = 1, y = 4, z = 12
- Verify: 1/1 + 1/4 + 1/12 = 12/12 + 3/12 + 1/12 = 16/12 = 4/3 ✓

## Requirements

1. **Use the standard solution predicate**:
```lean
def HasErdosStrausSolution (n : ℕ) : Prop :=
  ∃ x y z : ℕ, 0 < x ∧ 0 < y ∧ 0 < z ∧
  4 * x * y * z = n * (y * z + x * z + x * y)
```

2. **Prove the main theorem**:
```lean
theorem mult3_has_solution (n : ℕ) (h3 : 3 ∣ n) (hn : 0 < n) :
    HasErdosStrausSolution n
```

3. **Use the explicit construction**: For n = 3m, use x = m, y = 4m, z = 12m

## Lean 4 + Mathlib Template

```lean
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic

namespace ErdosStraus

def HasErdosStrausSolution (n : ℕ) : Prop :=
  ∃ x y z : ℕ, 0 < x ∧ 0 < y ∧ 0 < z ∧
  4 * x * y * z = n * (y * z + x * z + x * y)

/-- For n = 3, the solution is x=1, y=4, z=12. -/
lemma solution_3 : HasErdosStrausSolution 3 := by
  use 1, 4, 12
  norm_num

/-- For n = 3m, the solution is x=m, y=4m, z=12m. -/
theorem mult3_has_solution (n : ℕ) (h3 : 3 ∣ n) (hn : 0 < n) :
    HasErdosStrausSolution n := by
  obtain ⟨m, rfl⟩ := h3
  have hm : 0 < m := by omega
  use m, 4*m, 12*m
  constructor; exact hm
  constructor; omega
  constructor; omega
  -- Verify: 4 * m * (4m) * (12m) = (3m) * ((4m)*(12m) + m*(12m) + m*(4m))
  -- LHS: 4 * m * 4m * 12m = 192m³
  -- RHS: 3m * (48m² + 12m² + 4m²) = 3m * 64m² = 192m³
  ring

end ErdosStraus
```

## Output Requirements

- Complete Lean 4 file that compiles with Mathlib
- All proofs complete (no `sorry`)
- The algebraic verification should use `ring`
- Export theorem for use in main assembly file
