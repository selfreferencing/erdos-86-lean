# GPT Prompt 13: NonMordellHardPrimes.lean

## Task
Write a Lean 4 file proving that for all primes p that are NOT Mordell-hard, the Erdős-Straus equation 4/p = 1/x + 1/y + 1/z has a solution in positive integers.

## Background

The Erdős-Straus conjecture (1948) states that for every integer n ≥ 2, there exist positive integers x, y, z such that:

```
4/n = 1/x + 1/y + 1/z
```

### Mordell-Hard Primes

A prime p is **Mordell-hard** if p ≡ r (mod 840) where r ∈ {1, 121, 169, 289, 361, 529}.

These are the "hard cases" that require sophisticated constructions (handled in a separate file).

### Non-Mordell-Hard Primes

All other primes have simpler solutions via classical constructions.

## Key Classical Results

### 1. Primes p ≡ 2 (mod 3) — Mordell's 1922 Result

If p ≡ 2 (mod 3), then p + 1 ≡ 0 (mod 3), so we can write:

**Construction**:
- When p ≡ 3 (mod 4): x = (p+1)/4, y = (p+1)/4, z = p(p+1)/8...

Actually, simpler: For p ≡ 2 (mod 3), use the Type I identity:
```
4/p = 1/a + 1/b + 1/c where a = ⌈(p+1)/4⌉
```

### 2. Small Primes (Direct Solutions)

| p | Solution (x, y, z) | Verification |
|---|-------------------|--------------|
| 2 | (1, 2, 2) | 1 + 1/2 + 1/2 = 2 = 4/2 ✓ |
| 3 | (1, 4, 12) | 1 + 1/4 + 1/12 = 16/12 = 4/3 ✓ |
| 5 | (2, 4, 20) | 1/2 + 1/4 + 1/20 = 16/20 = 4/5 ✓ |
| 7 | (2, 28, 28) | 1/2 + 1/28 + 1/28 = 16/28 = 4/7 ✓ |
| 11 | (3, 12, 132) | 4/11 check ✓ |
| 13 | (4, 18, 468) | 4/13 check ✓ |

### 3. Residue Class Analysis

For p ≢ 1, 121, 169, 289, 361, 529 (mod 840), at least one of the Bradford Type II constructions for k ∈ {0, 1, 2} works:

- **k = 0**: m = 3, works when x₀ = (p+3)/4 has a prime factor ≡ 2 (mod 3)
- **k = 1**: m = 7, works when x₁ = (p+7)/4 has favorable factorization
- **k = 2**: m = 11, works when x₂ = (p+11)/4 has favorable factorization

## Requirements

1. **Define Mordell-hard classes**:
```lean
def MordellHardClasses : Finset ℕ := {1, 121, 169, 289, 361, 529}

def isNonMordellHardPrime (p : ℕ) : Prop :=
  Nat.Prime p ∧ p % 840 ∉ MordellHardClasses
```

2. **Prove small primes directly**:
```lean
lemma solution_2 : HasErdosStrausSolution 2 := by use 1, 2, 2; norm_num
lemma solution_5 : HasErdosStrausSolution 5 := by use 2, 4, 20; norm_num
lemma solution_7 : HasErdosStrausSolution 7 := by use 2, 28, 28; norm_num
-- etc.
```

3. **Prove the main theorem**:
```lean
theorem nonMordellHard_has_solution (p : ℕ) (hp : Nat.Prime p)
    (hnonMH : p % 840 ∉ MordellHardClasses) :
    HasErdosStrausSolution p
```

4. **Strategy**:
   - Handle p = 2, 3, 5, 7 explicitly
   - For p ≥ 11, use residue class analysis
   - Show that non-MH residue classes mod 840 have k ∈ {0,1,2} working

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

-- Small prime solutions
lemma solution_2 : HasErdosStrausSolution 2 := by use 1, 2, 2; norm_num
lemma solution_3 : HasErdosStrausSolution 3 := by use 1, 4, 12; norm_num
lemma solution_5 : HasErdosStrausSolution 5 := by use 2, 4, 20; norm_num
lemma solution_7 : HasErdosStrausSolution 7 := by use 2, 28, 28; norm_num
lemma solution_11 : HasErdosStrausSolution 11 := by use 3, 12, 132; norm_num
lemma solution_13 : HasErdosStrausSolution 13 := by use 4, 18, 468; norm_num

/-- Primes p ≡ 2 (mod 3) have solutions via Mordell's construction. -/
lemma prime_2_mod_3_has_solution (p : ℕ) (hp : Nat.Prime p) (hmod : p % 3 = 2) :
    HasErdosStrausSolution p := by
  sorry -- Use Type I construction

/-- Non-Mordell-hard primes all have Erdős-Straus solutions. -/
theorem nonMordellHard_has_solution (p : ℕ) (hp : Nat.Prime p)
    (hnonMH : p % 840 ∉ MordellHardClasses) :
    HasErdosStrausSolution p := by
  -- Case split on small primes, then use residue class analysis
  interval_cases p
  · exact solution_2
  · exact solution_3
  · exact solution_5
  · exact solution_7
  -- For larger primes, check if p ≡ 2 (mod 3)
  sorry

end ErdosStraus
```

## Output Requirements

- Complete Lean 4 file that compiles with Mathlib
- Handle small primes (2, 3, 5, 7, 11, 13, ...) explicitly with `norm_num`
- Use `sorry` for complex sub-cases if needed, but structure the proof
- The key insight: non-MH primes either have p ≡ 2 (mod 3) OR have k ∈ {0,1,2} working
