# GPT Prompt: Prove Type III Existence for Dyachenko

## Context
We are formalizing the Erdős-Straus conjecture in Lean 4 + Mathlib. The only remaining axiom is `dyachenko_type3_existence`. We have computationally verified that the theorem holds for all primes P < 10^8.

## The Theorem to Prove

```lean
def type3_x (p offset : ℕ) : ℕ := (p + offset) / 4

theorem dyachenko_type3_existence (p : ℕ) (hp : Nat.Prime p)
    (hp_mod : p % 4 = 1) (hp_ge : p ≥ 5) :
    ∃ offset c : ℕ,
      offset % 4 = 3 ∧
      c > 0 ∧
      (4 * c - 1) * offset > p ∧
      ((4 * c - 1) * offset - p) ∣ (4 * type3_x p offset * c * p) := by
  sorry
```

## Key Computational Observations

For all tested primes P ≡ 1 (mod 4):
1. **offset = 3 works for most primes** with c ≈ (p+15)/12
2. **offset = 7 works for exceptions** (P = 73, 193, ...)
3. The divisor is always small: typically 4 or 8

| P | offset | c | divisor = (4c-1)*offset - P |
|---|--------|---|------------------------------|
| 5 | 3 | 1 | 4 |
| 13 | 3 | 2 | 8 |
| 17 | 3 | 2 | 4 |
| 29 | 3 | 3 | 4 |
| 37 | 3 | 4 | 8 |
| 73 | **7** | 3 | 4 |
| 97 | 3 | 10 | 20 |
| 193 | **7** | 10 | 80 |

## The Divisibility Condition

For offset = 3:
- divisor = 12c - 3 - p
- dividend = 4 * ((p+3)/4) * c * p = c * p * (p+3)
- Need: divisor | c * p * (p+3)

For offset = 7:
- divisor = 28c - 7 - p
- dividend = 4 * ((p+7)/4) * c * p = c * p * (p+7)
- Need: divisor | c * p * (p+7)

## Proof Strategy

**Approach 1: Case split on p mod 12**
- For p ≡ 5 (mod 12): offset = 3, c = (p+7)/12 gives divisor = 4
- For p ≡ 1 (mod 12): offset = 3, c = (p+11)/12 gives divisor = 8
- For exceptions: offset = 7 with appropriate c

**Approach 2: Direct existence via divisibility**
- The divisor d = (4c-1)*offset - p divides c*p*(p+offset)
- For small d (like 4 or 8), this is easy since (p+offset) ≡ 0 (mod 4) when p ≡ 1 (mod 4)

## Your Task

Provide a complete Lean 4 proof of `dyachenko_type3_existence` using the following structure:

```lean
theorem dyachenko_type3_existence (p : ℕ) (hp : Nat.Prime p)
    (hp_mod : p % 4 = 1) (hp_ge : p ≥ 5) :
    ∃ offset c : ℕ,
      offset % 4 = 3 ∧
      c > 0 ∧
      (4 * c - 1) * offset > p ∧
      ((4 * c - 1) * offset - p) ∣ (4 * type3_x p offset * c * p) := by
  -- Case 1: Try offset = 3
  by_cases h : (can prove with offset = 3)
  · -- offset = 3 case
    use 3
    ...
  · -- offset = 7 fallback
    use 7
    ...
```

**Requirements**:
1. Complete Lean 4 proof with no sorries
2. Use Mathlib tactics: `omega`, `decide`, `norm_num`, `ring`, `simp`
3. Handle the case split cleanly
4. The proof should work for ALL p ≡ 1 (mod 4) with p ≥ 5

## Hints

1. For p ≡ 1 (mod 4), we have p + 3 ≡ 0 (mod 4), so (p+3)/4 is an integer
2. The divisibility often reduces to showing d | some_factor where d is small
3. You may need to use `Nat.dvd_of_mem_divisors` or construct explicit witnesses
4. Consider using `interval_cases` for small case analysis if needed

## Output Format

Provide ONLY the Lean proof code, starting with:
```lean
theorem dyachenko_type3_existence ...
```

No explanations needed - just working Lean 4 code.
