# Erdős Problem #125: Sumset Density Analysis

## Problem Statement

Let:
- A = {n : n has only digits 0,1 in base 3} = sums of distinct powers of 3
- B = {n : n has only digits 0,1 in base 4} = sums of distinct powers of 4 (Moser-de Bruijn)

**Question:** Does A + B have positive asymptotic density?

## Current State of the Art

| Result | Bound | Reference |
|--------|-------|-----------|
| Lower bound | \|C ∩ [1,x]\| ≫ x^0.965 | Melfi (2001) |
| Improved | \|C ∩ [1,x]\| ≫ x^0.9777 | Hasler-Melfi (2024) |
| Upper on lower density | ≤ 0.696 | Hasler-Melfi (2024) |

## Complement Structure (A367090)

The complement C' = ℕ \ (A+B) exhibits highly structured behavior.

### Run Statistics (first 1000 terms)

```
Total complement terms analyzed: 1000
Number of runs: 84

Run length distribution:
  Length 2: 54 occurrences
  Length 14: 2 occurrences
  Length 22: 1 occurrence
  Length 23: 10 occurrences
  Length 36: 17 occurrences

Gap distribution (between runs):
  Gap 62: 37 times
  Gap 79: 21 times
  Gap 253: 6 times
  Gap 515: 5 times
  Gap 144: 4 times
```

### Key Factorizations

- Run length 36 = 4 × 9 = 4 × 3²
- Run length 23 = 23 (prime)
- Gap 62 = 2 × 31
- Gap 144 = 16 × 9 = 4² × 3²

### First Runs

```
62-63 (length 2)
143-144 (length 2)
207-242 (length 36)
463-498 (length 36)
561-562 (length 2)
642-643 (length 2)
706-728 (length 23)
```

## Why Specific Numbers Are in the Complement

### Example: Why 62 ∉ A+B

For 62 = a + b with a ∈ A, we need b ∈ B:

| a | b=62-a | b in base 4 | b ∈ B? |
|---|--------|-------------|--------|
| 0 | 62 | 332 | ✗ |
| 1 | 61 | 331 | ✗ |
| 4 | 58 | 322 | ✗ |
| 13 | 49 | 301 | ✗ |
| 31 | 31 | 133 | ✗ |
| 40 | 22 | 112 | ✗ |

Every valid a ∈ A forces b to have forbidden digits (2 or 3) in base 4.

### Contrast: Why 61 ∈ A+B

61 = 40 + 21, where:
- 40 = 1111₃ ∈ A ✓
- 21 = 111₄ ∈ B ✓

## Pattern Analysis

### Base Representations of Complement Elements

```
n    | base3    | base4  | 2s_in_b3 | forbidden_b4
-----|----------|--------|----------|-------------
62   | 2022     | 332    | 3        | 3
63   | 2100     | 333    | 1        | 3
143  | 12022    | 2033   | 3        | 3
144  | 12100    | 2100   | 1        | 1
207  | 21200    | 3033   | 2        | 3
...
242  | 22222    | 3302   | 5        | 3
```

**Key observation:** Complement elements have BOTH high "2-count" in base 3 AND high "forbidden digit count" in base 4. This double-obstruction is what prevents representation.

### Near Powers of 3 and 4

Complement elements cluster near sums 3^a + 4^b:
- 62 = 64 - 2 = 4³ - 2
- 63 = 64 - 1 = 4³ - 1
- 143 = 145 - 2 = (81 + 64) - 2 = 3⁴ + 4³ - 2
- 144 = 145 - 1 = 3⁴ + 4³ - 1

### Scaling Property

Multiplying complement elements by 3 or 4 typically removes them from complement:
- 62 × 3 = 186 ∉ C'
- 62 × 4 = 248 ∉ C'
- 214 × 3 = 642 ∈ C' (rare exception)

This suggests the complement is "multiplicatively thin."

## M3 Attack Strategy

### Macro Architecture

The proof should show:
1. Runs in the complement have bounded length relative to their position
2. Gaps between runs grow (on average) faster than runs themselves
3. Therefore: density of complement → 0, so density of A+B → positive

### Micro Lemmas Needed

1. **Run Length Bound:** Show that run length L(n) at position n satisfies L(n) = O(n^α) for some α < 1.

2. **Gap Growth Lemma:** Show that average gap G(n) between runs near position n satisfies G(n) = Ω(n^β) for some β > 0.

3. **Double-Obstruction Decay:** The "bad region" where both base-3 and base-4 representations are far from {0,1}-only shrinks as n grows.

### Key Insight

The dimension sum log₃(2) + log₄(2) ≈ 1.13 > 1 suggests:
- A is "larger" than a set of dimension log₃(2) ≈ 0.631
- B is "larger" than a set of dimension log₄(2) = 0.5
- Their sum should be "full dimensional" (positive density)

The complement exists because of **resonances** between base-3 and base-4 digit restrictions, but these resonances become sparse at large scales.

## Computational Questions for AI

1. **Can we characterize which (a,b) pairs give 3^a + 4^b - k ∈ complement for small k?**

2. **Is there a finite automaton that generates the run length sequence [2,2,36,36,2,2,23,...]?**

3. **What is the spectral radius of the carry transducer when adding elements of A and B?**

4. **Does the self-similarity noted in A367090 correspond to a transfer operator with explicit eigenstructure?**

---

*Analysis generated: January 24, 2026*
*Method: M3 Computational Exploration*
*OEIS: A367090 (complement), A005836 (A), A000695 (B)*
