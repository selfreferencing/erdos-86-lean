# Refined Prompt for GPT-5.2: The 13 Hard Cases

## SUMMARY OF PROGRESS

We have made significant progress on proving `ten_k_cover_exists`. Here's what's been established:

### Coverage Analysis Results

**Total cases mod 210: 210**

1. **n odd (105 cases)**: FULLY COVERED
   - 2 | x_14 (since x_14 = n + 9)
   - 2 is a primitive root mod 59
   - Therefore ∃b: 2^b ≡ -x_14 (mod 59)

2. **n even, n ≡ 0 (mod 7) (15 cases)**: FULLY COVERED
   - 7 | x_5 (since x_5 = n)
   - 7 is a primitive root mod 23, 79, 107

3. **n even, n ≡ 2 (mod 7) (15 cases)**: FULLY COVERED
   - 7 | x_17 (since x_17 = n + 12)
   - 7 is a primitive root mod 71

4. **Other n even cases covered by prime products (62 cases)**: COVERED
   - Various combinations of primes generate full (Z/m_k)×

**Remaining: 13 "hard" cases mod 210**

---

## THE 13 HARD CASES

These values of n mod 210 are NOT covered by the primitive root analysis:

```
n ≡ 6, 8, 12, 18, 26, 36, 48, 62, 78, 96, 116, 138, 162, 188 (mod 210)
```

Wait - the output showed some additional cases covered. Let me list the truly hard ones:

```
UNCOVERED: 6, 8, 12, 18, 26, 36, 48, 62, 78, 96, 116, 138, 162, 188
```

### What makes these cases "hard"?

For each of these n values, every k ∈ K10 has the property that:
- The small prime factors of x_k (from {2, 3, 5, 7, 11, 13, 17, 19, 23}) generate a subgroup of **index 2** in (Z/m_k)×
- This means only half of residues are reachable as products of these primes
- If -x_k happens to be in the "wrong" coset, no small product works

---

## KEY STRUCTURAL OBSERVATION

For all 10 values of k ∈ K10, the subgroup index is exactly 2 for these hard cases. This is NOT a coincidence!

The quadratic residue subgroup Q ⊂ (Z/m)× always has index 2 (for odd prime m).
The subgroups ⟨generators⟩ that arise are related to Q.

**Hypothesis**: For the hard cases, the generators always land in the same coset (either all QR or all NQR).

---

## THE CORE QUESTION

For n in the hard cases, what ensures that -x_k IS reachable for at least one k?

**Option A**: Large prime factors
- x_k might have prime factors > 23 that complete the subgroup
- These large primes could be primitive roots or in the opposite coset

**Option B**: The target -x_k is in the reachable subgroup
- Even though the subgroup has index 2, perhaps -x_k is always in it for some k

**Option C**: Product structure
- The products 2^a × 3^b × 5^c × ... might cover -x_k by accident
- Even if the subgroup has index 2, maybe -x_k falls in the right half

---

## DETAILED DATA FOR HARD CASES

### n ≡ 6 (mod 210)

| k | m_k | x_k mod 210 | factors | |⟨factors⟩| | index |
|---|-----|-------------|---------|------------|-------|
| 5 | 23 | 6 | 2,3 | 11 | 2 |
| 7 | 31 | 8 | 2 | 5 | 6 |
| 9 | 39 | 10 | 2,5 | 12 | 2 |
| 11 | 47 | 12 | 2,3 | 23 | 2 |
| 14 | 59 | 15 | 3,5 | 29 | 2 |
| 17 | 71 | 18 | 2,3 | 35 | 2 |
| 19 | 79 | 20 | 2,5 | 39 | 2 |
| 23 | 95 | 24 | 2,3 | 36 | 2 |
| 26 | 107 | 27 | 3 | 53 | 2 |
| 29 | 119 | 30 | 2,3,5 | 48 | 2 |

For k=7: only factor 2, and ⟨2⟩ mod 31 has only 5 elements (index 6).
This is the smallest subgroup, making k=7 particularly constrained.

---

## WHAT NEEDS TO BE PROVED

For each hard case n mod 210, prove that at least one of:

1. **d1Sufficient holds for some k**: p ≡ 12k+5 (mod 16k+12)
   - This gives a witness d=1 directly

2. **-x_k is in the reachable subgroup for some k**
   - Compute -x_k mod m_k
   - Check if -x_k ∈ ⟨small primes dividing x_k⟩

3. **A large prime factor of x_k completes the group**
   - If x_k has a prime factor q > 23 with q ∉ ⟨small primes⟩ mod m_k
   - Then ⟨small primes, q⟩ might be the full group

---

## SPECIFIC COMPUTATIONAL TASK

For each hard case n ∈ {6, 8, 12, 18, 26, 36, 48, 62, 78, 96, 116, 138, 162, 188} mod 210:

1. **Compute** which Mordell-hard residues mod 840 map to this n mod 210
2. **For each such residue r**:
   - Compute p ≡ r (mod 840) implies x_k = (p + 4k + 3)/4
   - Determine -x_k mod m_k for each k
   - Check if -x_k ∈ ⟨prime factors of x_k mod 210⟩ mod m_k

**Key insight**: x_k mod m_k depends on p mod (4 × m_k), not just p mod 210.
So we need to analyze mod lcm(840, 4m_k) for each k.

---

## STRATEGY SUGGESTIONS

### Strategy 1: Coset analysis
For each k, the group (Z/m_k)× splits into two cosets: ⟨generators⟩ and its complement.
- Compute which coset -x_k falls into
- Show that across all k, the cosets "complement" each other

### Strategy 2: Large prime factor analysis
For x_k > 210², the value x_k has prime factors beyond just 2,3,5,7.
- These large factors might be primitive roots
- Or they might complete the subgroup to index 1

### Strategy 3: Direct finite verification
The constraint p ≡ r (mod 840) combined with n ≡ c (mod 210) gives p mod 840.
- For each of 6 Mordell-hard residues × 14 hard cases = 84 sub-cases
- Directly verify that at least one k works

---

## DELIVERABLE

Prove: For every Mordell-hard prime p, at least one k ∈ K10 has a witness d.

Methods:
1. Complete the coset analysis showing -x_k is always reachable for some k
2. OR reduce to a finite computation that can be verified in Lean via native_decide
3. OR identify the correct algebraic structure that guarantees coverage

**This is the ONLY remaining step to prove `ten_k_cover_exists`.**
