# GPT Prompts: Next Steps for Erdős-Straus

## Current State Summary

Extended witnesses achieve ~99.1% residue-class coverage, but ~0.9% remains uncovered. Explicit uncovered classes exist. Yet ESC holds for 100% of tested primes up to 10^18.

**The gap**: Something covers the "uncovered" 0.9%, but we don't know what.

**Key data**:
- M'' = 297,858,605,166,270,991,986,851,307,600 ≈ 2.98 × 10²⁹
- Explicit uncovered class: r ≡ 17,241,155,921,260,804,745,037,298,201 (mod M'')
- All 14 K13 failures certifiable with k ≤ 98, q ≤ 29

---

## PROMPT 9: Empirical Test of Uncovered Classes

**Estimated time: 30-45 minutes**

**THIS IS THE MOST INFORMATION-DENSE EXPERIMENT**

```
EMPIRICAL TEST OF "UNCOVERED" RESIDUE CLASSES

BACKGROUND:
We have shown that extended witnesses d = a·q^e (with a ∈ {1,2,3,4,6}, e ∈ {1,2}, q ≤ 29)
cover ~99.1% of residue classes mod M''.

An explicit UNCOVERED residue class is:
  r = 17,241,155,921,260,804,745,037,298,201

This satisfies:
  - r ≡ 1 (mod 24)
  - gcd(r, M'') = 1
  - r is NOT in any CRT-certified class C(k,q,a,e) for K13 × {q ≤ 29} × {a ∈ {1,2,3,4,6}} × {e ∈ {1,2}}

Yet by Dirichlet's theorem, infinitely many primes p ≡ r (mod M'') exist.
And ESC holds for all tested primes up to 10^18.

THE QUESTION: What witnesses do these "uncovered" primes actually use?

YOUR TASKS:

1. FIND A PRIME IN THE UNCOVERED CLASS:
   Compute the smallest prime p such that:
   - p ≡ r (mod M'') where r = 17,241,155,921,260,804,745,037,298,201
   - p ≡ 1 (mod 4)

   (This may require searching p = r + k·M'' for small k ≥ 0)

2. VERIFY ESC FOR THIS PRIME:
   For this prime p, search for ANY k ≥ 0 such that:
   - x_k = (p + m_k)/4 where m_k = 4k + 3
   - There exists d | x_k² with d ≡ -x_k (mod m_k)

   Search k = 0, 1, 2, 3, ... until a witness is found.

3. ANALYZE THE WITNESS:
   When you find the witness (k, d):
   - What is k? Is it small or large?
   - What is the factorization of d?
   - Can d be written as a·q^e for small a and prime q?
   - Or is d a more complex composite (like 2·5²·7²)?

4. PATTERN IDENTIFICATION:
   If time permits, repeat for 2-3 more primes in the uncovered class.

   Questions:
   - Do they all use similar k values?
   - Do the witnesses share structural features?
   - Is there a pattern that suggests a richer witness family?

5. THE CRITICAL QUESTION:
   Based on what you find, propose:
   - Either: An expanded witness family W' that would cover this class
   - Or: Evidence that no fixed finite (K, W) can achieve complete coverage

PROVIDE:
1. The smallest prime p in the uncovered class (or bounds on its size)
2. The certifying (k, d) pair for this p
3. The structure of d (factorization, whether it fits a·q^e template)
4. Assessment: What does this tell us about the gap between fixed-witness and existential coverage?
```

---

## PROMPT 10: Witness Structure Analysis

**Estimated time: 20-30 minutes**

```
WITNESS STRUCTURE ANALYSIS FOR K13 FAILURES

BACKGROUND:
The 14 K13 failures all have witnesses, but with varying structures:

| p | k | witness d | factorization |
|---|---|-----------|---------------|
| 10,170,169 | 3 | 29 | prime |
| 11,183,041 | 32 | 9 | 3² |
| 22,605,361 | 37 | 1,156 | 2² · 17² |
| 24,966,481 | 31 | 17 | prime |
| 30,573,481 | 89 | 9 | 3² |
| 30,619,801 | 98 | 51 | 3 · 17 |
| 30,619,801 | 39 | 2,450 | 2 · 5² · 7² |
| 34,103,161 | 41 | 19 | prime |
| 35,241,529 | 47 | 18 | 2 · 3² |
| 36,851,929 | 72 | 5 | prime |
| 36,869,281 | 39 | 29 | prime |
| 37,228,801 | 41 | 2 | prime |
| 45,575,401 | 39 | 50 | 2 · 5² |
| 46,936,849 | 27 | 14 | 2 · 7 |
| 48,991,849 | 13 | 29 | prime |

YOUR TASKS:

1. CLASSIFY WITNESS TYPES:
   Group the witnesses by structure:
   - Type A: Prime (q)
   - Type B: Prime square (q²)
   - Type C: a · q² for small a
   - Type D: a · q for small a
   - Type E: Products of squared primes (a · s² where s = ∏qᵢ)
   - Type F: Other

2. IDENTIFY THE "HARD" CASES:
   Which witnesses DON'T fit the template a · q^e for a ∈ {1,2,3,4,6}, q prime?

   For example: d = 2,450 = 2 · 5² · 7² = 2 · (35)²
   This is a · s² where s = 35 is composite.

3. PROPOSE AN EXTENDED WITNESS FAMILY:
   Based on the observed patterns, define a witness family W' that captures ALL observed cases.

   Candidate: W' = {a · s² : a ∈ {1,2,4}, s squarefree with prime factors from {2,3,5,7,11,13}}

   - Does this family cover all 14 failures?
   - What's the corresponding master modulus?
   - Can this be made into a CRT-checkable system?

4. THE MINIMALITY QUESTION:
   What's the SMALLEST witness family W such that:
   - All 14 K13 failures have witnesses in W (for some k ≤ 100)
   - W is finite and explicitly enumerable

5. STRUCTURAL INSIGHT:
   Is there a pattern relating:
   - The prime p
   - The required k
   - The structure of the witness d

   For instance: Do "harder" primes (larger k needed) tend to need more complex witnesses?

PROVIDE:
1. Classification of all 14 witnesses
2. The minimal witness family W covering all cases
3. Whether W' = {a · s² : ...} suffices
4. Any structural patterns relating p, k, and d
```

---

## PROMPT 11: Divisor Reach Theorem

**Estimated time: 30-45 minutes**

**THIS COULD BE THE "MAJOR NEW INGREDIENT"**

```
DIVISOR REACH THEOREM FOR MODULAR COVERAGE

BACKGROUND:
For a positive integer n and modulus m with gcd(n,m) = 1, define:
  R(n², m) = {d mod m : d | n²}

This is the set of residue classes mod m hit by divisors of n².

Key observations:
- |R(n², m)| grows with ω(n) (number of distinct prime factors)
- For n with many prime factors, R(n², m) can cover most/all of (Z/mZ)*
- The "trapped" primes in ESC are those where R(x_k², m_k) misses the target -x_k

THE QUESTION: Is there a theorem guaranteeing eventual coverage?

YOUR TASKS:

1. LITERATURE SEARCH:
   Are there known results of the form:

   "For any m and any r ∈ (Z/mZ)*, if n > f(m), then n² has a divisor d ≡ r (mod m)"?

   Or: "For n with ω(n) > g(m), the set R(n², m) = (Z/mZ)*"?

2. THE COVERING CONDITION:
   For fixed m, define:
     N(m) = min{n : R(n², m) = (Z/mZ)*}

   - Can you bound N(m) in terms of m?
   - Is N(m) finite for all m?
   - What's the growth rate?

3. THE ESC APPLICATION:
   For ESC with modulus m_k = 4k + 3, we have:
     x_k = (p + m_k)/4 ≈ p/4 for large p

   If x_k > N(m_k), then R(x_k², m_k) = (Z/m_k)*, so EVERY residue class is hit.

   This would mean: For p > 4·N(m_k), prime p has a witness at k.

   - Can this give a "large p" theorem for ESC?
   - What's the threshold p₀ such that all p > p₀ have witnesses?

4. THE MULTI-MODULUS VERSION:
   For ESC, we need coverage across multiple moduli simultaneously.

   Define: For K = {k₁, ..., kₙ}, let M = ∏m_kᵢ.

   Question: Is there N(K) such that for all p > N(K), at least one k ∈ K has a witness?

5. CONNECTION TO SMOOTHNESS:
   The "trapped" primes have x_k with few prime factors (all in QR kernel).

   Is there a theorem like:
   "For x > X₀, the integer x has either a non-QR prime factor mod m, OR ω(x) > log log x"?

   This could show that "trapping" becomes impossible for large x.

6. IF NO SUCH THEOREM EXISTS:
   Sketch what such a theorem would need to say, and identify the gap in current knowledge.

PROVIDE:
1. Any known results on "divisor reach" for modular coverage
2. Bounds on N(m) if known
3. Whether this gives a "large p" theorem for ESC
4. The key lemma needed if no theorem currently exists
```

---

## PROMPT 12: Uncovered Class Rescue (Detailed)

**Estimated time: 45-60 minutes**

```
DETAILED RESCUE OF UNCOVERED RESIDUE CLASSES

BACKGROUND:
Extended witnesses with K13 × {q ≤ 29} × {a ∈ {1,2,3,4,6}} × {e ∈ {1,2}} leave ~0.9% of residue classes uncovered.

Explicit uncovered class: r ≡ 17,241,155,921,260,804,745,037,298,201 (mod M'')

Where M'' = 2⁴ · 3² · 5² · 7² · 11² · 13² · 17² · 19² · 23² · 29 · 31 · 47 · 59 · 71 · 79 · 107

YOUR TASKS:

1. ANALYZE THE UNCOVERED CLASS:
   For r = 17,241,155,921,260,804,745,037,298,201:

   - Compute r mod m_k for each k ∈ K13
   - What is the "target" -x_k mod m_k for primes p ≡ r?
   - Why does no (k, q, a, e) certificate exist?

2. FIND A RESCUING k:
   Using the "divisor trick" from earlier prompts:

   For small primes q (say q ≤ 100), compute:
     r + 4q mod m_k for various k

   A candidate k exists when m_k | (r + 4q) for some m_k ≡ 3 (mod 4).

   Find the SMALLEST k ∉ K13 that could certify this residue class.

3. EXPLICIT CERTIFICATE:
   For the rescuing k found above:
   - What q makes the certificate work?
   - What is the extended witness d = a · q^e?
   - Verify: the CRT class C(k, q, a, e) contains r

4. COVERAGE CLOSURE:
   If you add this new k to K, what's the new coverage?

   - Does adding one k close the gap significantly?
   - Are there patterns in which k values rescue which uncovered classes?

5. THE SYSTEMATIC APPROACH:
   Propose an algorithm:

   Input: Set of uncovered residue classes U mod M''
   Output: Minimal set K' ⊃ K13 such that K' × W covers all of U

   Can this be done greedily? Is there structure to exploit?

6. THE FINITENESS QUESTION:
   After adding rescuing k values for the ~0.9% uncovered:
   - Do NEW uncovered classes appear (at the expanded modulus)?
   - Or does the process terminate?

   This is crucial: if it terminates, we have a proof path.

PROVIDE:
1. Analysis of why r is uncovered by current (K, W)
2. The smallest rescuing k for this residue class
3. The explicit certificate (k, q, a, e)
4. Assessment of whether iterating this process could terminate
```

---

## PROMPT 13: Covering Congruence Connection

**Estimated time: 30-45 minutes**

```
COVERING CONGRUENCE FRAMEWORK FOR ESC

BACKGROUND:
A covering system is a set of congruences {aᵢ (mod nᵢ)} such that every integer satisfies at least one.

The Erdős covering conjecture (proved 2015 by Hough) states that for any N, there exists a covering system with all moduli > N.

ESC has a similar flavor: we want to show every prime p ≡ 1 (mod 4) is "covered" by some k.

THE CONNECTION:
For each k, define the "good" set G_k = {p : k provides a Type II witness for p}.

ESC is equivalent to: ∪_{k≥0} G_k contains all primes p ≡ 1 (mod 4).

YOUR TASKS:

1. CHARACTERIZE G_k:
   For fixed k with m_k = 4k + 3:

   G_k = {primes p : ∃d | x_k² with d ≡ -x_k (mod m_k)}

   Can G_k be described as a union of arithmetic progressions?
   What's the structure of the "bad" set (complement of G_k)?

2. THE COVERING QUESTION:
   Is ESC equivalent to:

   "The family {G_k : k ≥ 0} is a covering of primes p ≡ 1 (mod 4)"?

   If so, what properties of this family can we exploit?

3. DENSITY CONSIDERATIONS:
   For each k:
   - What's the density of G_k among primes p ≡ 1 (mod 4)?
   - How does this density behave as k → ∞?
   - Does ∑_k density(G_k) diverge? (necessary but not sufficient for covering)

4. THE FINITE K QUESTION:
   The Erdős covering theorem shows finite coverings exist.

   For ESC: Does there exist a FINITE set K such that ∪_{k∈K} G_k covers all relevant primes?

   Or must K be infinite?

5. HOUGH'S TECHNIQUE:
   The 2015 proof of Erdős covering uses probabilistic and combinatorial methods.

   Can any of these techniques be adapted to ESC?
   What's the analogous "random covering" model?

6. THE GAP BETWEEN COVERING AND CERTIFICATION:
   We've seen:
   - Fixed-witness certification: ~99.1% coverage
   - Existential coverage: 100% (empirically to 10^18)

   Is this gap analogous to known phenomena in covering theory?
   Are there "covering systems" that can't be explicitly enumerated but provably exist?

PROVIDE:
1. Structure of G_k as arithmetic progressions (if possible)
2. Connection to classical covering congruences
3. Whether Hough-type techniques might apply
4. Assessment of finite vs infinite K requirement
```

---

## PROMPT 14: The Parametric Family Approach (Alternative Path)

**Estimated time: 30-45 minutes**

```
PARAMETRIC FAMILIES FOR ESC HARD CASES

BACKGROUND:
We've focused on Type II witnesses (the Bradford approach). But ESC has multiple parametric families that work for specific residue classes:

- Mordell family: Works for p ≡ 2 (mod 3)
- Schinzel family: Works for p ≡ 3 (mod 4)
- Yamamoto family: Works for various residue classes

The "hard" cases are p ≡ 1 (mod 840), where these families don't directly apply.

THE QUESTION: Can parametric families handle what modular covering can't?

YOUR TASKS:

1. CATALOG KNOWN FAMILIES:
   List all known parametric families for ESC with their coverage:

   | Family | Residue condition | Coverage |
   |--------|-------------------|----------|
   | Mordell | p ≡ 2 (mod 3) | ~1/2 of primes |
   | ... | ... | ... |

2. THE p ≡ 1 (mod 840) CASE:
   Our 14 K13 failures all have p ≡ 1 (mod 840).

   - Which parametric families apply to this class?
   - If none directly apply, why not?

3. CONSTRUCTING NEW FAMILIES:
   For p ≡ 1 (mod 840), can we find (x,y,z) parametrically?

   Try: x = f(p), y = g(p), z = h(p) for polynomial or rational functions.

   What constraints do we get? Can they be satisfied?

4. THE RECIPROCITY WALL:
   Earlier analysis mentioned a "reciprocity wall" blocking parametric approaches.

   - What exactly is this wall?
   - Can it be characterized precisely?
   - Are there ways around it?

5. HYBRID APPROACH:
   Can we combine:
   - Parametric families for "easy" residue classes
   - Modular covering for "medium" residue classes
   - Something new for the ~0.9% uncovered?

   What would "something new" need to look like?

6. THE ALGEBRAIC GEOMETRY ANGLE:
   ESC is equivalent to finding rational points on certain surfaces.

   - What's the geometric structure of these surfaces?
   - Are there known results about rational point density?
   - Does the Brauer-Manin obstruction apply?

PROVIDE:
1. Catalog of parametric families and their coverage
2. Why p ≡ 1 (mod 840) is hard for all of them
3. Whether a new parametric family could exist for this class
4. The key obstruction (reciprocity wall or other)
```

---

## Execution Strategy

**Priority order:**

1. **Prompt 9** (Empirical Test) - Most information-dense, reveals what we're actually missing
2. **Prompt 11** (Divisor Reach) - Could provide the "major new ingredient"
3. **Prompt 10** (Witness Structure) - Helps design better witness families
4. **Prompt 12** (Uncovered Rescue) - Tests whether iteration terminates
5. **Prompt 13** (Covering Congruence) - Theoretical framework
6. **Prompt 14** (Parametric) - Alternative approach if modular covering stalls

**Key decision point:**

After Prompts 9 and 11:
- If uncovered primes use "bounded" witnesses → expand W and iterate
- If witnesses grow unboundedly with p → need divisor reach theorem
- If no pattern emerges → may need fundamentally different approach

**Success criteria:**

- Find that some finite (K, W) achieves UNCOVERED = ∅ → proof path clear
- Prove divisor reach theorem → large-p theorem + computation = proof
- Both fail → document the obstacle for future work
