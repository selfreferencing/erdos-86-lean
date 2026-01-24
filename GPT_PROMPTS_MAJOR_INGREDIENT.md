# GPT Prompts: Finding the Major New Ingredient for Erdős-Straus

## ⚠️ CRITICAL UPDATE: Prompt 0 → 0' → 0'' Evolution

### Prompt 0: FLAWED
Coverage is **NOT** a residue-class property. The condition "∃d | x_k² with d ≡ -x_k (mod m_k)" depends on the *divisor structure* of x_k.

**Verified Counterexamples:**
- k=0: p=73 and p=97 both ≡ 1 (mod 3), but k=0 fails for p=73 and succeeds for p=97
- k=1: p=29 and p=113 both ≡ 1 (mod 28), but k=1 fails for p=29 and succeeds for p=113

### Prompt 0' (REPAIRED): INSUFFICIENT
Fix specific small primes q as witnesses. Coverage becomes a residue-class property via CRT.

**Problem:** K13 × {prime q ≤ 29} covers **NONE** of the 14 K13 failures!
- p = 30,619,801 cannot be certified by ANY prime witness q ≤ 29 for ANY k
- It requires **composite** divisors like d = 2 · 109357²

### Prompt 0'' (EXTENDED WITNESSES): CURRENT APPROACH
Extend witnesses from single primes to composite forms: d ∈ {q, q², 2q², 4q², ...}

**Key questions:**
1. Can K13 × (extended witnesses) certify all 14 failures?
2. Is finite K × W sufficient for complete coverage?
3. What's the minimal (K, W) achieving completeness?

---

## Context for All Prompts

We have established the following verified facts about Erdős-Straus:

1. **The Problem**: For prime p, find x,y,z with 4/p = 1/x + 1/y + 1/z

2. **The Reduction**: For each k, set m_k = 4k+3, x_k = (p + m_k)/4. A Type II witness exists iff some divisor d | x_k² satisfies d ≡ -x_k (mod m_k).

3. **The Obstruction**: This is equivalent to finding d ≡ r_k (mod m_k) where r_k = -1/4 (mod m_k). Since m_k ≡ 3 (mod 4), r_k is always a quadratic NON-residue.

4. **Character Kernel Trapping**: If ALL prime factors of x_k are quadratic residues mod m_k, then ALL divisors are QRs, so no divisor can hit the non-QR target r_k.

5. **K13 Failures**: There are exactly 14 primes p < 50M where K13 = {0,1,2,5,7,9,11,14,17,19,23,26,29} fails. These are primes where x_k is "trapped" for ALL 13 values of k simultaneously.

6. **The Precise Question**: For a fixed finite K, can we prove that for every t with 4t-3 prime, at least one t+k has a divisor in the non-residue class r_k (mod m_k)?

---

## PROMPT 0: Residue Class Completeness Check (⚠️ FLAWED - SEE 0' BELOW)

**Estimated time: 45-60 minutes**

**⚠️ THIS APPROACH HAS A FATAL FLAW - Coverage is not a residue-class property!**
**See PROMPT 0' for the corrected version.**

```
The Erdős-Straus conjecture via modular covering reduces to a FINITE COMPUTATION:

SETUP:
- K = {0, 1, 2, 5, 7, 9, 11, 14, 17, 19, 23, 26, 29} (K13)
- For each k, m_k = 4k+3
- M = lcm(m_k : k ∈ K13) = lcm(3, 7, 11, 23, 31, 39, 47, 59, 71, 79, 95, 107, 119)

CRITERION FOR A COMPLETE PROOF:
A prime p is "covered" by k if there exists a divisor d | x_k² with d ≡ -x_k (mod m_k),
where x_k = (p + m_k)/4.

This reduces to: p mod m_k must lie in a "certifying set" R_k for that modulus.

THE KEY THEOREM:
If EVERY reduced residue class r mod M with:
  - r ≡ 1 (mod 24), AND
  - gcd(r, M) = 1
is covered by at least one k ∈ K, then ALL primes are covered by K.

YOUR TASKS:

1. COMPUTE M = lcm(3, 7, 11, 23, 31, 39, 47, 59, 71, 79, 95, 107, 119).
   Factor each: 39 = 3×13, 95 = 5×19, 119 = 7×17
   So M = lcm involves primes {3, 5, 7, 11, 13, 17, 19, 23, 31, 47, 59, 71, 79, 107}

2. For each k ∈ K13, determine the "certifying set" R_k ⊆ (Z/m_k)*:
   R_k = {r mod m_k : there exists d | ((r + m_k)/4)² with d ≡ -(r + m_k)/4 (mod m_k)}

   Note: This is equivalent to asking when x = (r + m_k)/4 has a divisor in residue class -x mod m_k.

3. Using CRT, lift each R_k to residue classes mod M.
   Let C_k = {r mod M : r mod m_k ∈ R_k} (the classes covered by k).

4. Compute C = ∪_{k ∈ K13} C_k (all covered classes).

5. Let U = {r mod M : r ≡ 1 (mod 24), gcd(r,M) = 1, r ∉ C} (uncovered classes).

6. THE DECISION:
   - If U = ∅, then K13 covers ALL primes. PROOF COMPLETE.
   - If U ≠ ∅, then by Dirichlet's theorem, infinitely many primes lie in uncovered classes.

7. If U ≠ ∅, find the SMALLEST extension K' = K13 ∪ {k₁, k₂, ...} such that U becomes empty.
   This gives the minimal K that covers all primes.

IMPORTANT COMPUTATIONAL NOTES:
- M is large but finite. φ(M) is the number of reduced residue classes.
- The sets R_k can be computed explicitly for each small m_k.
- For m_k prime, R_k has a clean characterization via quadratic characters.

PROVIDE:
1. The explicit value of M
2. φ(M)
3. The number of classes with r ≡ 1 (mod 24) and gcd(r,M) = 1
4. For at least k = 0, 1, 2: the explicit sets R_k
5. An estimate or exact count of |U| for K13
6. If |U| > 0, which additional k values would make U empty?
```

---

## PROMPT 0' (REPAIRED): Fixed-Witness Residue Class Coverage (NEW HIGHEST PRIORITY)

**Estimated time: 45-60 minutes**

**THIS IS THE CORRECTED VERSION OF PROMPT 0**

The original approach failed because coverage depends on factorization. The repair: fix specific small primes q as witness divisors, making coverage a true residue-class property.

```
REPAIRED ERDŐS-STRAUS FINITE COMPUTATION

BACKGROUND (Critical Insight):
The condition "∃d | x_k² with d ≡ -x_k (mod m_k)" is NOT a residue-class property.
Counterexample: p=73 and p=97 both ≡ 1 (mod 3), but k=0 fails for p=73 and succeeds for p=97.

THE REPAIR:
For a fixed small prime q, the conditions:
  1. q | x_k  ⟺  p ≡ -m_k (mod 4q)
  2. q ≡ -x_k (mod m_k)  ⟺  p ≡ -4q (mod m_k)
combine via CRT to give a SINGLE residue class mod 4q·m_k.

This IS a residue-class property! A pair (k, q) "certifies" all primes in that class.

SETUP:
- K = {0, 1, 2, 5, 7, 9, 11, 14, 17, 19, 23, 26, 29} (K13)
- For each k ∈ K, m_k = 4k+3
- For each small prime q (say q ≤ 29), compute the certified residue class C(k,q)

YOUR TASKS:

1. For k=0 (m=3), enumerate small primes q with gcd(q, 3) = 1:
   For each q ∈ {2, 5, 7, 11, 13, 17, 19, 23, 29}:
   - Condition 1: p ≡ -3 (mod 4q)
   - Condition 2: p ≡ -4q (mod 3)
   - CRT solution: p ≡ ? (mod 12q)
   List all certified classes.

2. Similarly for k=1 (m=7) and k=2 (m=11).

3. For each (k, q) pair, let C(k,q) be the certified residue class.
   The modulus is 4q·m_k.

4. Compute M' = lcm(4q·m_k : all pairs (k,q) with k ∈ K13, q ≤ Q)
   for some cutoff Q (start with Q = 29).

5. Lift each C(k,q) to residue classes mod M'.
   Let COVERED = ∪ (all lifted certified classes).

6. Let UNCOVERED = {r mod M' : r ≡ 1 (mod 24), gcd(r, M') = 1, r ∉ COVERED}.

7. THE KEY QUESTIONS:
   (a) Is UNCOVERED empty for some choice of K and Q?
   (b) If not, what happens as we increase K or Q?
   (c) Can you prove UNCOVERED eventually becomes empty?

8. IMPORTANT: The 14 K13 failures are:
   10170169, 11183041, 22605361, 24966481, 30573481, 30619801,
   34103161, 35241529, 36851929, 36869281, 37228801, 45575401,
   46936849, 48991849

   For each failure p, find which (k, q) pair certifies it.
   This tells us what's MISSING from K13's coverage.

PROVIDE:
1. For k=0,1,2: the certified residue classes for q ∈ {2,3,5,7,11,13}
2. Which (k,q) pairs from K13 × {q ≤ 29} cover the 14 failures
3. An estimate of the coverage fraction
4. A strategy for showing complete coverage (or proving impossibility)
```

---

## PROMPT 0'' (EXTENDED WITNESSES): Beyond Single Primes

**Estimated time: 45-60 minutes**

**THIS EXTENDS PROMPT 0' TO HANDLE THE HARD CASES**

Prompt 0' found that K13 × {prime q ≤ 29} covers NONE of the 14 K13 failures when using only prime witnesses. The critical case is p = 30,619,801 which cannot be certified by ANY prime q ≤ 29 for ANY k. It requires composite divisors like d = 2 · 109357².

**THE EXTENSION:** Include composite witnesses d ∈ {q, q², 2q, 2q², 3q, 3q², ...} for small primes q.

```
EXTENDED WITNESS ERDŐS-STRAUS COMPUTATION

BACKGROUND (Why Prime Witnesses Are Insufficient):
The condition for (k, q) to certify prime p is:
  1. q | x_k where x_k = (p + m_k)/4
  2. q ≡ -x_k (mod m_k)

But p = 30,619,801 fails ALL prime witness checks for K13:
- For each k ∈ K13, let x_k = (p + m_k)/4
- For no k does x_k have a prime factor q with q ≡ -x_k (mod m_k)

YET p = 30,619,801 IS covered by k=31 (m=127) using the COMPOSITE divisor:
  d = 2 · 109357² (where 109357 is prime)

THE EXTENSION:
For small primes q and small multipliers a ∈ {1, 2, 3, 4, 6}, consider witnesses:
  d = a · q^e where e ∈ {1, 2}

Condition for (k, q, a, e) to certify p:
  1. q | x_k (ensures q^e | x_k²)
  2. gcd(a, m_k) = 1 AND a | x_k² (ensures a · q^e | x_k²)
  3. a · q^e ≡ -x_k (mod m_k)

For fixed (k, q, a, e), this becomes a CRT condition on p.

YOUR TASKS:

1. STRESS TEST: For p = 30,619,801:
   - Compute x_k for each k ∈ {31, 39, 41}
   - Find the witness d | x_k² with d ≡ -x_k (mod m_k)
   - Express d as a · q^e and identify (q, a, e)

2. EXTENDED WITNESS CLASSES:
   For k = 0 (m = 3), enumerate witnesses d ∈ {q, q², 2q, 2q², 4q, 4q²}:
   For each (q, a, e) with q ∈ {2, 5, 7, 11}, a ∈ {1, 2, 4}, e ∈ {1, 2}:
   - Compute the CRT condition on p
   - List the certified residue class

3. COVERAGE OF K13 FAILURES:
   For each of the 14 K13 failures:
   10170169, 11183041, 22605361, 24966481, 30573481, 30619801,
   34103161, 35241529, 36851929, 36869281, 37228801, 45575401,
   46936849, 48991849

   Find a certifying tuple (k, q, a, e) where:
   - k ∈ K13 ∪ {31, 39, 41, ...}
   - d = a · q^e is a witness for that k

   QUESTION: Can ALL 14 be certified with k ∈ K13 if we allow composite witnesses?
   Or do we NEED k ∉ K13?

4. MODULUS GROWTH:
   For prime-only witnesses, modulus is 4q · m_k.
   For extended witnesses, modulus is lcm(4q, 4a) · m_k = 4·lcm(q,a) · m_k.

   How does this affect the CRT computation?
   What is the new master modulus M''?

5. COVERAGE ESTIMATE:
   With extended witnesses d ∈ {q, q², 2q², 4q², ...} for q ≤ 29:
   - Estimate the fraction of residue classes mod M'' that are covered
   - Is complete coverage achievable?

6. THE CRITICAL QUESTION:
   Is there a FINITE set of extended witnesses W = {(q_i, a_i, e_i)} such that:

   K13 × W covers ALL residue classes r ≡ 1 (mod 24) with gcd(r, M'') = 1?

   If yes: PROOF COMPLETE.
   If no: What's the minimal extension K' ⊃ K13 such that K' × W achieves coverage?

7. THEORETICAL BOUND:
   For large p, x_k ≈ p/4, so x_k² ≈ p²/16.
   The divisors of x_k² up to x_k are those d with d ≤ √(x_k²) = x_k.

   How many residue classes mod m_k can be hit by divisors ≤ x_k?
   Does this grow with p, ensuring eventual coverage?

PROVIDE:
1. The witness (k, q, a, e) certifying p = 30,619,801
2. For k=0: all certified classes using extended witnesses with q ≤ 11
3. Which of the 14 failures can be certified with K13 using extended witnesses
4. Coverage fraction estimate with extended witnesses
5. Assessment: Is finite K × W sufficient, or is something more needed?
```

---

## PROMPT 1: Zero-Sum / Davenport Constant Approach (Deep Theory)

**Estimated time: 30-45 minutes**

```
I'm working on the Erdős-Straus conjecture via a modular covering approach. The key obstruction has been reduced to:

For each k, m_k = 4k+3. A witness exists at k iff x_k = (p+m_k)/4 has a prime factor that's a quadratic NON-residue mod m_k.

The 14 known failures for K13 are primes where ALL prime factors of x_k lie in the QR subgroup for k=0,1,2 (moduli 3, 7, 11).

QUESTION: Can zero-sum theory / Davenport constants provide the "major new ingredient"?

Specifically:

1. Consider the group G = ∏_{k∈K} (Z/m_k)* / QR(m_k)
   This is a product of Z/2 groups (one for each odd prime factor of each m_k).

   For K13, what is this group? What is its Davenport constant D(G)?

2. The Davenport constant D(G) is the smallest d such that any sequence of d elements in G has a zero-sum subsequence.

   THEOREM ATTEMPT: If x has more than D(G) distinct prime factors (counted with multiplicity across all x_k), then some x_k must have a divisor in the non-QR coset.

   Is this theorem true? Can you prove or disprove it?

3. For the product group arising from K13, compute or bound D(G).

   If D(G) = N, then any x with > N prime factors would automatically escape the trap.
   Can we prove that for large enough p, some x_k has enough prime factors?

4. Can you find a finite K such that D(G_K) is small enough that escape is GUARANTEED for all p above some threshold?

Work through the group theory carefully. This could be the key.
```

---

## PROMPT 2: Chebotarev Density and Finiteness (Analytic Number Theory)

**Estimated time: 20-30 minutes**

```
The Erdős-Straus failures for K13 occur when:
- For k=0: ALL prime factors of x_0 ≡ 1 (mod 3)
- For k=1: ALL prime factors of x_1 are QRs mod 7
- For k=2: ALL prime factors of x_2 are QRs mod 11

Let S_k(m) = {primes p : all prime factors of (p+m)/4 lie in QR(m)}

QUESTIONS:

1. Using Chebotarev density theorem, what is the density of S_0(3) ∩ S_1(7) ∩ S_2(11)?

2. Is this intersection FINITE or INFINITE?

3. More generally, for a finite set K, let S_K = ∩_{k∈K} S_k(m_k).
   - Can you characterize exactly which primes are in S_K?
   - Is there a K such that S_K is FINITE (or even EMPTY)?

4. The key constraint: x_k = t + k where t = (p+3)/4 and 4t-3 = p is prime.
   This is NOT a random integer - it's constrained by p being prime.

   Does this constraint help? Can we use sieve methods or the large sieve to show S_K is finite for some K?

5. THEOREM ATTEMPT: For K large enough, the conditions "all factors of x_k are QRs mod m_k for all k∈K" become mutually exclusive.

   Can you prove this? What's the structure of the mutual exclusion?

Provide detailed calculations, not just heuristics.
```

---

## PROMPT 3: Prime Factor Distribution in Linear Forms (Deep Dive)

**Estimated time: 30-40 minutes**

```
For the Erdős-Straus conjecture, I need to understand when t+k (for k=0,1,...,29) has prime factors in specific residue classes.

Here t = (p+3)/4 where p is prime, so t is constrained.

QUESTIONS:

1. KNOWN RESULTS: What theorems exist about prime factors of n+k for consecutive k?
   - Grimm's conjecture
   - Results on largest prime factor of n(n+1)...(n+k)
   - Erdős-Selfridge type results

2. For a single k, let P_k = set of primes q where q | (t+k) implies q is a QR mod m_k.
   What is the density of P_k among all primes?

   For k=0, m_0=3: P_0 = primes ≡ 1 (mod 3), density = 1/2
   For k=1, m_1=7: P_1 = QRs mod 7 = {primes ≡ 1,2,4 mod 7}, density = 3/6 = 1/2

   In general, for prime m_k, density = 1/2.

3. INDEPENDENCE QUESTION: If we choose K = {k_1, ..., k_n} with all m_{k_i} prime and pairwise coprime, are the events "all factors of t+k_i are in P_{k_i}" approximately independent?

4. If independent with density 1/2 each, then P(all trapped) ≈ 2^{-n}.
   For n=13, this gives ≈ 1/8192.
   Among primes p ≡ 1 (mod 840) up to 50M, there are ~8500.
   Expected failures ≈ 1. We observe 14.

   WHY IS THE ACTUAL COUNT HIGHER? What correlation structure exists?

5. THEOREM ATTEMPT: The constraints are NOT independent. Specifically:
   - t+0, t+1, t+2 share small prime factors with probability > independent
   - This creates positive correlation in trapping

   Can you quantify this correlation and show it's bounded?

6. CRITICAL QUESTION: Is there a set K where the constraints become NEGATIVELY correlated (making simultaneous trapping impossible)?
```

---

## PROMPT 4: Direct Incompatibility Proof (Constructive)

**Estimated time: 40-50 minutes**

```
I want to prove directly that certain obstruction conditions are INCOMPATIBLE.

Setup: For k, obstruction occurs when all prime factors of x_k = t+k lie in QR(m_k).

SPECIFIC QUESTION: Can we prove that for any t, it's IMPOSSIBLE for:
- All prime factors of t ≡ 1 (mod 3), AND
- All prime factors of t+1 are QRs mod 7, AND
- All prime factors of t+2 are QRs mod 11, AND
- [additional conditions for other k]

APPROACH 1: GCD Coupling
Since gcd(t+a, t+b) | (a-b), any prime q > 29 divides at most one of t, t+1, ..., t+29.
Can this create incompatibility?

Example: If q | t with q ≡ 2 (mod 3), then t escapes the k=0 trap.
But what if no such q divides t?

APPROACH 2: Residue Class Forcing
If t ≡ a (mod M) for some large M, what constraints does this put on the prime factors of t, t+1, ..., t+29?

APPROACH 3: Smooth Number Exclusion
From computational data, gaps between 29-smooth numbers exceed 25 for n > 4.25×10^9.
So for t > 4.25×10^9, at least 28 of t, t+1, ..., t+29 have a prime factor > 29.

Let q_k be the largest prime factor of t+k. These q_k are distinct (by GCD coupling).

THEOREM ATTEMPT: Among 28 distinct primes q_k > 29, at least one must be:
- A non-QR mod 3 (≡ 2 mod 3), OR
- A non-QR mod 7, OR
- A non-QR mod 11

This would prove escape for large t. CAN YOU PROVE THIS?

By Chebotarev, primes equidistribute in residue classes.
- Primes ≡ 2 (mod 3): density 1/2
- Non-QRs mod 7: density 1/2
- Non-QRs mod 11: density 1/2

If these were independent, P(q is QR mod 3 AND QR mod 7 AND QR mod 11) = 1/8.
So P(all 28 primes avoid non-QR classes) ≈ (1/8)^{28} ≈ 10^{-25}.

But they're NOT independent. What's the actual probability?

PROVE OR DISPROVE: There exists N such that for all t > N, at least one of t, t+1, ..., t+29 has a prime factor that escapes all three traps.
```

---

## PROMPT 5: The Algebraic Bypass (Alternative Approach)

**Estimated time: 20-30 minutes**

```
If the modular covering approach cannot be completed, what ALTERNATIVE approaches exist?

The Erdős-Straus conjecture states: For all n ≥ 2, 4/n = 1/x + 1/y + 1/z has a solution in positive integers.

APPROACH 1: Mordell Curves
The equation can be related to y² = x³ - n (Mordell curve).
- For n ≡ 1 (mod 840), these are the "hard" cases.
- Is there a theorem about Mordell curves that implies ESC for these n?

APPROACH 2: Parametric Families
Are there parametric solutions that cover specific residue classes?
Example: If n ≡ a (mod m), then (x,y,z) = (f(n), g(n), h(n)) works.

Can we find enough parametric families to cover all n?

APPROACH 3: Descent
Suppose ESC fails for some n₀. Can we derive a contradiction via descent?
- If no solution exists, what does this imply about related Diophantine equations?

APPROACH 4: Local-Global
ESC is known to have solutions over Q (rational solutions always exist).
The question is integrality.
- Can we use local-global principles?
- Is there a "Hasse principle failure" obstruction that can be ruled out?

APPROACH 5: Computational Completeness
- ESC is verified for all n up to 10^17.
- Is there any approach that converts large computational verification into a proof?
- Example: Prove that if ESC holds for n ≤ N, it holds for all n. (Is this possible?)

For each approach, assess: How close is this to a complete proof? What's the key obstacle?
```

---

## PROMPT 6: The Product Group Structure (Detailed Calculation)

**Estimated time: 25-35 minutes**

```
Let me set up the group theory precisely for the Erdős-Straus obstruction.

For K = {0, 1, 2, 5, 7, 9, 11, 14, 17, 19, 23, 26, 29}, the moduli are:
m_0 = 3, m_1 = 7, m_2 = 11, m_5 = 23, m_7 = 31, m_9 = 39 = 3×13,
m_11 = 47, m_14 = 59, m_17 = 71, m_19 = 79, m_23 = 95 = 5×19,
m_26 = 107, m_29 = 119 = 7×17

TASK 1: For each m_k, compute (Z/m_k)*/QR(m_k).
This quotient has order 2^(number of odd prime factors of m_k).

For m_0 = 3: Z/2
For m_1 = 7: Z/2
For m_2 = 11: Z/2
For m_9 = 39 = 3×13: Z/2 × Z/2
...

TASK 2: Define the "obstruction group" G_K = ∏_{k∈K} (Z/m_k)*/QR(m_k).

What is the structure of G_K for K13?
What is |G_K|?

TASK 3: For a prime q, define its "signature" σ(q) ∈ G_K by:
σ(q)_k = 0 if q is QR mod m_k, 1 if q is non-QR mod m_k

ESCAPE CONDITION: x_k escapes the trap iff the sum (in G_K) of signatures of its prime factors is nonzero in the k-th component.

TASK 4: THEOREM ATTEMPT
If x has prime factors q_1, ..., q_r, then x escapes some trap iff
σ(q_1) + ... + σ(q_r) ≠ 0 in G_K.

This is a zero-sum problem! If r > D(G_K), escape is guaranteed.

COMPUTE D(G_K) for K13.

TASK 5: For the specific K13, can we show that "typical" integers t+k have enough distinct prime factors that escape is guaranteed?

Hint: The number of distinct prime factors of n is ω(n) ≈ log log n for typical n.
For n ≈ 10^7, ω(n) ≈ 3.
For n ≈ 10^{17}, ω(n) ≈ 4.

Is D(G_K) ≤ 4 achievable for some K?
```

---

## PROMPT 7: Explicit Construction of "Escape-Forcing" K (Computational/Constructive)

**Estimated time: 30-40 minutes**

```
GOAL: Find an explicit finite set K such that escape is GUARANTEED for all primes p above some threshold.

We know K13 has 14 failures up to 50M.
K13 + {31, 39, 41} covers these 14.

QUESTION: How do we PROVE that some finite K covers ALL primes?

APPROACH: Incremental Covering

Step 1: Start with K = {0, 1, 2}.
- Failure set F_K = primes where all factors of x_k are in QR(m_k) for all k ∈ K
- Characterize F_K: these are primes where:
  * All factors of t ≡ 1 (mod 3)
  * All factors of t+1 are QRs mod 7
  * All factors of t+2 are QRs mod 11

Step 2: For each k ∉ K, compute how many primes in F_K are rescued by adding k.
- k=31 (m=127) rescues 12/14 of K13 failures
- k=41 (m=167) rescues 11/14 of K13 failures

Step 3: THEOREM NEEDED
For each remaining "super-failure" (failure for K + {31, 39, 41}), find a k that rescues it.
Continue until... what?

KEY QUESTION:
- Does this process terminate?
- Is there a proof that it must terminate?
- What's the structure that guarantees termination?

SPECIFIC CALCULATION:
Take p = 10170169 (first K13 failure).
t = (p+3)/4 = 2542543 = 829 × 3067

For k=0: x_0 = 2542543 = 829 × 3067
  829 ≡ 1 (mod 3), 3067 ≡ 1 (mod 3) → TRAPPED

For k=31: x_31 = 2542574 = 2 × 1271287
  Compute: Is 1271287 a non-QR mod 127?
  1271287 mod 127 = ?

Continue this analysis. Find the SMALLEST k that rescues p = 10170169.

Then: Is there a pattern? Can we prove every failure is eventually rescued?
```

---

## PROMPT 8: Sieve Methods and the Large Sieve (Technical)

**Estimated time: 35-45 minutes**

```
Can sieve methods prove that the "trapped" set is finite?

SETUP: Let A = {t : 4t-3 is prime and for all k ∈ K, all prime factors of t+k are QRs mod m_k}

QUESTION: Is |A| < ∞?

APPROACH 1: Selberg Sieve
For each k, let S_k = {n : all prime factors of n are QRs mod m_k}

S_k has density ∏_{q prime, q non-QR mod m_k} (1 - 1/q) by inclusion-exclusion.

For m_k prime, non-QRs have density 1/2 among primes, so:
density(S_k) = ∏_{q ≡ non-QR mod m_k} (1 - 1/q)

This product is ZERO (diverges to 0) because:
∑_{q non-QR} 1/q = (1/2) ∑_q 1/q = ∞

So S_k has density 0 in integers. But does S_0 ∩ S_1 ∩ ... have density 0 in PRIMES?

APPROACH 2: Large Sieve
The large sieve inequality bounds:
∑_{n ≤ N, n∈A} 1 ≤ N/L(A)

where L(A) depends on the "sieve dimension" of A.

For our A, what is the sieve dimension?
Can we show L(A) → ∞, implying |A ∩ [1,N]| = o(N)?

APPROACH 3: Bombieri-Vinogradov
This gives equidistribution of primes in arithmetic progressions on average.

For t+k, the constraint "all prime factors are QRs mod m_k" is equivalent to:
t+k ∈ ⟨QRs mod m_k⟩ (multiplicative subgroup generated by QRs)

This is NOT an arithmetic progression. But can we still use BV-type ideas?

APPROACH 4: Character Sums
Define χ_k = quadratic character mod m_k.
The condition "all factors of n are QRs" is: χ_k(n) = 1 AND n has no factors where χ_k = -1.

Can we write this as a Dirichlet series / L-function condition?

∑_{n, all factors QR} n^{-s} = ∏_{q QR mod m_k} (1-q^{-s})^{-1}

This is a partial Euler product. Can we analyze it?

PROVE OR DISPROVE: |A| < ∞ for K = K13 (or some explicit K).
```

---

## Instructions for Running These Prompts

1. **Run prompts 1, 2, 3, 4 in parallel** on different GPT instances - these are the most likely to yield the breakthrough.

2. **Prompt 6** is computational/structural - good for GPT-4 which is reliable.

3. **Prompt 5** is the "escape hatch" - alternative approaches if modular covering fails.

4. **Prompts 7 and 8** are technical deep-dives.

5. **Key phrases to look for in responses**:
   - "This proves..." (actual theorem)
   - "The Davenport constant is..." (specific number)
   - "The density is zero/finite" (finiteness result)
   - "These conditions are mutually exclusive when..." (incompatibility)

6. **If GPT finds something promising**, follow up with: "Can you write this as a formal theorem with complete proof?"

Good luck! One of these angles should yield the major new ingredient.
