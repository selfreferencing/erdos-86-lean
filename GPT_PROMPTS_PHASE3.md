# GPT 5.2 Phase 3 Prompts

Two targeted prompts to run in parallel before implementation.

---

## PROMPT 29: Extended Witnesses - Can K13 Alone Suffice?

**For: GPT 5.2 Pro Extended (45-60 min)**

```
ERDŐS-STRAUS: EXTENDED WITNESS ANALYSIS

CONTEXT:
We've established that coverage is NOT a residue-class property when using only prime witnesses.
However, using COMPOSITE witnesses d = a · q^e might change this.

THE 14 K13 FAILURES (primes that fail all k ∈ K13):
10170169, 11183041, 22605361, 24966481, 30573481, 30619801,
34103161, 35241529, 36851929, 36869281, 37228801, 45575401,
46936849, 48991849

K13 = {0, 1, 2, 5, 7, 9, 11, 14, 17, 19, 23, 26, 29}

WITNESS CONDITION:
For k, a Type II witness is d | x_k² with d ≡ -x_k (mod m_k)
where m_k = 4k+3 and x_k = (p + m_k)/4

EXTENDED WITNESS TEMPLATES:
- Type A: d = q (prime)
- Type B: d = q² (square of prime)
- Type C: d = a·q where a ∈ {2, 3, 4, 6} and gcd(a, m_k) = 1
- Type D: d = a·q² where a ∈ {2, 3, 4, 6} and gcd(a, m_k) = 1

YOUR TASKS:

1. FOR EACH OF THE 14 FAILURES:
   Compute x_k for each k ∈ K13 and find ANY witness d | x_k² with d ≡ -x_k (mod m_k).

   For each failure p, report:
   - The k ∈ K13 that works (if any)
   - The witness d
   - Express d in form a·q^e

2. CRITICAL QUESTION:
   Can ALL 14 failures be certified using ONLY k ∈ K13 with extended witnesses?
   Or do some REQUIRE k ∉ K13?

3. IF K13 IS INSUFFICIENT:
   For failures that cannot be certified by K13:
   - Find the smallest k ∉ K13 that certifies them
   - Report the witness d for that k

4. THE SPECIAL CASE p = 66,032,521:
   This prime is fully trapped at ALL k ∈ K13 (all prime factors of each x_k are QRs).
   - Verify k = 3 rescues it with witness d = 116 = 2² · 29
   - Find any other small k ∉ K13 that works

5. COVERAGE ASSESSMENT:
   Based on your analysis:
   - What is the minimal K_rescue = {k ∉ K13} needed to cover all known failures?
   - Is K13 ∪ K_rescue likely to achieve complete coverage?

PROVIDE:
1. Table: For each of 14 failures, the certifying (k, d) pair
2. Answer: Does K13 alone suffice with extended witnesses?
3. If not: The minimal K_rescue set
4. Verification that k=3 rescues p=66,032,521
```

---

## PROMPT 30: K13 ∪ {3} Coverage Analysis

**For: GPT 5.2 Thinking Heavy (30-45 min)**

```
ERDŐS-STRAUS: COVERAGE ANALYSIS FOR K14 = K13 ∪ {3}

BACKGROUND:
K13 = {0, 1, 2, 5, 7, 9, 11, 14, 17, 19, 23, 26, 29}
leaves 419,904 uncovered residue classes mod M'' = 70,148,764,800.

We discovered that k = 3 (m = 15) is NOT in K13, yet it rescues:
- p = 66,032,521 (the ONLY prime < 10^8 fully trapped at all K13)
- Witness: d = 116 = 2² · 29

QUESTION: What does adding k = 3 do to coverage?

YOUR TASKS:

1. ANALYZE k = 3 (m = 15 = 3 × 5):
   - What residue classes mod 15 can be hit by witness d | x_3²?
   - The QR subgroup of (Z/15Z)* has what structure?
   - For which p does k = 3 provide a witness?

2. CRT ANALYSIS:
   When k = 3 certifies p via witness d = q (prime):
   - Condition 1: q | x_3 ⟺ p ≡ -15 (mod 4q)
   - Condition 2: q ≡ -x_3 (mod 15) ⟺ p ≡ -4q (mod 15)

   For small primes q ∈ {2, 7, 11, 13, 17, 19, 23, 29}:
   - Compute the CRT condition on p
   - Which of these cover NEW classes not covered by K13?

3. COVERAGE IMPROVEMENT:
   Let K14 = K13 ∪ {3}.
   - Estimate how many of the 419,904 uncovered classes are now covered
   - What fraction remains uncovered?

4. THE 14 K13 FAILURES:
   For each of the 14 failures:
   10170169, 11183041, 22605361, 24966481, 30573481, 30619801,
   34103161, 35241529, 36851929, 36869281, 37228801, 45575401,
   46936849, 48991849

   Check: Does k = 3 provide a witness for any of them?
   (Compute x_3 = (p + 15)/4 for each, find if any d | x_3² has d ≡ -x_3 mod 15)

5. WHY WAS k = 3 EXCLUDED FROM K13?
   - m_3 = 15 = 3 × 5 is composite
   - The original K13 was optimized for prime m_k or m_k with large prime factors
   - But k = 3 might cover classes that K13 misses due to its composite structure

6. OPTIMAL EXTENSION:
   If K14 = K13 ∪ {3} is still insufficient:
   - What additional k values should be added?
   - Is there a pattern (composite m_k vs prime m_k)?

PROVIDE:
1. Structure of (Z/15Z)* and its QR subgroup
2. CRT conditions for k = 3 with small prime witnesses
3. Estimate of coverage improvement from K13 to K14
4. Which (if any) of the 14 failures are rescued by k = 3
5. Assessment: Is K14 sufficient, or what else is needed?
```

---

## Usage Notes

**Run these in parallel:**
- Prompt 29 → GPT 5.2 Pro Extended (comprehensive computation)
- Prompt 30 → GPT 5.2 Thinking Heavy (structural analysis)

**Key questions these will answer:**
1. Can K13 alone suffice with extended witnesses?
2. What does adding k = 3 accomplish?
3. What is the minimal K_rescue set?

**After these complete:**
- We'll know the exact K_final needed
- Implementation can target the correct K set

---

## UPDATE: K_COMPLETE DISCOVERED (January 21, 2025)

**Prompts 29 and 30 are now superseded by the following finding:**

We computationally discovered **K_COMPLETE** with 23 k values that covers ALL 2,880,504 primes ≡ 1 (mod 4) up to 10^8:

```
K_COMPLETE = [0, 1, 2, 3, 4, 5, 6, 7, 9, 11, 13, 14, 16, 17, 19, 21, 23, 25, 26, 29, 31, 39, 41]
```

The theoretical gap is now: **Prove K_COMPLETE works for ALL primes, not just those up to 10^8.**

---

## PROMPT 31: Proving K_COMPLETE Sufficiency

**For: GPT 5.2 Pro Extended (60+ min)**

```
ERDŐS-STRAUS: PROVING K_COMPLETE COVERS ALL PRIMES

BREAKTHROUGH:
We have computationally verified that K_COMPLETE covers ALL 2,880,504 primes
p ≡ 1 (mod 4) with p < 10^8.

K_COMPLETE = [0, 1, 2, 3, 4, 5, 6, 7, 9, 11, 13, 14, 16, 17, 19, 21, 23, 25, 26, 29, 31, 39, 41]
|K_COMPLETE| = 23

The corresponding m_k = 4k+3 values are:
3, 7, 11, 15, 19, 23, 27, 31, 39, 47, 55, 59, 67, 71, 79, 87, 95, 103, 107, 119, 127, 159, 167

THE THEORETICAL GAP:
We need to prove K_COMPLETE covers ALL primes p ≡ 1 (mod 4), not just those < 10^8.

FACTS WE HAVE:

1. ESCAPE LEMMA (PROVED):
   For every prime p ≡ 1 (mod 4), there exists SOME k with a Type II witness.
   Proof: Via quadratic reciprocity and Dirichlet's theorem.

2. EMPIRICAL COVERAGE:
   - K13 (13 values) fails on exactly 14 primes < 10^8
   - K13 ∪ K_RESCUE (17 values) fails on 0 primes < 10^8
   - K_COMPLETE (23 values) fails on 0 primes < 10^8

3. STRUCTURE OF K_COMPLETE:
   - K13 = [0,1,2,5,7,9,11,14,17,19,23,26,29] (original base)
   - K_RESCUE = [3,31,39,41] (rescues K13 failures)
   - K_ADDITIONAL = [4,6,13,16,21,25] (covers remaining mod-840 classes)

YOUR TASKS:

1. COVERAGE ANALYSIS MOD M:
   Let M = lcm(m_k : k ∈ K_COMPLETE).

   a) Compute M (or its factorization)
   b) For each admissible residue class r mod M (r ≡ 1 mod 4, gcd(r,M) = 1):
      - Can you prove there exists k ∈ K_COMPLETE and witness d such that
        all p ≡ r (mod M) are covered by (k, d)?

   This would give a CERTIFICATE approach: enumerate mod-M rules.

2. GROUP-THEORETIC APPROACH:
   For each k, let G_k = (Z/m_k Z)* and H_k = QR subgroup.

   The "trapping" condition at k is: all prime factors of x_k lie in H_k.

   Question: Can you prove that for any prime p ≡ 1 (mod 4), at least one
   k ∈ K_COMPLETE has some prime factor q | x_k with q ∉ H_k?

   This would establish "escape" exists within K_COMPLETE.

3. CHARACTER ORTHOGONALITY:
   Each k defines a quadratic character χ_k : (Z/m_k Z)* → {±1}.

   For p to be trapped at ALL k ∈ K_COMPLETE, we need:
   - For each k, all prime factors of x_k are in ker(χ_k)

   This seems highly over-constrained. Can you:
   a) Formalize this constraint using character sums?
   b) Show that for large p, the constraint is impossible to satisfy?

4. DENSITY/SIEVE ARGUMENT:
   The Escape Lemma shows trapped primes have density 0.

   Can you strengthen this to: "If K has enough k values with coprime m_k,
   then trapped primes are FINITE"?

   Specifically: What conditions on K guarantee finitely many failures?

5. DIRECT PROOF ATTEMPT:
   For any prime p ≡ 1 (mod 4) with p > 10^8:

   Step 1: p falls in some residue class r mod 840
   Step 2: Our greedy analysis shows K_COMPLETE covers all 96 admissible classes mod 840
   Step 3: Therefore... (complete the argument)

   The gap: Covering class r mod 840 by testing small primes doesn't guarantee
   covering ALL primes in class r. How do we bridge this?

6. POSSIBLE APPROACHES:
   a) Show witness existence is a "residue class property" for large enough modulus
   b) Prove a uniform bound on witness size d (so finite search works)
   c) Use Baker-type bounds on linear forms in logarithms
   d) Apply sieve methods to bound exceptions

PROVIDE:
1. Your best approach to proving K_COMPLETE suffices for ALL primes
2. Any conditions/bounds that would complete the proof
3. If gap remains: what additional computation or theory is needed
4. Assessment: Is full proof achievable, or is there a fundamental obstacle?
```

---

## PROMPT 32: Certificate Construction for K_COMPLETE

**For: GPT 5.2 Thinking Heavy (45 min)**

```
ERDŐS-STRAUS: CERTIFICATE FOR K_COMPLETE

GOAL: Construct a finite certificate proving K_COMPLETE covers ALL primes p ≡ 1 (mod 4).

K_COMPLETE = [0, 1, 2, 3, 4, 5, 6, 7, 9, 11, 13, 14, 16, 17, 19, 21, 23, 25, 26, 29, 31, 39, 41]

CERTIFICATE STRUCTURE:
For each admissible residue class r mod M (some modulus M):
- Provide a "recipe" (k, witness_type, parameters) that certifies all p ≡ r (mod M)

WITNESS TYPES:
1. Prime witness: d = q (prime) where q | x_k and q ≡ -x_k (mod m_k)
2. Square witness: d = q² where q² | x_k² and q² ≡ -x_k (mod m_k)
3. Product witness: d = a·q^e where d | x_k² and d ≡ -x_k (mod m_k)

YOUR TASKS:

1. CHOOSE MODULUS M:
   The certificate modulus M should satisfy:
   - M is divisible by lcm of small m_k values
   - |{r mod M : r ≡ 1 (mod 4), gcd(r,M) = 1}| is manageable

   Candidates:
   - M = 840 = lcm(3,5,7,8) → 96 admissible classes
   - M = 27720 = lcm(3,5,7,8,9,11) → ~2500 classes
   - M = 360360 = lcm(3,5,7,8,9,11,13) → ~17000 classes

   What is the right M for a complete certificate?

2. FOR M = 840:
   We found that K_COMPLETE covers all 96 admissible classes.

   For each class r, give:
   - The k ∈ K_COMPLETE that covers it
   - The witness type (prime/square/product)
   - For prime witness: which small prime q works?

   Format: Table with 96 rows.

3. VERIFY COMPLETENESS:
   For the certificate to prove ESC:
   - Must cover ALL admissible classes mod M
   - Must show witness recipe works for ALL p in each class (not just small p)

   The second point is the hard part. How do we ensure the recipe works universally?

4. UNIVERSAL WITNESS ARGUMENT:
   For a class r mod M certified by (k, "prime", q):

   The recipe says: "For all p ≡ r (mod M), q | x_k and q ≡ -x_k (mod m_k)"

   This follows from:
   - q | x_k ⟺ p ≡ -m_k (mod 4q)
   - q ≡ -x_k (mod m_k) ⟺ p ≡ -4q (mod m_k)

   Combined: p ≡ some fixed residue (mod lcm(M, 4q, m_k))

   If r mod M is compatible with this, the recipe works for ALL p ≡ r (mod M).

   Verify this logic is sound.

5. EXCEPTION HANDLING:
   Some classes mod 840 might not have a "uniform" recipe.

   Instead: "For all p ≡ r (mod 840) with p > B, use recipe R"
   And: "For small exceptions p ≤ B, verify individually"

   What is a reasonable B? Can you bound the exceptions?

6. FINAL CERTIFICATE:
   Produce a certificate in this format:

   ```
   MODULUS: M = 840

   CLASS r = 1:
     Recipe: k = X, witness q = Y
     CRT condition: p ≡ Z (mod ...)
     Valid for all p ≡ 1 (mod 840)

   CLASS r = 17:
     Recipe: k = X, witness q = Y
     ...

   [96 entries total]

   EXCEPTIONS (p ≤ B):
   [List any that need individual verification]
   ```

PROVIDE:
1. Choice of M with justification
2. Complete table of 96 recipes (for M = 840)
3. Proof that recipes work universally (not just for small p)
4. List of any exceptions
5. Assessment: Is this a valid proof certificate?
```

---

## Current Status

- **Prompts 29-30**: Superseded by K_COMPLETE discovery
- **Prompt 31**: Theoretical proof that K_COMPLETE works for ALL primes
- **Prompt 32**: Certificate construction approach

**Priority**: Run Prompt 31 first for theoretical breakthrough, then Prompt 32 for certificate.
