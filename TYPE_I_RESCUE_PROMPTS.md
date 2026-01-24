# Type I Rescue Prompts

Run these on GPT Pro Extended during commute. The overnight fleet established that Type II can fail at all k=0,...,5, but Type I rescues. We need to prove WHY.

---

## PROMPT A: Direct Type I Analysis [Run 3 instances]

**Context**: For the Erdős-Straus Conjecture, we have two methods for prime p ≡ 1 (mod 4):

- **Type I at k**: kp + 1 has a divisor d ≡ -p (mod 4k)
- **Type II at k**: G(n_k, m_k) ≥ 1 where n_k = (p + 4k + 3)/4, m_k = 4k + 3

**Verified computationally**: There are exactly 57 primes p < 800,000 where Type II fails at ALL k = 0,1,2,3,4,5. The first few are:
> 21169, 61681, 66529, 67369, 87481, 94441, 99961, 112249, ...

For ALL of these, Type I succeeds at some k (usually k=5).

**The theorem to prove**:
> If Type II fails at all k = 0,1,2,3,4,5, then Type I succeeds at some k ≤ 5.

**Key observation**: Type II fails at k iff n_k is "QR-trapped" (all prime factors are quadratic residues mod m_k). This imposes constraints on p.

**Questions**:
1. For p = 21169, verify Type I succeeds at k=5. What divisor d of 5p+1 satisfies d ≡ -p (mod 20)?
2. What do the "QR-trapped at all k" conditions imply about p mod various moduli?
3. Can you prove that these conditions force Type I to succeed?

---

## PROMPT B: The QR-Trapping Implies Type I Success [Run 2 instances]

**Setup**: Let p ≡ 1 (mod 4) be prime. Define:
- n_k = (p + 4k + 3)/4 for k = 0,1,2,3,4,5
- m_k = 4k + 3

**Known**: G(n_k, m_k) = 0 iff all prime factors of n_k lie in the QR subgroup mod m_k:
- m=3: factors ≡ 1 (mod 3)
- m=7: factors ≡ 1, 2, 4 (mod 7)
- m=11: factors ≡ 1, 3, 4, 5, 9 (mod 11)
- m=15: factors ≡ 1, 2, 4, 8 (mod 15)
- m=19: factors ≡ 1, 4, 5, 6, 7, 9, 11, 16, 17 (mod 19)
- m=23: factors ≡ 1, 2, 3, 4, 6, 8, 9, 12, 13, 16, 18 (mod 23)

**The situation**: When ALL six n_k are QR-trapped simultaneously, what constraints does this place on p?

**Type I condition at k**: kp + 1 has a divisor d with d ≡ -p (mod 4k).

**Question**: Prove that the constraints from "all n_k are QR-trapped" force kp + 1 to have such a divisor for some k ≤ 5.

**Hint**: The QR-trapping conditions may force p to lie in specific residue classes mod lcm(3,7,11,15,19,23) = 504735. These residue classes may automatically make Type I succeed.

---

## PROMPT C: Analyze the 57 Primes [Run 2 instances]

**Data**: The following primes p ≡ 1 (mod 4) have Type II fail at ALL k = 0,1,2,3,4,5:

21169, 61681, 66529, 67369, 87481, 94441, 99961, 112249

For each, Type I succeeds (usually at k=5).

**Tasks**:
1. For each prime, compute:
   - p mod 504735 (the lcm of 3,7,11,15,19,23 × 4)
   - Which k has Type I succeed
   - The divisor d of kp+1 that satisfies d ≡ -p (mod 4k)

2. Find the pattern: What residue class(es) mod some M do all these primes share?

3. Prove: For primes in this residue class, Type I must succeed at some k.

---

## PROMPT D: Combined Covering Argument [Run 2 instances]

**Goal**: Prove that for every prime p ≡ 1 (mod 4), either Type I or Type II succeeds at some k.

**Known from overnight fleet**:
- Type II alone fails for infinitely many primes (density 0)
- The failures are exactly when each n_k is QR-trapped
- Type I rescues all known failures

**Approach**:

Define "p is dangerous" if Type II fails at all k = 0,...,5. We know:
- Dangerous ⟹ n_0 has all factors ≡ 1 (mod 3)
- Dangerous ⟹ n_1 has all factors in {1,2,4} (mod 7)
- ... (similar for k=2,3,4,5)

These six conditions on n_0, n_0+1, ..., n_0+5 impose constraints on p.

**Questions**:
1. Use CRT to find what residue classes mod L = lcm(3,7,11,15,19,23) are "dangerous"
2. For each dangerous residue class, check if Type I succeeds at some k
3. Prove the covering: dangerous classes are covered by Type I success

---

## PROMPT E: Why k=5 Type I Works [Run 2 instances]

**Observation**: For most of the 57 "all Type II fail" primes, Type I succeeds at k=5.

**Type I at k=5**: 5p + 1 must have a divisor d ≡ -p (mod 20).

**Question**: Why does the condition "n_5 = (p+23)/4 is QR-trapped mod 23" help Type I at k=5 succeed?

**Possible connection**:
- QR-trapped mod 23 means n_5 = (p+23)/4 has all prime factors in {1,2,3,4,6,8,9,12,13,16,18} mod 23
- This constrains p mod 23
- Does this constraint on p mod 23 force 5p+1 to have a nice factorization?

**Analyze**:
1. For p = 21169: Compute 5p + 1 = 105846. Factor it. Find d with d ≡ -21169 ≡ 11 (mod 20).
2. For p = 61681: Same analysis.
3. Find the pattern.

---

## PROMPT F: The Nuclear Option - Extend to k ≤ 10 [Run 1 instance]

**Question**: Is the "max k = 5" claim even true?

**From overnight**: p = 66529 needs k = 7 for Type II. Are there primes needing k ≥ 6 for BOTH Type I and Type II?

**Computational request**:
1. For p = 66529, check if Type I works at any k ≤ 5
2. Find the smallest k where either Type I or Type II works
3. Is there any prime p where BOTH methods need k ≥ 6?

If max k grows slowly, the proof might need to handle arbitrarily large k, which requires different techniques.

---

## Summary: Recommended Distribution

| Prompt | Instances | Focus |
|--------|-----------|-------|
| A (Direct Type I) | 3 | Main target |
| B (QR-Trapping implies Type I) | 2 | Structural |
| C (Analyze 57 primes) | 2 | Computational |
| D (Combined covering) | 2 | Proof strategy |
| E (Why k=5 works) | 2 | Specific mechanism |
| F (Extend to k≤10) | 1 | Boundary check |

**Total: 12 instances**

Safe drive! 🚗
