# GPT Overnight Fleet: ESC Proof Prompts

Run 12-15 instances on these prompts. Mix of approaches to maximize discovery.

---

## PROMPT 1: The 6|n Theorem (Main Target) [Run 3 instances]

**Problem**: Prove or find counterexample to:

> If n ≡ 0 (mod 6) and n ≥ 300, then G(n, 23) ≥ 1.

Where G(n, m) = number of unordered pairs (a, b) of coprime divisors of n with a + b ≡ 0 (mod m).

**Context**: This completes the Erdős-Straus Conjecture proof. We've verified computationally that for all primes p ≡ 1 (mod 4) up to 10^7, some k ∈ {0,1,2,3,4,5} gives G(n_k, 4k+3) ≥ 1. The hardest cases (p = 1201, 2521) require k = 5, where n_5 ≡ 0 (mod 6).

**Key observations**:
- If 6 | n, then n = 2^a · 3^b · m where gcd(m, 6) = 1
- Divisors of n include 1, 2, 3, 6, and products with m's factors
- Coprime pairs include (2, 3d) for any d | m with gcd(d, 2) = 1
- We need 2 + 3d ≡ 0 (mod 23), i.e., d ≡ 7 (mod 23)

**Question**: Can you prove that for n ≥ 300 with 6 | n, either:
(a) n has a divisor d ≡ 7 (mod 23) coprime to 2, giving pair (2, 3d), OR
(b) Some other coprime pair (a, b) with a + b ≡ 0 (mod 23) exists?

---

## PROMPT 2: Covering System Approach [Run 2 instances]

**Problem**: Show that the "bad" residue classes for k = 0, 1, 2, 3, 4, 5 cannot all be satisfied simultaneously.

**Setup**: For prime p ≡ 1 (mod 4), define n_k = (p + 4k + 3)/4 and m_k = 4k + 3.

G(n_k, m_k) = 0 imposes constraints on p. We know:
- k=0: G(n_0, 3) = 0 requires n_0 to have special structure (prime or bad semiprime)
- k=1: G(n_1, 7) = 0 requires n_1 ∈ Family A ∪ Family B (restricted prime factors)
- Similar for k=2,3,4,5

**Known safe classes**:
- k=0: p ≡ 5 (mod 12) ⟹ G(n_0, 3) ≥ 1 always
- k=1: p ≡ 17 (mod 28) ⟹ G(n_1, 7) ≥ 1 always
- k=2: p ≡ 29 (mod 44) ⟹ G(n_2, 11) ≥ 1 always
- k=3: p ≡ 41 (mod 60) ⟹ G(n_3, 15) ≥ 1 always
- k=4: p ≡ 53 (mod 76) ⟹ G(n_4, 19) ≥ 1 always
- k=5: p ≡ 65 (mod 92) ⟹ G(n_5, 23) ≥ 1 always

**Question**: Can you prove that for any p ≡ 1 (mod 4), at least one of these safe conditions holds, OR that the intersection of all dangerous classes is empty?

---

## PROMPT 3: Linear Relation Constraints [Run 2 instances]

**Problem**: Use the linear relation 2n_k = m + (2k+1) to derive constraints.

**Setup**: Let m = (p+1)/2 and n_k = (p + 4k + 3)/4.

Then 2n_k = m + (2k + 1), so gcd(m, n_k) | gcd(m, 2k+1).

**Key constraint**: If m has all prime factors ≡ 1 (mod 4) (Condition A fails), then:
- 3 ∤ m, 7 ∤ m, 11 ∤ m, ... (all primes ≡ 3 mod 4)
- So gcd(m, n_1) = gcd(m, 3) = 1
- And gcd(m, n_5) = gcd(m, 11) = 1

This means n_k is **coprime to m** for k = 1, 3, 5 when A fails.

**Additionally**: n_0 ≡ 1 (mod 3) when p ≡ 1 (mod 12), so:
- n_2 ≡ 0 (mod 3)
- n_5 ≡ 0 (mod 3)

**Question**: Can you prove that the combination of:
- n_5 coprime to m
- 3 | n_5
- n_5 even (when A fails, m ≡ 1 mod 4)

forces G(n_5, 23) ≥ 1?

---

## PROMPT 4: Divisor Count Argument [Run 2 instances]

**Problem**: Use divisor counting to show G(n, 23) ≥ 1 for "rich" n.

**Key fact**: G(n, m) = 0 requires ALL coprime pairs (a, b) of n to miss 0 (mod m).

If n = p_1^{e_1} · ... · p_k^{e_k}, the number of coprime pairs is related to 2^{k-1}.

**For n with 6 | n**:
- n = 2^a · 3^b · r where gcd(r, 6) = 1
- Number of divisors: τ(n) = (a+1)(b+1)τ(r)
- Coprime pairs include pairs from {powers of 2} × {3^j · d : d | r, gcd(d,2)=1}

**Probabilistic heuristic**: Each coprime pair independently hits 0 (mod 23) with probability ~1/23. With C coprime pairs, probability all miss is ~(22/23)^C.

For n = 306 = 2·3²·17: C = 22 coprime pairs, P(all miss) ≈ (22/23)^22 ≈ 0.38
For n = 636 = 2²·3·53: C = 22 coprime pairs, P(all miss) ≈ 0.38

But actually G(n, 23) ≥ 1 in both cases!

**Question**: Can you prove that for n ≥ 300 with 6 | n, the number of coprime pairs is large enough to guarantee at least one hits 0 (mod 23)?

---

## PROMPT 5: Direct k=5 Analysis [Run 2 instances]

**Problem**: Prove G(n, 23) ≥ 1 when n = (m + 11)/2, m odd, all prime factors of m are ≡ 1 (mod 4).

**Setup**: This is exactly the k=5 case when Condition A fails.

From 2n = m + 11:
- gcd(m, n) | gcd(m, 11) = 1 (since 11 ≡ 3 mod 4 and m has only 1 mod 4 factors)
- So n is **coprime to m**

From m ≡ 1 (mod 3) (since 3 ∤ m):
- 2n = m + 11 ≡ 1 + 2 ≡ 0 (mod 3)
- So **3 | n**

From m ≡ 1 (mod 4):
- 2n = m + 11 ≡ 1 + 3 ≡ 0 (mod 4)
- So **2 | n**

Therefore **6 | n** and **gcd(m, n) = 1**.

**Question**: Prove that under these constraints, G(n, 23) ≥ 1.

---

## PROMPT 6: Consecutive Integer Formulation [Run 2 instances]

**Problem**: Prove that among 6 consecutive integers n, n+1, ..., n+5, at least one satisfies G(n+k, 4k+3) ≥ 1.

**Setup**: For n ≡ 1 (mod 3):
- n ≡ 1 (mod 3)
- n+1 ≡ 2 (mod 3)
- n+2 ≡ 0 (mod 3)
- n+3 ≡ 1 (mod 3)
- n+4 ≡ 2 (mod 3)
- n+5 ≡ 0 (mod 3)

So n+2 and n+5 are divisible by 3.

**Verified**: For all n arising from primes p ≡ 1 (mod 4) up to 10^7, at least one k ∈ {0,1,2,3,4,5} works.

**The hardest cases**: n = 301 (p = 1201) and n = 631 (p = 2521) both require k = 5.

**Question**: Prove that for n ≡ 1 (mod 3) with n ≥ 300, at least one of the 6 conditions holds.

---

## PROMPT 7: Family A/B Classification Extension [Run 2 instances]

**Problem**: Extend the k=1 Family A/B classification to k=2, 3, 4, 5.

**For k=1** (m=7), G(n, 7) = 0 iff n ∈ Family A ∪ Family B where:
- Family A: all prime factors ≡ 1, 2, 4 (mod 7)
- Family B: all prime factors ≡ 1, 3, 5 (mod 7), with Ω_{3,5} ≤ 2

**Question**:
1. Derive similar classifications for G(n, 11) = 0, G(n, 15) = 0, G(n, 19) = 0, G(n, 23) = 0.
2. Show that for consecutive integers n, n+1, ..., n+5, the constraints cannot all be satisfied simultaneously when n ≡ 1 (mod 3).

---

## PROMPT 8: Sieve Theory Approach [Run 1-2 instances]

**Problem**: Use sieve methods to bound the density of "bad" n.

**Setup**: An integer n is "k-bad" if G(n, 4k+3) = 0. Define:
- B_k = {n : G(n, 4k+3) = 0}

**Question**:
1. What is the density of B_k among integers?
2. What is the density of B_0 ∩ B_1 ∩ B_2 ∩ B_3 ∩ B_4 ∩ B_5?
3. Can you show this intersection has density 0, or is finite, or empty for n ≥ N?

---

## Summary: Recommended Fleet Distribution

| Prompt | Instances | Focus |
|--------|-----------|-------|
| 1 (6|n theorem) | 3 | Main target |
| 2 (Covering) | 2 | Combinatorial |
| 3 (Linear relations) | 2 | Algebraic |
| 4 (Divisor count) | 2 | Probabilistic |
| 5 (Direct k=5) | 2 | Focused proof |
| 6 (Consecutive) | 2 | Alternative formulation |
| 7 (Family extension) | 1-2 | Classification |
| 8 (Sieve) | 1 | Density |

**Total: 15-17 instances**

Good luck! 🌙
