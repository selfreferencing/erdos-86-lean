# GPT Prompt 11: Prove the Covering Theorem for Erdos-Straus

## Context

I am formalizing the Erdos-Straus conjecture (4/n = 1/x + 1/y + 1/z) in Lean 4. ONE sorry remains. It reduces to the following:

**Theorem needed.** For every prime P with P >= 1,000,001 and P === 1 (mod 24), there exist positive integers alpha, s, r such that:
- M := 4*alpha*s*r - 1 divides P + 4*alpha*s^2
- A := alpha*s*(m*r - s) lies in [(P+3)/4, (3P-3)/4], where m = (P + 4*alpha*s^2)/M

This is Dyachenko's Lemma D.6 parametrization (arXiv:2511.07465). The bridge to the Erdos-Straus conjecture is already proven in Lean.

## Equivalent reformulation (simpler)

Setting alpha = 1 for simplicity (alpha > 1 gives additional flexibility), the condition becomes:

**For every prime P >= 10^6 with P === 1 (mod 24), there exists s >= 1 such that P + 4s^2 has a divisor d with d === -1 (mod 4s).**

Why this is equivalent: if d === -1 (mod 4s) and d | (P + 4s^2), set r = (d+1)/(4s). Then M = 4sr - 1 = d divides P + 4s^2. The D.6 construction then produces valid ED2 parameters.

Even simpler: d === -1 (mod 4s) means d = 4sr - 1 for some r >= 1, so we need some r >= 1 with (4sr - 1) | (P + 4s^2).

## What I have tried and what failed

### Approach 1: Fixed offset (24 offsets), DISPROVED

I tried showing that for A_k = (P+3)/4 + k and delta_k = 3 + 4k (k = 0..23), some d | A_k^2 satisfies delta_k | (d + A_k). This is FALSE. Counterexample: P = 8,803,369 (prime, 1 mod 24). All 24 offsets fail because A_0 = 2,200,843 is prime (so A_0^2 has only 3 divisors) and the remaining A_k have unlucky factorizations.

### Approach 2: Lattice argument (Dyachenko Section 9.10), CIRCULAR

The kernel lattice L = {(u,v) : g | ub' + vc'} takes (g, b', c') as inputs. But b', c' are what we're trying to find. Two independent GPT Pro analyses confirmed this circularity. The lattice is a search tool once coefficients are fixed, not an existence engine.

### Approach 3: The D.6 parametric search (what works empirically)

The `findED2` function searches over (alpha, r, s) with alpha in 1..5, s in 1..50, r in 1..50. This succeeds for EVERY prime P === 1 (mod 24) up to 10,000,000+. But "it works computationally" is not a proof for all P.

## Empirical data on failure rates

For each (alpha, s) pair, the "failure condition" is: P + 4*alpha*s^2 has NO divisor === -1 (mod 4*alpha*s).

For alpha = 1, s = 1: failure iff all prime factors of P+4 are === 1 (mod 4). Failure rate: 46.7%.

Joint failure rates (testing all (alpha, s) with 4*alpha*s^2 <= K):

```
K=   4:  1 pair   -> 46.7% fail
K=   8:  2 pairs  -> 16.9% fail
K=  16:  5 pairs  -> 4.8% fail
K=  32: 10 pairs  -> 0.78% fail
K=  64: 22 pairs  -> 0.095% fail
K= 100: 35 pairs  -> 0.025% fail
K= 128: 46 pairs  -> 0.006% fail
K= 200: 74 pairs  -> 0.000% fail (zero in 82,887 primes up to 10M)
```

The decay is roughly exponential: each additional pair eliminates ~30% of remaining failures.

## What I need you to prove

**Primary question:** Prove that for all primes P >= B (for some explicit B), there exists s with 1 <= s <= S (for some explicit S) such that P + 4s^2 has a divisor d === -1 (mod 4s).

Allowing alpha > 1 as well is fine and may make the proof easier.

The bound B should ideally be <= 10^6 (so our computational certificate handles P < B). If B is larger, that's acceptable as long as it's computationally feasible to extend the certificate.

## Suggested approaches

### Approach A: Explicit covering system

For specific choices of s and r, the modulus M = 4sr - 1 covers the residue class P === -4s^2 (mod M). If we can find a finite set of (s, r) pairs whose moduli M_i have lcm Q, and the union of covered classes hits every residue mod Q that is === 1 (mod 24), we're done.

The challenge: the lcm grows fast. But we only need to cover residues === 1 (mod 24), which is 1/24 of all residues.

Key structural fact from our computation: for each prime q dividing some M value, residue 0 mod q is the ONLY residue never covered. Since P is prime and P > q for P >= 10^6, the residue P mod q is never 0. This means the only obstruction comes from residue 0, which is automatically excluded for prime P.

**This might mean the covering works with a very small set.** Can you make this rigorous?

### Approach B: Divisor distribution in shifted primes

For fixed s, the question "does P + 4s^2 have a divisor === -1 (mod 4s)?" is equivalent to: does P + 4s^2 have a prime factor q with q === -1 (mod 4s), or more generally, do the prime factors of P + 4s^2 multiplicatively generate a subgroup of (Z/4sZ)* that contains -1?

For s = 1: does P + 4 have a prime factor === 3 (mod 4)? By Landau-Ramanujan, numbers with all prime factors === 1 (mod 4) have density ~C/sqrt(log N). So the failure probability for s = 1 alone is ~1/sqrt(log P), which goes to 0 but slowly.

But for s = 1 AND s = 2 to both fail, we need P + 4 to have all factors === 1 (mod 4) AND P + 16 to have no divisor === 7 (mod 8). These conditions involve DIFFERENT numbers (P+4 vs P+16), so they should be approximately independent.

If each failure has probability ~C_s/sqrt(log P), and we have K independent conditions, the joint failure probability is ~prod(C_s/sqrt(log P)) ~ C^K / (log P)^{K/2}. For K large enough, this is o(1/P), and then summing over primes gives a convergent series, proving that only finitely many primes fail.

**Can you make this rigorous?** The key issue is proving sufficient independence between the conditions for different s values. They're not fully independent (P + 4s^2 for different s share the same P), but they should be sufficiently independent because the relevant moduli are different.

### Approach C: Character sum / sieve lower bound

For fixed s, define f_s(P) = 1 if P + 4s^2 has a divisor === -1 (mod 4s), and 0 otherwise. Then we want to show max_s f_s(P) = 1 for all large P.

Equivalently, show that sum_{s=1}^{S} f_s(P) >= 1 for all large P.

A lower bound on sum_s f_s(P) averaged over P in an interval might be obtainable via sieve methods, and then a variance bound could show the sum is positive for individual P.

### Approach D: Direct construction using quadratic reciprocity

For s = 1: we need a prime q | (P+4) with q === 3 (mod 4). If P+4 is even (it's not, since P is odd), this is trivial. P+4 is odd. If P+4 === 3 (mod 4), then P+4 itself has a factor === 3 (mod 4). But P === 1 (mod 24) gives P+4 === 5 (mod 8), so P+4 === 1 (mod 4). So P+4 could have all factors === 1 (mod 4).

For s = 3: we need a divisor of P + 36 that is === -1 (mod 12), i.e., === 11 (mod 12). Since P === 1 (mod 24), P + 36 === 37 === 13 (mod 24). So P + 36 === 1 (mod 12). Every prime factor of P+36 is either 2, 3, or coprime to 6. We need one that's === 11 (mod 12), i.e., === -1 (mod 12).

For s = 6: divisor of P + 144 === -1 (mod 24). P + 144 === 145 === 1 (mod 24). We need a prime factor === 23 (mod 24).

Hmm, for s where 4s | 24 (s = 1, 2, 3, 6), the values P + 4s^2 have predictable residues mod 24. For other s values, the residues mod 4s are less constrained.

### Approach E: Pigeonhole on small primes

Consider the primes q = 3, 7, 11. Each gives a D.6 modulus:
- q = 3: M = 3 means 4sr = 4, so s = r = 1, alpha = 1. Covers P === -4 === 2 (mod 3).
- q = 7: M = 7 means 4sr = 8, so (s,r) in {(1,2),(2,1)}, alpha = 1. Covers P === -4 === 3 (mod 7) and P === -16 === 5 (mod 7).
- q = 11: M = 11 means 4sr = 12, so (s,r) in {(1,3),(3,1)}, alpha = 1. Covers P === -4 === 7 (mod 11) and P === -36 === 8 (mod 11).

P === 1 (mod 24) means P === 1 (mod 3). So q = 3 never helps (covers P === 2 mod 3).

P mod 7 can be anything (gcd(24,7) = 1). The two covered classes are {3, 5}. Uncovered: {0, 1, 2, 4, 6}. But P prime and P > 7 means P mod 7 != 0. So uncovered: {1, 2, 4, 6}.

With alpha = 2, s = 1, r = 1: M = 7, covers P === -8 === 6 (mod 7). Now uncovered mod 7: {1, 2, 4}.

With alpha = 3, s = 1, r = 1: M = 11, covers P === -12 === 10 (mod 11).
With alpha = 4, s = 1, r = 1: M = 15, covers P === -16 === 14 (mod 15).

This is getting complicated but structured. The question is whether enough small primes q can be covered to handle all residue classes.

**Can you systematically check: for each small prime q, which residue classes of P mod q are covered by (alpha, s, r) triples with M = q? And does the CRT product of uncovered classes eventually become empty (restricted to P === 1 mod 24 and P prime)?**

## Constraints

1. The proof must be mathematically complete. No "by density heuristics" or "the probability goes to zero."
2. Ideally the proof is elementary enough to formalize in Lean 4 without importing analytic number theory.
3. If a fully elementary proof is impossible, state what the minimal analytic input is (e.g., "we need Dirichlet's theorem on primes in arithmetic progressions" which IS in Mathlib).
4. An explicit covering system verified by finite computation is the ideal answer, as it reduces to a decidable check.
5. If no proof exists for all P, give the best conditional result and the smallest explicit B for which it holds.
