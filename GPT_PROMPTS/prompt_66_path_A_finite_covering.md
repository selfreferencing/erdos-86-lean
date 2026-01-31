# Prompt 66: Path A - Finite Covering via Forced Small-Prime Structure

## Context

From the Route C1 roadmap and GPT evaluation, we identified that the core problem is proving Lemma 3: "k ≤ 15 always suffices for hard primes."

**Path A** attempts to prove this using only the **forced small-prime structure** in x₀,...,x₁₅, without relying on unpredictable large prime factors.

## The Setup

For hard primes p ≡ r (mod 840) with r ∈ {1, 121, 169, 289, 361, 529}:
- x₀ = (p+3)/4 ≡ (r+3)/4 (mod 210)
- x_k = x₀ + k for k = 0,...,15
- m_k = 4k + 3

**Forced small prime factors:**
- 2 | x_k ⟺ k odd
- 3 | x_k ⟺ k ≡ 2 (mod 3)
- 5 | x_k depends on class (k ∈ {4,9,14} or {2,7,12})
- 7 | x_k depends on class

**Target:** e ≡ 3k+2 (mod 4k+3), which is always a **quadratic nonresidue** mod m_k.

## The Core Question

**Can the forced small primes (2, 3, 5, 7) alone guarantee that some k ≤ 15 succeeds?**

If yes, this gives a **fully explicit, finite proof**.

## Research Questions

### Q1: Quadratic Character of Small Primes

For each k ∈ {0,...,15} and each small prime q ∈ {2, 3, 5, 7}:

Compute the Legendre symbol (q | m_k) where m_k = 4k+3.

Format:
```
k | m_k | (2|m) | (3|m) | (5|m) | (7|m) | Which are QNR?
```

This tells us which forced factors can provide the "escape" to the non-square coset.

### Q2: Which k-values Can Succeed with Forced Factors Alone?

For each hard class and each k:
- What small primes divide x_k (forced)?
- Are any of them QNRs mod m_k?
- If so, can the divisors of x_k² hit the target e₀?

Give a table:
```
Class | k | Forced factors | QNR among them? | Can hit target?
```

### Q3: Certificate Templates Using Only Small Primes

For each k where forced factors include a QNR:

Can you write an explicit formula for e in terms of powers of 2, 3, 5, 7 that hits e₀(m_k)?

Example: For k=2, m=11, target e₀=8:
- If 3 | x and 3 is QNR mod 11, can some power of 3 (times other factors) give 8?

### Q4: The Finite Covering Argument

**Key question:** Is there a finite modulus L such that:

For every residue class of x₀ mod L (consistent with hard classes), at least one k ∈ {0,...,15} has:
1. A forced small prime factor that is QNR mod m_k, AND
2. That factor (possibly with other forced factors) can hit the target e₀

If such L exists, what is it? (Start with L = 210, try L = 2310 = 2·3·5·7·11 if needed)

### Q5: Where Does Forced-Factor-Only Fail?

Identify the residue classes of x₀ (mod L) where:
- For ALL k ≤ 15, either no forced factor is QNR, OR the QNR factor can't hit the target

These are the cases that would require an "escape prime" (large unpredictable factor).

### Q6: Can We Eliminate the Failures?

For the failure cases from Q5:
- How many residue classes fail?
- Can we prove these classes contain only finitely many primes? (Using sieve arguments)
- Or can we show some other k (with larger m) rescues them?

## Desired Output

1. **Complete quadratic character table** for small primes vs all 16 moduli
2. **Forced-factor success table** by hard class and k
3. **Explicit certificate templates** where they exist
4. **The finite modulus L** if covering works
5. **List of failure cases** (residue classes needing escape primes)
6. **Assessment:** Does Path A give a complete proof, or only partial coverage?

## Goal

Determine whether Route C1 can be proven using **only the deterministic small-prime structure**, making it a fully finite, combinatorial argument with no reliance on distribution of large primes.
