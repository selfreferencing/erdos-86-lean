# TASK: Derive Explicit Computational Verification Bound

## Context

We have verified computationally that K13 = {0,1,2} ∪ K10 covers all Mordell-hard primes ≤ 10^7.

**Goal:** Find an explicit N such that:
- For p > N, K13 coverage follows from an asymptotic argument
- For p ≤ N, we have computational verification

Ideally N ≤ 10^7 (already verified) or N small enough to extend verification.

## The Asymptotic Argument Structure

For large p, x_k = (p + m_k)/4 ≈ p/4 is large.

Large numbers tend to have:
1. Many prime factors
2. Diverse prime factors (not all in QR subgroup)
3. Many divisors in any given residue class

## Quantitative Bounds Needed

### Bound 1: Number of Prime Factors

By Hardy-Ramanujan: ω(n) ~ log log n on average.

For n > N₁, we have ω(n) ≥ f(N₁) with high probability.

**Question:** What's an explicit N₁ such that for n > N₁, ω(n) ≥ 3 always (or with quantifiable exceptions)?

### Bound 2: Primitive Root Probability

The density of primes that are primitive roots mod m_k is given by Artin's conjecture (conditional on GRH).

For m_k prime, this density is approximately 0.3739... (Artin's constant).

**Question:** For p > N₂, what's the probability that at least one x_k has a primitive root factor?

### Bound 3: Subgroup Coverage

If x_k has r distinct prime factors, the generated subgroup of (Z/m_k Z)* has size at least 2^r (roughly).

For m_k ≤ 119 (max in K10), |（Z/m_k Z)*| ≤ 96.

**Question:** How many prime factors guarantee the generated subgroup is the full group?

## Data-Driven Approach

From computational verification up to 10^7:
- Distribution of "first successful k" in K13
- Characteristics of the "close call" primes (those requiring high k)
- Maximum k needed as function of p

**Question:** Is there a pattern suggesting a bound N where k ≤ 14 always suffices?

## YOUR TASK

1. **Derive explicit bounds** N₁, N₂, N₃ for the three components above

2. **Combine into N = max(N₁, N₂, N₃)** such that for p > N:
   - Either ω(x_k) is large enough, OR
   - Primitive root probability is high enough, OR
   - Subgroup coverage is guaranteed

3. **Compare N to 10^7:** If N ≤ 10^7, we're done. If N > 10^7, estimate the additional verification needed.

4. **If unconditional bound is too large:** State what's achievable under GRH or other standard hypotheses.

## Deliverable

An explicit statement:
> For all Hard10 primes p > N, at least one k ∈ K10 provides a witness.

with:
- N explicitly computed
- The argument for p > N clearly stated
- Any conditional assumptions (GRH, etc.) identified
