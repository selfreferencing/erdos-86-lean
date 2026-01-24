# TASK: Analyze the K10 Cascade Structure for Hard10 Coverage

## Context

We have verified computationally that K10 = {5, 7, 9, 11, 14, 17, 19, 23, 26, 29} covers all 2,725 "Hard10" primes ≤ 10^7.

Hard10 = Mordell-hard primes NOT covered by k ∈ {0, 1, 2}.

**Key empirical observation:** The K10 cascade is highly efficient:
- k=5 (m=23): catches 64% of Hard10 primes
- k=7 (m=31): catches 21% of remaining
- k=9 (m=39): catches 8% of remaining
- k=11 (m=47): catches 4% of remaining
- Higher k: catches < 3% combined

This suggests k=5 alone catches most Hard10 primes, and each subsequent k catches most of what remains.

## The Type II Witness Condition

For k ∈ K10 with m_k = 4k + 3:
- x_k = (p + m_k) / 4
- Witness exists iff: ∃ d | x_k², d ≤ x_k, d ≡ -x_k (mod m_k)

## Key Questions

### 1. Why Does k=5 (m=23) Catch 64%?

What is special about m=23 that makes it catch most Hard10 primes?

Observations:
- 23 is prime, so (Z/23Z)* is cyclic of order 22
- Hard10 primes fail k=0,1,2, so they satisfy specific congruence conditions
- These conditions might make k=5 especially likely to work

**Task:** Characterize exactly when k=5 fails for a Hard10 prime.

### 2. Why Does the Cascade Work?

The cascade structure suggests:
- If k=5 fails, k=7 usually succeeds
- If k=5 and k=7 fail, k=9 usually succeeds
- etc.

**Hypothesis:** The failures at each stage are "orthogonal" - the conditions that make k=5 fail tend to make k=7 succeed, etc.

**Task:** Prove or disprove this orthogonality hypothesis algebraically.

### 3. Probability of All K10 Failing

If each k ∈ K10 independently fails with probability ε_k:
- ε_5 ≈ 0.36 (36% not caught by k=5)
- ε_7 | k=5 fails ≈ 0.79 × 0.36 ≈ 0.28
- etc.

**But these are NOT independent.** The failure at k=5 constrains the factorization of x_5, which constrains the factorizations of other x_k.

**Task:** Analyze the dependency structure. Show that despite dependencies, the combined probability of all 10 failing is 0 for Hard10 primes.

### 4. Why Does K10 Work When K3 = {0,1,2} Fails?

The 2,725 Hard10 primes all fail k=0,1,2 but all have a K10 witness.

This is suspicious - why should the "hard" primes be perfectly covered by a different set?

**Hypothesis:** The conditions that make k=0,1,2 fail actually GUARANTEE that some k ∈ K10 succeeds.

**Task:** Find this guarantee algebraically.

## Data Available

From computational verification up to 10^7:
- First successful k distribution: 64% at k=5, 21% at k=7, 8% at k=9, 4% at k=11, <3% higher
- The "last resort" k=29 is rarely needed
- Maximum k needed decreases as p increases (for Hard10 primes)

## Approaches

### Approach 1: Subgroup Analysis

For each k, the divisors of x_k² generate a subgroup of (Z/m_k Z)*.

The target -x_k must be in this subgroup for a witness to exist.

**Question:** When does Hard10 status FORCE -x_k into the subgroup for some k ∈ K10?

### Approach 2: Residue Class Partitioning

Hard10 primes satisfy specific congruence conditions mod lcm(3, 7, 11, 840).

Partition Hard10 by these residue classes.

**Question:** Does each partition class have a guaranteed k ∈ K10 witness?

### Approach 3: Primitive Root Density

If x_k has a factor q that is a primitive root mod m_k, then the divisors generate all of (Z/m_k Z)*, guaranteeing a witness.

**Question:** For Hard10 primes, is there always some k where x_k has such a factor?

## Deliverables

1. **Explain the cascade:** Why does k=5 catch 64%, k=7 catch 21% of remainder, etc.?

2. **Prove orthogonality:** Show that failures at different k values are "anti-correlated" - if k_i fails, k_j is MORE likely to succeed.

3. **Derive a guarantee:** Find an explicit condition on Hard10 primes that guarantees K10 coverage.

4. **Bound the cascade:** Prove that for Hard10 primes, some k ∈ K10 must succeed (not just probably succeeds).

## Alternative Outcome

If you cannot prove the guarantee, characterize the "worst case" primes:
- What would a Hard10 prime that fails all K10 look like?
- Show such primes cannot exist (constructive impossibility proof).
