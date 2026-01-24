# TASK: Derive Effective Sieve Bound for K13 Coverage

## Context (Critical Updates)

The genus/norm approach is **DEAD**. GPT2 proved that "all prime factors split" does NOT imply principal genus representation. We cannot use Faltings/Diophantine finiteness.

**What we have:**
- K13 = {0,1,2} ∪ K10 covers all Mordell-hard primes ≤ 10^7 (computationally verified)
- Sieve methods show the "exceptional set" (primes failing K13) has density zero
- But density zero ≠ empty

**What we need:**
An effective bound N such that for Hard10 primes p > N, K10 definitely provides a witness.

## The Sieve Setup

Define for each prime ℓ:
- S_k = {ℓ prime : (ℓ/m_k) = +1} (primes that split for m_k)
- G_ℓ = {-k mod ℓ : k ∈ K10 and (ℓ/m_k) = -1} (good residues)

A Hard10 prime p fails ALL of K10 iff:
- r = (p+3)/4 satisfies r mod ℓ ∉ G_ℓ for every prime ℓ

## Key Structural Facts

1. **Coprimality:** For ℓ > 24, ℓ divides at most one x_k (since gcd(x_i, x_j) | |i-j|)

2. **Density of good residues:** By Chebotarev, roughly half of primes ℓ have (ℓ/m_k) = -1 for each k

3. **Expected |G_ℓ|:** For typical ℓ, about 5 of the 10 k-values have (ℓ/m_k) = -1, so |G_ℓ| ≈ 5

## The Sieve Bound

Standard sieve theory gives:
```
#{r ≤ R : r ∉ G_ℓ for all ℓ ≤ z} ≪ R / (log z)^c
```

where c depends on the average |G_ℓ|/ℓ.

Combined with prime counting in arithmetic progressions:
```
#{exceptional Mordell-hard p ≤ X} ≪ X / (log X)^{c+1}
```

## YOUR TASK

1. **Compute c explicitly** using the actual G_ℓ data for K10

2. **Derive an explicit N** such that:
   - Expected number of Hard10 failures in (N, ∞) is < 1
   - This N should be computable (ideally ≤ 10^7)

3. **If possible under GRH:** Prove there are NO Hard10 failures above some explicit N

4. **Alternative:** Find a covering congruence argument that doesn't require sieve estimates

## Useful Data

The m_k values and their quadratic character structure:
- m_5 = 23 (prime)
- m_7 = 31 (prime)
- m_9 = 39 = 3×13
- m_11 = 47 (prime)
- m_14 = 59 (prime)
- m_17 = 71 (prime)
- m_19 = 79 (prime)
- m_23 = 95 = 5×19
- m_26 = 107 (prime)
- m_29 = 119 = 7×17

## Note on the Actual Witness Condition

The obstruction O_k (all factors split) is NECESSARY but not SUFFICIENT for failure.

Even when O_k holds, there might still be a divisor d ≤ x_k with d ≡ -x_k (mod m_k).

So the sieve bound on "O_k holds for all k" is an UPPER bound on actual failures.

## Deliverable

An explicit statement:
> For all Hard10 primes p > N, at least one k ∈ K10 provides a Type II witness.

with N as small as possible (ideally ≤ 10^7 so it's already verified).
