# TASK: Prove the Covering Property Theorem

## The Theorem

**Theorem (Covering Property)**: For every prime p ≥ 5, let:
```
n = (p + 23) / 4
S = {n, n+2, n+4, n+6, n+9, n+12, n+14, n+18, n+21, n+24}
```

Then **at least one element of S has an odd prime factor q with (p/q) = -1**.

Here (p/q) is the Legendre symbol.

## Why This Matters

This theorem is the FINAL STEP in proving that the Erdős-Straus conjecture holds for all "Mordell-hard" primes (primes ≡ 1, 121, 169, 289, 361, 529 mod 840).

Via quadratic reciprocity, we have shown:
- The Bradford Type II obstruction at parameter k fails if any prime factor q of x_k satisfies (p/q) = -1
- The set S consists of the x_k values for k ∈ {5, 7, 9, 11, 14, 17, 19, 23, 26, 29}
- So if ANY element of S has a "bad" prime factor (with (p/q) = -1), the conjecture holds

## What We Know

1. **Computationally verified** for all primes p ≤ 50,000 (137 Mordell-hard primes)
2. The elements of S have **12-16 distinct odd prime factors** collectively
3. On average, **7-8 of these are "bad"** (have (p/q) = -1)
4. The **minimum observed is 3-5 bad factors** - never 0

## Constraints

- The theorem MUST hold for ALL primes, not just "almost all" or "with high probability"
- A probabilistic/heuristic argument is NOT sufficient
- Need a rigorous proof or reduction to finite verification

## Possible Approaches

### 1. Pseudo-Square Argument
If p is a QR mod every prime dividing any element of S, then p "looks like a square" mod all these primes. But primes aren't squares. Formalize this contradiction.

### 2. Sieve Theory
The 10 elements of S span a range of 25 integers. Use a covering sieve to show they must include a factor from any set of positive density.

### 3. Chebotarev + Large Sieve
The set of primes q with (p/q) = -1 has density exactly 1/2. Use a large sieve inequality to show S cannot avoid all of them.

### 4. Structural Argument
The elements n, n+2, n+4, n+6, n+9, n+12, n+14, n+18, n+21, n+24 have GCD structure that forces diversity of prime factors.

### 5. Finite + Asymptotic
- For p ≤ N: verify computationally (done for N = 50,000)
- For p > N: the elements of S are large enough that they must have factors in the "bad" half

## YOUR TASK

Provide a complete, rigorous proof of the Covering Property Theorem.

The proof should:
1. Work for ALL primes p ≥ 5 (not just large ones or almost all)
2. Be mathematically rigorous (no heuristics or probabilistic bounds)
3. Identify any finite computations needed (we can verify these in Lean)

If a complete proof is not immediately possible, identify the key lemma that is missing and prove as much as you can.
