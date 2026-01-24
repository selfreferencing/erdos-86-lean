# ESC Research: Current State (January 2026)

## The Single Remaining Gap

To prove ESC for all primes p ≡ 1 (mod 4), we need:

> **Micro-Theorem**: For every prime p ≡ 1 (mod 12) where:
> - (p+1)/2 has all prime factors ≡ 1 (mod 4)
> - G((p+3)/4, 3) = 0
>
> Some k ∈ {1, 2, 3, 4, 5} gives G((p+4k+3)/4, 4k+3) ≥ 1.

**Status**: Verified computationally to 10^7. No theoretical proof yet.

## What We Know

### Proven
1. **k=0 for p ≡ 5 (mod 12)**: Always works (GPT 3 proof)
2. **Algebraic construction**: If G(n_k, m_k) ≥ 1, ESC has a solution (Bradford 2025)

### Computationally Verified
- All primes to 10^7 satisfy ESC via Type II
- Maximum k needed: 5
- Only 49 primes (up to 10^4) require k ≥ 1 after both Type I (k=1) and Type II (k=0) fail

### The Hardest Cases
Only 2 primes require k=5:

| p | n_0 = (p+3)/4 | Why n_0 fails | n_5 = (p+23)/4 | Winning pair |
|---|---------------|---------------|----------------|--------------|
| 1201 | 301 = 7·43 | 7+43=50 ≢ 0 (mod 3) | 306 = 2·3²·17 | (6, 17): 6+17=23 |
| 2521 | 631 (prime) | Only pair (1,631), 632 ≢ 0 (mod 3) | 636 = 2²·3·53 | (2, 159): 2+159=161=7·23 |

## Key Structural Observation

For any p ≡ 1 (mod 12), the values n_0, n_1, ..., n_5 are **6 consecutive integers**.

Among any 6 consecutive integers:
- At least 3 are even (factor of 2)
- At least 2 are divisible by 3
- At least 1 is divisible by 6
- At least 1 is divisible by 5

This guarantees **divisor diversity**. The question: why does this diversity always produce a good pair for some k?

## The Consecutive Integer Formulation

**Restatement**: For n ≡ 1 (mod 3), at least one of:
- G(n, 3) ≥ 1
- G(n+1, 7) ≥ 1
- G(n+2, 11) ≥ 1
- G(n+3, 15) ≥ 1
- G(n+4, 19) ≥ 1
- G(n+5, 23) ≥ 1

**Constraint**: n arises from primes p ≡ 1 (mod 12) with (p+1)/2 having special factorization.

## Possible Proof Strategies

### 1. Covering System Approach
Show the "bad" conditions for each k cannot simultaneously hold for the same n.

### 2. Density Argument
Show that among 6 consecutive integers with constrained starting point, the probability all fail is 0.

### 3. Explicit Classification
For each k, classify when G(n+k, 4k+3) = 0. Show the intersection of these classifications is empty for valid n.

### 4. Divisor Sum Methods
Use multiplicative structure of n_k to bound G from below on average over k.

## Files

- [MICRO_THEOREM_K12_PROMPT.md](MICRO_THEOREM_K12_PROMPT.md) - Detailed prompt for GPT
- [MASTER_SYNTHESIS.md](MASTER_SYNTHESIS.md) - Previous synthesis of three GPT responses
- [GPT_PROOF_PROMPT.md](GPT_PROOF_PROMPT.md) - Original GPT prompts

## Next Steps

1. **Draft GPT prompts** for the consecutive integer formulation
2. **Investigate k=5 specifically**: Why do n+5 and m=23 always work as last resort?
3. **Look for covering argument**: Can we show incompatibility of all-fail conditions?
