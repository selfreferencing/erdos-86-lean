# GPT Prompt: Eliminate the ED2 Existence Axiom

## The Axiom to Eliminate

For every prime P ≡ 1 (mod 4), there exist natural numbers α (squarefree), d' ≥ 1 such that:

1. N = 4αP(d')² + 1 has a factorization N = X × Y
2. X ≡ Y ≡ -1 (mod 4αd')
3. gcd((X+1)/(4αd'), (Y+1)/(4αd')) = 1

## Equivalent Formulation

For δ = α(d')², the condition simplifies to finding a factorization of N = 4Pδ + 1 where both factors satisfy a specific congruence condition modulo 4αd'.

**Simplest case (α=1, d'=1, δ=1):**
- N = 4P + 1
- Need: N = X × Y with X ≡ Y ≡ 3 (mod 4)
- This works iff N has a prime factor q ≡ 3 (mod 4)

## Computational Evidence

Tested 4,783 primes P ≡ 1 (mod 4) up to 100,000:
- **100% success rate**
- Maximum δ needed: 95 (for P = 46237)
- Distribution: 59% need δ=1, 76% need δ≤2, 100% need δ≤100

The paper (Dyachenko, arXiv:2511.07465) claims verification up to 10^8.

## Key Observations

### When δ=1 fails:
δ=1 fails exactly when N = 4P+1 is a "1 (mod 4) number" (all prime factors ≡ 1 mod 4).

Examples:
- P = 13: N = 53 (prime ≡ 1 mod 4)
- P = 37: N = 149 (prime ≡ 1 mod 4)
- P = 73: N = 293 (prime ≡ 1 mod 4)

### When δ=2 rescues:
For δ=2 (α=2, d'=1), N = 8P+1, need X ≡ Y ≡ 7 (mod 8).
- P = 13: N = 105 = 7 × 15, both ≡ 7 (mod 8) ✓
- P = 73: N = 585 = 15 × 39, both ≡ 7 (mod 8) ✓

### The hardest case P = 37:
- δ=1: N = 149 (prime ≡ 1 mod 4) ✗
- δ=2: N = 297 = 27 × 11, no factors ≡ 7 (mod 8) ✗
- δ=3: N = 445 = 5 × 89, no factors ≡ 11 (mod 12) ✗
- δ=4: N = 593 (prime ≡ 1 mod 4) ✗
- δ=5: N = 741 = 19 × 39, both ≡ 19 (mod 20) ✓

## The Core Mathematical Question

**Why must some δ ≤ O(log P) always work?**

For the sequence N_δ = 4Pδ + 1 (δ = 1, 2, 3, ...), we need to show that at least one N_δ has the required factorization structure.

## Proof Approaches to Explore

### 1. Sieve Theory
Can we show that among N₁, N₂, ..., N_k for k = O(log P), at least one must have a prime factor q ≡ 3 (mod 4) with the right congruence properties?

### 2. Density Argument
The probability that a random odd number N has all prime factors ≡ 1 (mod 4) is roughly 1/√(log N). Can we make this rigorous for the specific sequence N_δ?

### 3. CRT Construction
For each small prime q ≡ 3 (mod 4), we can find δ_q such that q | N_{δ_q}:
- q | (4Pδ + 1) iff δ ≡ -(4P)^{-1} (mod q)

Can we show that for SOME such q, the additional congruence X ≡ Y ≡ -1 (mod 4αd') is satisfiable?

### 4. Residue Class Analysis
We analyzed P mod 840 (LCM of relevant moduli). Different primes in the same residue class need different (α, d'). Is there a pattern?

### 5. Key Lemma
**Lemma**: N odd with N ≡ 1 (mod 4) has factorization X × Y with X ≡ Y ≡ 3 (mod 4) iff N has ≥ 2 prime factors ≡ 3 (mod 4) (counting multiplicity).

Can we prove that for any P, some N_δ has this property?

## Critical Insight

The "hardest" residue class is P ≡ 37 (mod 840), NOT the Mordell-hard classes {1, 121, 169, 289, 361, 529} mod 840.

This means ED2 works fundamentally differently from congruence-covering methods. The difficulty comes from factorization structure, not quadratic residues.

## What We Need

A proof (or proof sketch) that for any prime P ≡ 1 (mod 4), there exists δ ≤ B for some explicit bound B (ideally B = O(log P) or even B = 100) such that the ED2 conditions are satisfied.

Alternatively, identify why this might be as hard as the full Erdős-Straus Conjecture (though our analysis suggests it shouldn't be, since it bypasses the Mordell-hard barrier).

## Context

This is for formalizing the Erdős-Straus Conjecture in Lean 4. We have a complete proof EXCEPT for this one existence axiom. Eliminating it would give a fully constructive proof.
