# Prompt 67: Path B - Structural Contradiction from "All k Fail"

## Context

From the Route C1 roadmap and GPT evaluation, we identified that the core problem is proving Lemma 3: "k ≤ 15 always suffices for hard primes."

**Path B** attempts to prove this by showing that **16 consecutive integers cannot all fail** - i.e., deriving a contradiction from the assumption that no k ∈ {0,...,15} works.

## The Setup

For a hard prime p, define x_k = ⌈p/4⌉ + k and m_k = 4k + 3.

**k fails** means: No divisor e | x_k² satisfies e ≡ e₀(m_k) (mod m_k), where e₀ = 3k+2.

**Two failure modes identified (Prompt 64):**

1. **Subgroup obstruction:** All prime factors of x_k are QRs mod m_k, so all divisors are QRs, but target e₀ is QNR.

2. **Exponent-box obstruction:** Some prime factors are QNRs (target is reachable in principle), but the required representation needs exponent > 2v_q(x_k).

## The Core Question

**Can 16 consecutive integers x₀, x₀+1, ..., x₀+15 all satisfy the failure conditions for their respective moduli m_0, m_1, ..., m_{15}?**

If not (for large x₀), then Route C1 is proven.

## Research Questions

### Q1: Formalize the Failure Conditions

For each k, write the precise condition "k fails" as a constraint on x_k.

**Subgroup failure:** All prime factors q | x_k satisfy (q | m_k) = +1

**Exponent failure:** Characterize when target is in generated subgroup but not reachable with bounded exponents.

### Q2: Define the "Failure Sets"

For each k, define:
```
F_k = { n ∈ Z⁺ : "k fails for n" }
```

What is the structure of F_k?
- Is it a multiplicative set (closed under multiplication)?
- Is it defined by prime-factor residue conditions?
- What is its density?

### Q3: Intersection of Shifted Failure Sets

The "all k fail" condition means:
```
x₀ ∈ F_0 ∩ (F_1 - 1) ∩ (F_2 - 2) ∩ ... ∩ (F_{15} - 15)
```

where (F_k - k) = {n : n+k ∈ F_k}.

**Question:** Is this intersection finite? Empty for large x₀?

### Q4: Runs in Multiplicative Sets

There's classical number theory about "runs of consecutive integers in special sets."

**Key fact:** Consecutive integers are coprime, so they can't share prime factors.

**Question:** Does this constraint force at least one x_k to have a "good" prime factor (QNR for its modulus)?

### Q5: The 16-Moduli Constraint System

For "all k fail," we need:
- x₀ has all prime factors QR mod 3
- x₀+1 has all prime factors QR mod 7
- x₀+2 has all prime factors QR mod 11
- ...
- x₀+15 has all prime factors QR mod 63

**Each consecutive integer must avoid ALL QNR primes for its modulus.**

Since consecutive integers are coprime, the prime factors are "spread out" across the 16 integers. Can they all avoid their respective QNR sets?

### Q6: Density/Sieve Argument

**Heuristic:** For each k, Pr(all factors of n are QR mod m_k) ≈ 1/√(log n) (smooth number bounds).

For 16 independent such constraints: Pr(all fail) ≈ (1/√log n)^{16} = 1/(log n)^8 → 0.

**Question:** Can this heuristic be made rigorous? What tools apply?
- Large sieve?
- Multiplicative function distribution?
- Smooth number theory?

### Q7: The Exponent-Box Complication

Even if some x_k has a QNR factor, it might still fail due to exponent bounds.

**Question:** How restrictive is the exponent-box condition?
- For which (k, m_k) pairs is exponent failure even possible?
- Can we bound how often it occurs?

### Q8: Explicit Contradiction for Large x₀

**Goal:** Prove that for x₀ > X₀ (explicit), the intersection from Q3 is empty.

**Approach ideas:**
1. CRT: The 16 moduli {3,7,11,...,63} have lcm L. Work mod L.
2. Sieve: Count integers n ≤ N with all prime factors in specific residue classes.
3. Covering: Show the QNR primes for different moduli "cover" the small primes.

### Q9: What If Contradiction Fails?

If we can't prove the intersection is empty:
- Can we show it's finite?
- Can we characterize its elements?
- Does computation help identify all elements up to some bound?

## Desired Output

1. **Precise formalization** of failure conditions for each k
2. **Structure of failure sets F_k** (multiplicative? density?)
3. **Analysis of the 16-fold intersection** - when is it empty?
4. **Rigorous density/sieve argument** if possible
5. **Explicit threshold X₀** if contradiction can be proven
6. **Fallback:** If full contradiction fails, what partial results are achievable?

## Goal

Prove that for sufficiently large x₀, at least one k ∈ {0,...,15} must succeed - by showing the simultaneous failure conditions are too restrictive to all hold.

This would complete the Route C1 proof.
