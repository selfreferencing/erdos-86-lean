# APPROACH 37: Decorrelation - CF Denominators Avoid Powers of 10

## Context

We are working on the Erdős 86 Conjecture. The major/minor arc approach (34A/34B) identified a "two-resonance" structure:

1. **Rotation resonance:** k near continued fraction denominators of θ₀ = log₁₀(2)
2. **Digit resonance:** k divisible by large powers of 10

The "double major arc" (region IV) where BOTH resonances occur is potentially dangerous. The proof requires showing this region is either:
- Very sparse, or
- The Fourier coefficients are still small there

This prompt focuses on proving **decorrelation**: the two resonance conditions rarely overlap.

## The CF Denominators of θ₀

θ₀ = log₁₀(2) = [0; 3, 3, 9, 2, 2, 4, 6, 2, 1, 1, 3, 1, 18, ...]

Convergent denominators:
```
q_n: 1, 3, 10, 93, 196, 485, 2136, 13301, 28738, 42039, 70777, 112816, 2101265, ...
```

## The Decorrelation Claim

**Claim:** For most n, the CF denominator q_n is NOT divisible by a large power of 10.

More precisely: the sequence v₁₀(q_n) (the 10-adic valuation of q_n) is typically 0 or 1.

## Questions

### Q1: Compute v₁₀(q_n) for n = 0, ..., 50

For each convergent denominator q_n, compute:
- q_n itself
- v₂(q_n) = largest power of 2 dividing q_n
- v₅(q_n) = largest power of 5 dividing q_n
- v₁₀(q_n) = min(v₂(q_n), v₅(q_n))

Present in a table.

### Q2: Pattern Analysis

Looking at the v₁₀(q_n) sequence:
1. How often is v₁₀(q_n) = 0?
2. How often is v₁₀(q_n) = 1?
3. How often is v₁₀(q_n) ≥ 2?
4. Is there a pattern?

### Q3: Theoretical Explanation

Why should we expect v₁₀(q_n) to be small for most n?

The CF denominators satisfy the recurrence:
```
q_{n+1} = a_{n+1} · q_n + q_{n-1}
```
where a_{n+1} is the (n+1)-th partial quotient.

For θ₀ = log₁₀(2), the partial quotients are known to be unbounded but with no special structure.

**Question:** Is there a theorem saying that for "generic" continued fractions, the denominators avoid high prime powers?

### Q4: The Key Divisibility Question

For the double major arc to be dangerous, we need k such that:
1. |k·θ₀| < 1/L (rotation resonance)
2. 10^J | k for large J (digit resonance)

Condition 1 means k is close to a multiple of some q_n.

**Question:** If k = r·q_n with r small, what is v₁₀(k)?

Since v₁₀(k) ≥ v₁₀(q_n), we need v₁₀(q_n) to be small for this to not be in the digit-major arc.

### Q5: Explicit Decorrelation Bound

**Desired statement:** There exists J_0 such that for all n with q_n ≤ 10^{100}:
```
v₁₀(q_n) ≤ J_0
```

What is the smallest J_0 that works? (Based on computation of the first 50+ denominators.)

### Q6: Consequences for the Proof

If v₁₀(q_n) ≤ J_0 for all relevant n, then:
- The double major arc has k = r·q_n with v₁₀(k) ≤ J_0 + v₁₀(r)
- If we set J = J_0 + 5 in the digit-major arc definition, the double major arc is essentially empty

This would resolve the decorrelation question.

**Question:** Is J_0 small enough for this to work?

### Q7: What if Decorrelation Fails?

Suppose some q_n is divisible by 10^{100}. Then what?

Options:
1. **Direct bound:** Show |ĉ_{F_m}(q_n)| is small anyway (using other structure)
2. **Sparse contribution:** Show such q_n are so rare that their contribution is negligible
3. **Explicit computation:** For specific "bad" q_n, compute the contribution directly

Which option is most viable?

### Q8: Connection to θ₀'s Arithmetic

θ₀ = log₁₀(2) = log(2)/log(10).

Does the special form of θ₀ (ratio of logarithms of 2 and 10) impose structure on the CF denominators?

Note: 10 = 2 × 5, so there's an intrinsic connection between θ₀ and the prime 5.

**Question:** Does this connection help or hurt the decorrelation argument?

## Desired Output

1. **Table of v₁₀(q_n)** for n = 0, ..., 50
2. **Statement and proof** (or evidence) that v₁₀(q_n) is bounded
3. **Explicit value of J_0** (the maximum 10-adic valuation observed)
4. **Conclusion:** Does decorrelation hold? If so, with what parameters?

## Why This Matters

The decorrelation claim is one of the 5 lemmas in the proof skeleton. If it fails, we need a different approach to the double major arc. If it holds with good parameters, the double major arc is essentially empty and the proof is much cleaner.
