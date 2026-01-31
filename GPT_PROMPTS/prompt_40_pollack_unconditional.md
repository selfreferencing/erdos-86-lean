# Prompt 40: Pollack's Theorem and Unconditional ES Completion

## Context

We have a GRH-conditional proof of Erdős-Straus for p ≡ 1 (mod 24). The GRH axiom states:

> Under GRH, for every prime p ≡ 1 (mod 4), there exists a prime q << (log p)² with q ≡ 3 (mod 4) and (p/q) = -1.

This follows from effective Chebotarev in the biquadratic field K = Q(i, √p).

Paul Pollack's work (pollack.uga.edu/gica4.pdf) proves **unconditional** results about prime quadratic nonresidues in specified congruence classes using genus theory of binary quadratic forms.

## Questions

### Q1: What exactly does Pollack's theorem provide?

Please read Pollack's paper and extract the precise statement. Specifically:
- For a prime P ≡ 1 (mod 4), what does Pollack prove about the existence of primes q with (P/q) = -1?
- What congruence constraints on q can he guarantee?
- What size bounds (if any) does he give on q?

### Q2: Gap analysis

Our ES reduction needs:
- **Existence**: A prime q ≡ 3 (mod 4) with (p/q) = -1
- **Size bound**: q << (log p)² (or at least q << p^ε for small ε)

What does Pollack give vs what we need? Specifically:
- Does Pollack's theorem guarantee q ≡ 3 (mod 4)?
- Does Pollack give any effective size bound on q?
- If Pollack only gives existence without size bound, does that still help for ES?

### Q3: Does ES actually need the size bound?

This is the key question. Our current proof uses:
1. GRH gives small q with the right properties
2. q gives s with q | (p + 4s²)
3. The Dyachenko lattice argument produces (A, d) from such q

But does step 3 actually require q to be small? Or does it just need q to exist?

If we trace through Dyachenko's argument:
- The parameter s satisfies s² ≡ -p/4 (mod q)
- We need s in some range related to p

**Question**: If q exists but is potentially large (say q ~ p), can we still extract (A, d) satisfying the window and divisibility constraints? Or does the window constraint [(p+3)/4, (3p-3)/4] force q to be small?

### Q4: Alternative unconditional approaches

If Pollack doesn't directly give what we need, are there other unconditional results that might help?

**Burgess bounds**: The best unconditional result for least quadratic nonresidue gives:
- n_p << p^{1/(4√e) + ε} ≈ p^{0.152}

This is much weaker than GRH's (log p)² but still polynomial.

**Key question**: Does our ES reduction actually need q << (log p)², or would q << p^{0.15} suffice? If the latter, Burgess might close the gap unconditionally.

Other possibilities:
- Unconditional Linnik-type theorems
- Genus theory results beyond Pollack
- Hybrid sieve + Burgess approaches

### Q5: Is there a simpler structure we're missing?

The GPT calibration noted:
> "ES has a lot of internal flexibility (three denominators, multiple parametrizations). Many conjectures with this kind of flexibility end up solvable with unconditional tools once the right structure is found."

Is there a parameterization of ES solutions that doesn't require finding a special prime q at all? For instance:
- Direct divisor-sum approaches
- Greedy algorithms with correction terms
- Density arguments that don't reduce to prime placement

## Desired output

1. Precise statement of Pollack's main theorem relevant to our setup
2. Gap analysis: what Pollack gives vs what we need
3. Assessment: can Pollack (possibly with additional work) replace our GRH axiom?
4. If not Pollack, what's the most promising unconditional route?
5. Any "obvious" simplification we might be missing
