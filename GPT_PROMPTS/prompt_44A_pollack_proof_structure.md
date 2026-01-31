# Prompt 44A: Pollack's Theorem 1.4 - Proof Structure

## Context

We need to understand the exact structure of Pollack's proof that gives:

> For p ≡ 1 (mod 4), there exists a prime q with q ≡ 3 (mod 4), (p/q) = -1, and q << p^{1/4+ε}.

This bound is UNCONDITIONAL but INEFFECTIVE (cannot extract explicit p₀).

## The Key Reference

Pollack's paper (often cited as "generalsplit6.pdf" or similar) proves this using the character combination:

ξ = (1 - χ₄)(1 - χ_p)

where χ₄ is the non-principal character mod 4 and χ_p is the Legendre symbol (·/p).

## Questions

### Q1: What is the exact statement of Theorem 1.4?

Please state Pollack's Theorem 1.4 precisely, including:
- All hypotheses
- The exact conclusion
- Any implicit assumptions

### Q2: What is the proof structure?

Outline the proof in 5-10 steps. For each step, identify:
- What technique is used (sieve, character sums, etc.)
- What bounds are invoked
- Whether the step is effective or ineffective

### Q3: Where does Siegel's theorem enter?

The ineffectivity comes from Siegel's theorem: |L(1,χ)| >>_ε f^{-ε}.

- At which step is this invoked?
- What specific inequality uses this bound?
- What would the proof look like if we had an explicit lower bound instead?

### Q4: What are the explicit ingredients?

List every theorem/lemma used in the proof that HAS an explicit version:
- Zero-free regions (Kadiri?)
- Zero density estimates
- Character sum bounds
- Sieve inequalities

For each, give the reference and the explicit constants if known.

### Q5: What is the "sieve skeleton"?

42A/43A mentioned a "sieve skeleton" of the form:

S(x) ≥ Main(x; p) - Err(x; p)

Write out this inequality explicitly. What are Main and Err in terms of the parameters?

## Desired Output

1. Precise statement of Theorem 1.4
2. Step-by-step proof outline with effectivity marked
3. Exact location where Siegel enters
4. List of explicit ingredients with references
5. The sieve inequality in explicit form
