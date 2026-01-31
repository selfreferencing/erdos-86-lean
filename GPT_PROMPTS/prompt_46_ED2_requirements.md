# Prompt 46: What Does ED2 Actually Require?

## Context

From 45A/45B, we learned the key strategic question is: what does the ED2 reduction actually require from q?

The ED2 method (Dyachenko's "ED2" parameterization for Erdős-Straus) reduces ES to finding a suitable q. But we need to know the EXACT requirements.

## The Current Understanding

We've been assuming:
1. q must be PRIME
2. q ≡ 3 (mod 4)
3. (p/q) = -1 (p is a quadratic nonresidue mod q)
4. q << √p (for the window constraint)

But 45A/45B suggest we should scrutinize these assumptions.

## Questions

### Q1: Does q need to be prime?

The ED2 reduction uses q to find s with s² ≡ -p (mod q).

- For prime q ≡ 3 (mod 4) with (p/q) = -1: -p is a quadratic residue (nonresidue × nonresidue = residue)
- For composite squarefree q: Could we use CRT to find such an s?
- What properties of q does the rest of ED2 actually use?

**Specifically:** If q = q₁q₂ with q₁, q₂ primes, both ≡ 3 (mod 4), what conditions on (p/q₁) and (p/q₂) would make ED2 work?

### Q2: What's the actual size constraint?

We've been saying q << √p for the "window constraint." But:

- Where exactly does this come from in Dyachenko's argument?
- Is it q << √p, or q << p^{1/4}, or something else?
- Could we accept a worse bound (say q << p^{0.4}) and still have ED2 work?

### Q3: The window constraint [(p+3)/4, (3p-3)/4]

The ED2 method produces A in the window [(p+3)/4, (3p-3)/4].

- How does q affect where A lands in this window?
- What's the relationship between |s| (the square root of -p mod q) and A?
- Is there flexibility here we haven't exploited?

### Q4: The divisibility condition d | A², (4A-p) | (d+A)

After finding A, we need a divisor d of A² satisfying (4A-p) | (d+A).

- Does this step depend on q being prime?
- Could a composite q give more divisor options?
- Is there a trade-off: larger q gives more divisors but harder to find?

### Q5: Could "almost prime" q work?

If q doesn't need to be prime, could we use:
- Semiprimes (q = q₁q₂, two prime factors)
- Squarefree numbers
- Numbers with bounded number of prime factors

For each: what would the analogous conditions be, and would effective Burgess + sieve methods give us such q?

### Q6: What if we relax multiple constraints?

Could we trade:
- Larger q (say q << p^{0.4} instead of q << √p)
- For easier-to-find q (e.g., squarefree instead of prime)

And still have ED2 produce valid ES decompositions?

## Desired Output

1. Precise statement of what ED2 requires from q
2. Whether "q prime" can be relaxed to "q squarefree" or similar
3. The exact size constraint and where it comes from
4. Whether there's flexibility we can exploit for effectivity
