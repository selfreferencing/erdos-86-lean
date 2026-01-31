# APPROACH 41: Adapt Maynard's Spectral Gap Methods

## Context

We are working on the Erdős 86 Conjecture. The proof strategy (34A/34B) explicitly parallels Maynard's work:

> "Same mechanism as Maynard's primes-with-restricted-digits, but easier because: no Type I/II estimates needed."

This prompt asks you to read and adapt the relevant parts of Maynard's paper.

## Reference

James Maynard, "Primes with restricted digits" (arXiv:1604.01041, published in Inventiones Mathematicae)

## The Parallel

| Maynard's Setting | Our Setting |
|-------------------|-------------|
| Primes p with digits in S | Powers 2^n that are zeroless |
| Counting function π_S(x) | Counting function N_m |
| Digit set S ⊂ {0,...,9} | Digit set {1,...,9} (no zeros) |
| Fourier analysis on digit sums | Fourier analysis on F_m |
| Type I/II estimates for primes | NOT NEEDED (orbit is explicit) |
| Spectral gap for digit correlations | **NEEDED** |

## Questions

### Q1: Maynard's Main Theorem

State Maynard's main theorem about primes with restricted digits.

What is the form of his result? (Asymptotic density, explicit bound, etc.)

### Q2: Maynard's Fourier Setup

How does Maynard set up the Fourier analysis?

What is his analog of our R_m(0)?

### Q3: Maynard's Major/Minor Arc Decomposition

Describe Maynard's major/minor arc decomposition:
1. How does he define major arcs?
2. How does he define minor arcs?
3. What bounds does he use on each?

### Q4: Maynard's Spectral Gap

**Key Question:** What spectral gap lemma does Maynard prove?

State the lemma precisely. What is the spectral gap parameter? What matrices/operators are involved?

### Q5: Maynard's Markov Model

Maynard compares the digit distribution to a Markov model.

1. What is the Markov model?
2. How does he prove the comparison?
3. What properties of the Markov model does he use?

### Q6: Adapting the Spectral Gap

Maynard's spectral gap applies to "missing digit" sets.

**Question:** Can we apply his lemma directly to our setting (F_m = zeroless sets)?

If not, what modifications are needed?

### Q7: The Decorrelation Argument

Maynard has to show that "Diophantine major arcs" and "digital major arcs" rarely overlap.

What is his decorrelation argument? Can we adapt it?

### Q8: The Role of Primes

Maynard's proof uses deep results about primes (Bombieri-Vinogradov, sieve methods).

**Question:** Which parts of his proof depend on primes, and which are "pure digit structure"?

List the key lemmas that are purely about digits and could be used directly.

### Q9: Extracting the Digit Lemmas

From Maynard's paper, extract the lemmas that are about:
- Fourier coefficients of digit-restriction sets
- Spectral gap for digit correlations
- Product structure of digit indicators

State these lemmas in a form applicable to our setting.

### Q10: What's Missing for Our Application?

After adapting Maynard's methods:
1. What do we get "for free"?
2. What additional work is needed for our specific problem?
3. Are there any obstructions?

## The Ideal Extraction

**Ideal Statement (adapted from Maynard):**

Let D ⊂ {0,1,...,9} be a proper subset with |D| = d. Let F_m(D) be the set of x ∈ [0,1) whose first m base-10 digits all lie in D.

Then for all k with v₁₀(k) ≤ γm:
```
|ĉ_{F_m(D)}(k)| ≤ C · (d/10)^m · polynomial correction
```

**Question:** Does Maynard prove this? If so, cite the theorem number. If not, what does he prove?

## Specific Sections to Read

If you have access to the paper, focus on:
1. **Section 2:** The Fourier setup
2. **Section 3:** The Markov model
3. **Section 4:** Spectral gap lemmas
4. **Section 6:** Major/minor arc decomposition

Summarize the key lemmas from each section.

## Desired Output

1. **Summary** of Maynard's approach
2. **Key lemmas** extracted and stated for our setting
3. **Adaptation roadmap:** what carries over, what doesn't
4. **The spectral gap lemma:** precise statement applicable to F_m
5. **Gap identification:** what's still needed after using Maynard's results

## Why This Matters

Maynard's paper is the template. If we can adapt his spectral gap lemma directly, the proof is essentially complete. If we can't, we need to understand exactly why not.
