# Prompt 62: Concrete Hybrid Attack Plan for Unconditional Effective ES

## Context

From prompts 60-61, we've established:

1. **Bradford's reduction:** For prime p, find x ∈ [p/4, p/2] and e | x² with (4x-p) | (4e+1)

2. **Modular coverage:** Bradford/Mordell identities cover all primes EXCEPT ~6 classes mod 840:
   ```
   p ≡ 1, 121, 169, 289, 361, 529 (mod 840)
   ```

3. **The barrier:** Diagonal coupling (m = 4x-p depends on x) - NOT Siegel zeros

4. **The path:** Hybrid approach combining explicit coverage + analytic methods

## Request

Please provide a **concrete attack plan** for proving unconditional effective ES via the hybrid approach.

---

## Part 1: Formalize Bradford's Modular Coverage

### Q1: What explicit identities cover which residue classes?

List the known modular identities (Mordell, Ionascu-Wilson, Salez, Bradford) and which residue classes mod 840 (or finer modulus) each covers.

Format:
```
Identity for p ≡ a (mod m): [explicit formula for x, or first denominator choice]
Covers classes: [list]
```

### Q2: After all known identities, what EXACTLY remains?

Give the precise residue classes mod 840 (or the finest known modulus) that are NOT covered by explicit identities.

### Q3: Can we refine further?

Are there additional identities in the literature (or easily derivable) that reduce the uncovered set below 6 classes?

---

## Part 2: Analyze the Leftover Classes

### Q4: Structure of the hard classes

For each remaining class (e.g., p ≡ 1 mod 840):
- What is the structure of such primes?
- What makes Bradford fail for small x?
- Are there patterns in which x values work computationally?

### Q5: Density of the hard primes

Among primes up to X:
- What fraction are in the hard classes?
- How does this compare to the density needed for sieve methods?

### Q6: Special structure for p ≡ 1 (mod 24)?

The class p ≡ 1 (mod 24) seems to be the "core" hard case. What special properties do these primes have that we can exploit?

---

## Part 3: The Analytic Attack on Remaining Classes

### Q7: The bilinear sum to estimate

Write the precise sum whose positivity implies ES for the remaining classes:

```
S(p) = Σ_{x ∈ I_p} Σ_{e | x²} 1_{(4x-p) | (4e+1)}
```

or the character expansion version.

### Q8: What existing estimates apply?

For primes p in the hard classes:
- Can we get a lower bound on S(p) using existing divisor-in-AP technology?
- What's the "barrier" modulus size where current methods break down?

### Q9: The key bilinear/Kloosterman sums

Write out explicitly what exponential sums appear when you expand S(p) using characters. What would need to be bounded?

### Q10: Averaging over p?

If we can't get uniform-in-p estimates, can we average over p in a residue class?

I.e., prove: For p ≡ 1 (mod 840) with p ∈ [P, 2P], at least (1-ε) fraction have S(p) > 0?

This plus computation would give ES.

---

## Part 4: The Complete Proof Roadmap

### Q11: Theorem statement

State the theorem we're aiming for:

> **Theorem (Unconditional Effective ES):** For all primes p > p₀, the equation 4/p = 1/x + 1/y + 1/z has a solution in positive integers.

With explicit p₀.

### Q12: Proof structure

Outline the proof:
1. For p ≡ [covered classes] (mod 840): Use identity [X]
2. For p ≡ [hard classes] (mod 840) with p > p₁: Use [analytic lemma]
3. For p ≤ p₁: Computational verification

### Q13: What needs to be proven?

List the specific lemmas/estimates that need to be established:
- Lemma A: [statement]
- Lemma B: [statement]
- etc.

### Q14: What's the hardest part?

Which lemma is the main obstacle? Is it:
- A new equidistribution result?
- A Kloosterman sum bound?
- Something else?

### Q15: Is this achievable?

Honest assessment: Is this proof roadmap realistic with current technology + reasonable new work? Or does it require a breakthrough?

---

## Part 5: Explicit Computations for Small Cases

### Q16: For p = 2521 (smallest hard prime ≡ 1 mod 840)

- What is I_p = [p/4, p/2]?
- For which x does Bradford succeed?
- What divisor e works?

### Q17: Pattern in the working x values

For the first 100 primes p ≡ 1 (mod 840):
- Is there a pattern in which x values work?
- Do certain x (e.g., x with many small prime factors) always work?

---

## Desired Output

1. **Complete modular coverage table** (which identities cover which classes)
2. **Precise leftover set** (exact residue classes needing analytic treatment)
3. **The bilinear sum** to estimate, in explicit form
4. **Proof roadmap** with numbered steps
5. **List of required lemmas** with difficulty assessment
6. **Honest feasibility assessment**
