# APPROACH 55: Shrinking Target Theorems for Digit Cylinders

## Context

We're proving the Erdős 86 Conjecture: **2^86 is the last power of 2 with no zero digit.**

APPROACH 53A/B identified that the core missing piece is a **shrinking-target theorem** that can handle targets with exponential complexity (unions of ~9^d intervals).

---

## The Setup

Let θ = log₁₀(2) ≈ 0.30103 (irrational, finite type, μ(θ) believed to be 2 but unknown).

The orbit is {nθ} mod 1 for n = 1, 2, 3, ...

Define target sets:
- S_d = {f ∈ [0,1) : the first d digits of 10^f are all nonzero}

Then 2^n is zeroless (in all d(n) = ⌊nθ⌋ + 1 digits) iff {nθ} ∈ S_{d(n)}.

We have:
- μ(S_d) ≈ (9/10)^d (exponentially small)
- S_d is a union of approximately 9^d intervals
- The intervals have width ~10^(-d) each

---

## What We Need

### The Ideal Theorem

**Theorem (Hypothetical):** Let θ have irrationality exponent μ(θ) < ∞. Let (S_n) be a sequence of measurable sets with:
1. Σ μ(S_n) < ∞
2. [Some regularity condition on S_n]

Then the orbit {nθ} enters S_n only finitely often.

### The Problem

Standard shrinking-target theorems (Kurzweil, Kim-Tseng, Haynes-Jensen-Kristensen) typically require:
- **Single ball targets** (or monotone nested balls)
- **Bounded complexity** (O(1) connected components)

Our S_d has:
- ~9^d connected components
- Non-nested structure
- Boundary complexity exponential in d

---

## Questions for Research

### Q1: What shrinking-target theorems exist for irrational rotations?

Please survey the known results:
- Kurzweil (1955)
- Kim-Tseng
- Haynes-Jensen-Kristensen
- Beresnevich-Velani
- Others?

For each, state:
- The target condition
- The Diophantine condition on θ
- Whether it applies to unions of intervals
- How complexity enters

### Q2: What about unions of intervals with controlled complexity?

Are there results for targets that are unions of N intervals, where N may grow but is controlled?

For example:
- N = O(poly(d)) intervals
- N = O(exp(αd)) for α < log(10)

### Q3: The Duffin-Schaeffer / Koukoulopoulos-Maynard connection

The recent proof of Duffin-Schaeffer conjecture handles:
- Infinitely many Diophantine approximations
- With general "approximation function" ψ(q)

Is there any connection to our digit cylinder targets?

### Q4: Discrepancy bounds for specific sets

Instead of Borel-Cantelli, could we use discrepancy?

If D_N is the discrepancy of {θ}, {2θ}, ..., {Nθ}, then:
```
|#{n ≤ N : {nθ} ∈ A} - N·μ(A)| ≤ D_N · (complexity of ∂A)
```

For our sets:
- μ(S_d) ≈ 0.9^d
- Complexity of ∂S_d ≈ 2·9^d

What does Koksma-Hlawka say? Does it blow up?

### Q5: What's known specifically for digit constraints?

Are there papers specifically about:
- "How often does nα have digit 0 in position k?"
- Digit distribution in fractional parts of nα
- Benford's law with constraints

### Q6: Effective vs. ineffective results

For our purpose (proving Erdős 86), we need an **effective** result that gives a finite N.

Are there ineffective results that at least prove finiteness? What's the obstruction to making them effective?

---

## Related Structures

### The Cantor-like Structure of S_d

S_d has a Cantor-set-like structure:
- At scale 10^(-1): remove 1/10 (digit 1 = 0)
- At scale 10^(-2): remove 1/10 of each remaining (digit 2 = 0)
- ...
- At scale 10^(-d): final refinement

This is NOT a standard Cantor set (measure 0) because we stop at finite d.

### Connection to β-expansions

The problem resembles questions about digit expansions in non-integer bases. Is there relevant literature on "forbidden digits" in β-expansions?

### Dynamical Systems Perspective

The map T: x → 10x mod 1 generates decimal digits. Our constraint is "orbit of 10^{nθ} under T avoids 0 for d steps."

Is there literature on symbolic dynamics / forbidden words that applies?

---

## What Would Make Progress

Even partial results would be valuable:

1. **Density zero result:** "The set of n with 2^n zeroless has natural density 0" — this is trivial from digit counting, but formalizing it in the shrinking-target framework would be a start.

2. **Logarithmic density:** "The set of n with 2^n zeroless has logarithmic density 0" — stronger than natural density.

3. **Almost-all θ result:** "For almost all θ with μ(θ) = 2, the orbit has zeros eventually" — follows from BC + mixing, but our θ is specific.

4. **Effective bound for specific θ:** "For θ = log₁₀(2), there exists N such that for all n > N, 2^n has a zero" — this is the goal.

---

## Request

Please provide:

1. A survey of relevant shrinking-target / Borel-Cantelli theorems for rotations
2. Assessment of which (if any) could handle our exponential-complexity targets
3. Identification of the key obstruction
4. Suggestions for weaker results that ARE provable
5. Any relevant papers or names to search for
