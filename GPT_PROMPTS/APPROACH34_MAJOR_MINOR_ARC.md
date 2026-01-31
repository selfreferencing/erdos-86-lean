# APPROACH 34: Explicit Major/Minor Arc Decomposition for Digit Targets

## Context

We are working on the Erdős 86 Conjecture: the last zeroless power of 2 is 2^86.

Previous responses (31B, 31C) identified the Fourier approach as the **most viable path**:

> "Q4 (Fourier coefficients) is the most viable analytic route to pointwise control at a specific θ₀."

The key identity is:
```
R_m(x) = Σ_{k≠0} ĉ_{F_m}(k) · S_{L_m}(k·θ₀) · e^{2πikx}
```
where:
- ĉ_{F_m}(k) = Fourier coefficient of 1_{F_m} (the zeroless indicator)
- S_N(α) = Σ_{n=0}^{N-1} e^{2πinα} (geometric sum)
- θ₀ = log₁₀(2)

Both 31B and 31C recommended a **major/minor arc decomposition**:

> "Implement a major/minor arc decomposition in frequency k:
> - Minor arcs: where |k·θ₀| is not too small, so S_{L_m}(k·θ₀) is controlled
> - Major arcs: sparse k (near convergent denominators) where S_{L_m} might be large; show ĉ_{F_m}(k) is tiny there"

31B explicitly offered:
> "If you want, I can also sketch an explicit 'major/minor arc' decomposition for the Fourier sum for R_m(m·θ₀) that makes the needed missing-digit Fourier estimate completely explicit."

This prompt requests that explicit sketch.

## The Setup

### The Discrepancy Function
```
R_m(x) = #{0 ≤ n < L_m : {n·θ + x} ∈ F_m} - L_m · μ(F_m)
```
where:
- L_m ≈ 3.32m (orbit length at scale m)
- F_m = {x ∈ [0,1) : first m digits of 10^x are zeroless}
- μ(F_m) = (9/10)^m

### The Goal
Prove |R_m(0)| < 1/2 for all m ≥ M₀, for some explicit M₀.

This would give: for m ≥ M₀, the number of hits N_m satisfies:
```
|N_m - L_m · μ(F_m)| < 1/2
```
Since L_m · μ(F_m) → 0, this forces N_m = 0 for large m.

### The Fourier Expansion
```
R_m(0) = Σ_{k≠0} ĉ_{F_m}(k) · S_{L_m}(k·θ₀)
```

### The Geometric Sum Bound
```
|S_N(α)| ≤ min(N, 1/(2||α||))
```
where ||α|| = min(|α - n| : n ∈ Z) is the distance to the nearest integer.

## Questions

### Q1: Define the Major/Minor Arc Split

For a parameter Q (to be chosen), define:
- **Major arcs M_Q:** Those k where ||k·θ₀|| < 1/Q
- **Minor arcs m_Q:** Those k where ||k·θ₀|| ≥ 1/Q

What is the right choice of Q as a function of m and L_m?

### Q2: Minor Arc Contribution

On the minor arcs, |S_{L_m}(k·θ₀)| ≤ Q/2.

So the minor arc contribution is:
```
|Σ_{k ∈ m_Q} ĉ_{F_m}(k) · S_{L_m}(k·θ₀)| ≤ (Q/2) · Σ_{k ∈ m_Q} |ĉ_{F_m}(k)|
```

**What bound on Σ|ĉ_{F_m}(k)| is needed to make this < 1/4?**

If we need Σ|ĉ_{F_m}(k)| ≤ ρ^m for some ρ < 1, what value of ρ suffices?

### Q3: Major Arc Structure

The major arcs are where ||k·θ₀|| < 1/Q.

By the theory of continued fractions, these k are "close to" multiples of convergent denominators q_n of θ₀.

For θ₀ = log₁₀(2) = [0; 3, 3, 9, 2, 2, 4, 6, 2, 1, 1, 3, 1, 18, ...]:
- q_0 = 1
- q_1 = 3
- q_2 = 10
- q_3 = 93
- q_4 = 196
- q_5 = 485
- q_6 = 2136
- q_7 = 13301
- ...

**How many k ∈ [1, K] lie in the major arcs M_Q?**

### Q4: Major Arc Contribution

On major arcs, |S_{L_m}(k·θ₀)| can be as large as L_m.

So we need |ĉ_{F_m}(k)| to be very small on major arcs to compensate.

**What bound on |ĉ_{F_m}(k)| for k ∈ M_Q is needed?**

If |ĉ_{F_m}(k)| ≤ C · ρ^m · |k|^{-1-η} for some ρ < 1, η > 0, is that sufficient?

### Q5: The Fourier Coefficients of 1_{F_m}

The set F_m is a union of ~9^m intervals in [0,1), corresponding to all zeroless m-digit prefixes.

**What is known about the Fourier coefficients ĉ_{F_m}(k)?**

Generic estimates (bounded variation) give |ĉ_{F_m}(k)| ≤ Var(1_{F_m})/|k| ~ 9^m/|k|, which is useless.

But 31B cited Maynard's work:
> "Missing-digit sets have a 'convenient explicit analytic description' of their Fourier transform and it is 'often unusually small.'"

**Can you provide the explicit Fourier structure for digit-restriction sets?**

### Q6: The Digit-Set Fourier Transform

For the set D_m = {integers with no digit 0 in first m positions}, there should be a product formula:
```
ĉ_{D_m}(k) = Π_{j=0}^{m-1} f_j(k)
```
where f_j involves sums over allowed digits {1,...,9}.

**Derive this product formula explicitly.**

### Q7: Base-10 Resonances

The Fourier coefficients of digit-restriction sets have special structure at frequencies related to powers of 10.

**What happens to |ĉ_{F_m}(k)| when k is a multiple of 10^j for some j?**

Are these "base-10 resonances" the analog of major arcs in the digit structure?

### Q8: The Two-Resonance Picture

31C suggested a "two-mechanism" major/minor arc decomposition:
> "One major arc coming from rotation near-resonance (continued fractions), and one coming from digit/carry near-resonance (powers of 10 structure)."

**Describe how these two types of resonances interact.**

Is there a 2D decomposition:
- k near CF denominators AND k near powers of 10 → double major arc?
- k near CF denominators but NOT near powers of 10 → ?
- k NOT near CF denominators but near powers of 10 → ?
- k far from both → double minor arc?

### Q9: Explicit Bound for M₀

Putting it all together:

Given explicit bounds on:
- The Fourier coefficients |ĉ_{F_m}(k)|
- The geometry of major arcs (how many k, how large S_{L_m})
- The continued fraction of θ₀

**What is the explicit value of M₀ such that |R_m(0)| < 1/2 for m ≥ M₀?**

Our computational data suggests M₀ ≈ 50 (where |R_m(m·θ₀)| becomes < 1).

### Q10: The Pre-Asymptotic Band

For m < M₀, we need a different argument.

The "danger cylinder" approach (APPROACH 32) showed:
- For m ≤ 35, there ARE hits (the 35 zeroless powers)
- For 36 ≤ m ≤ 49, no hits but the analytic bound is not yet strong enough

**How do we handle the band m ∈ [36, M₀)?**

Options:
1. Certified computation
2. Sharper Fourier estimates specific to this range
3. Danger cylinder enumeration + Baker

### Q11: Comparison to Maynard's Approach

James Maynard proved results about primes with restricted digits using:
- A Markov model for digit correlations
- Moment estimates via comparison to the model
- Major/minor arc decomposition in Fourier space

**How closely does our problem parallel Maynard's?**

Key differences:
- Maynard: primes (multiplicative structure)
- Us: powers of 2 (additive/exponential structure)
- Maynard: general missing digit
- Us: specifically missing 0 (affects carries differently)

### Q12: The Spectral Gap Connection

APPROACH 31 discussed the carry automaton having a spectral gap, which would imply correlation decay, which would imply Fourier decay.

**How does the spectral gap of the carry automaton translate to bounds on |ĉ_{F_m}(k)|?**

Is there a direct formula:
```
|ĉ_{F_m}(k)| ≤ C · λ^m
```
where λ is the spectral gap parameter?

## Desired Output

1. **Explicit major/minor arc decomposition** for R_m(0)
2. **Required Fourier bounds** on |ĉ_{F_m}(k)| (both sum and pointwise)
3. **Analysis of major arc structure** using CF of θ₀
4. **Product formula** for digit-set Fourier coefficients
5. **Explicit estimate of M₀** (or bounds on it)
6. **Strategy for pre-asymptotic band** m ∈ [36, M₀)
7. **Assessment:** Is this approach viable for proving Erdős 86?

## Data Available

### Continued Fraction of θ₀ = log₁₀(2)
```
θ₀ = [0; 3, 3, 9, 2, 2, 4, 6, 2, 1, 1, 3, 1, 18, 1, 6, 1, 2, 9, 117, ...]
```

### Convergent Denominators
```
q_n: 1, 3, 10, 93, 196, 485, 2136, 13301, 28738, 42039, ...
```

### Computational Observations
- N_m = 0 for m ≥ 36 (verified to m = 100)
- |R_m(m·θ₀)| < 1 for m ≥ 50 (approximately)
- The 35 zeroless powers all have n ≤ 86

### The 35 Zeroless Powers
```
n = 1, 2, 3, 4, 5, 6, 7, 8, 9, 13, 14, 15, 16, 18, 19, 24, 25, 27, 28,
    31, 32, 33, 34, 35, 36, 37, 39, 49, 51, 67, 72, 76, 77, 81, 86
```

## References

- Maynard, J. "Primes with restricted digits"
- Erdős-Turán inequality for exponential sums
- Denjoy-Koksma inequality
- Theory of continued fractions and Diophantine approximation
