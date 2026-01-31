# APPROACH 39: Carry Automaton Spectral Gap

## Context

We are working on the Erdős 86 Conjecture. The Target Lemma requires proving:
```
|ĉ_{F_m}(k)| ≤ C · ρ^m  with ρ < 0.84
```

The product formula suggests a transfer matrix approach. This prompt explores the spectral gap of the carry automaton as the engine for proving the Target Lemma.

## The Product Formula Revisited

From 34A/34B:
```
ĉ_{F_m}(k) = prefactor(k,m) · Π_{j=1}^m f_j(k)
```

The factors f_j(k) = Σ_{d=1}^9 e^{2πikd/10^j} can be viewed as matrix entries in a transfer matrix formulation.

## The Transfer Matrix

### Basic Setup

Consider the 9 × 9 matrix T_k(s) defined for s ∈ [0,1) by:
```
[T_k(s)]_{a,b} = e^{2πik(a + s·b)/10} for a,b ∈ {1,...,9}
```

This matrix propagates the Fourier phase from one digit position to the next.

### Connection to Fourier Coefficients

The product Π_{j=1}^m f_j(k) can be written as:
```
Π_{j=1}^m f_j(k) = 1^T · T_k(0.1) · T_k(0.01) · ... · T_k(10^{-m+1}) · 1
```
where 1 = (1,1,...,1)^T is the all-ones vector.

### The Spectral Radius

Define ρ(T_k) = spectral radius of T_k(s) (for generic s).

**Key Claim:** If ρ(T_k) < 9 uniformly for k not in the digit-major arcs, then the Target Lemma follows.

## Questions

### Q1: Compute T_k(s) Explicitly

For k = 1, 2, 3 and s = 0.1, 0.01, compute the 9 × 9 matrix T_k(s) explicitly.

What are its eigenvalues?

### Q2: Spectral Radius as Function of k

For s = 0.1 fixed, compute ρ(T_k(s)) for k = 1, 2, ..., 100.

Present as a table or plot. What is max_k ρ(T_k(0.1))?

### Q3: The Eigenvalue Structure

For T_k(s) with generic k and s:
1. What is the largest eigenvalue?
2. Is there an eigenvalue gap (second largest << largest)?
3. Does the matrix have special structure (e.g., circulant, Toeplitz)?

### Q4: The Spectral Gap Statement

**Desired Lemma:** For k not divisible by 10 and s ∈ [0.001, 0.1]:
```
||T_k(s)|| ≤ λ_0 < 9
```
for some explicit λ_0.

Can you prove this? What is λ_0?

### Q5: Product of Matrices

The Fourier coefficient involves a product of DIFFERENT matrices T_k(s_j) for s_j = 10^{-j}.

Even if each matrix has spectral radius 9, the PRODUCT might contract due to misalignment of eigenspaces.

**Question:** Is there a theorem about products of matrices with spectral radius ρ giving a product with spectral radius < ρ^n?

### Q6: The Carry Automaton Formulation

Alternative approach: model the digit sequence as a finite automaton with carry states.

When computing the Fourier transform of digit-restricted numbers, carries between positions introduce dependencies.

**Setup:**
- States: (carry, current_digit) ∈ {0,1} × {1,...,9}
- Transitions: determined by doubling with carry

**Question:** What is the transfer matrix for this automaton? Does it have a spectral gap?

### Q7: Connection to Maynard's Spectral Gap

Maynard's paper (arXiv:1604.01041) proves a spectral gap for digit correlations via a Markov model.

**Question:** Can you summarize Maynard's spectral gap theorem and adapt it to our setting?

### Q8: Explicit Computation Strategy

If the spectral gap is true but hard to prove analytically, can we verify it computationally?

**Approach:**
1. For each k ∈ [1, 1000], compute the product Π_{j=1}^{50} T_k(10^{-j})
2. Measure the operator norm of this product
3. Check if it's ≤ C · 0.8^{50} for some constant C

**Question:** Design and describe this computation.

### Q9: What If No Spectral Gap?

If the transfer matrix has spectral radius exactly 9 (no gap), what alternatives exist?

Options:
1. **Phase cancellation:** Even without spectral gap, the eigenvector directions might not align
2. **Averaged bound:** Spectral gap in an averaged sense
3. **Restricted k:** Spectral gap only for k satisfying additional conditions

**Question:** Which alternative is most viable?

### Q10: The Minimal Spectral Gap Needed

From the major/minor arc analysis, we need ρ < 0.84.

Since the spectral radius of the "independent digits" model is 9, we need:
```
(spectral radius) / 9 < 0.84
⟺ spectral radius < 7.56
```

**Question:** Is this achievable? Is 7.56 a reasonable target?

## The Ideal Theorem

**Ideal Spectral Gap Theorem:**

For all k with v₁₀(k) ≤ γm and all j ≥ v₁₀(k) + 1:
```
||T_k(10^{-j})|| ≤ λ_0 < 9
```

with λ_0 ≤ 7.5 (so that λ_0/9 ≤ 0.833 < 0.84).

This would immediately give the Target Lemma.

**Question:** Can you prove this theorem, or identify what's missing?

## Desired Output

1. **Explicit matrices** T_k(s) for small k and s
2. **Eigenvalue analysis** of these matrices
3. **Spectral radius bounds** (computational or analytical)
4. **Proof of spectral gap** if possible
5. **If blocked:** identify the obstruction and alternatives

## References

- Maynard, J. "Primes with restricted digits" (arXiv:1604.01041) - spectral gap methods
- Standard references on transfer matrix methods in combinatorics
