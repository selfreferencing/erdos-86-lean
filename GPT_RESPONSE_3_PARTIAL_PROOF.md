# GPT Response 3: Partial Proof and Exact Gap

## The Rigorous Partial Result

### Proposition (k=0 Classification - COMPLETE)

Let p ≡ 1 (mod 4) be prime. Then:

**Type II succeeds at k=0 iff p ≡ 5 (mod 12)**

**Proof**:
- k=0 gives m₀ = 3, x₀ = (p+3)/4
- Need coprime divisors (a,b) of x₀ with a + b ≡ 0 (mod 3)
- By Lemma 2, need gcd(x₀, 3) = 1
- For sum ≡ 0 (mod 3), need residues (1,2) mod 3
- So x₀ = ab ≡ 1·2 ≡ 2 (mod 3) is necessary
- It's sufficient: pair (1, x₀) has sum 1 + x₀ ≡ 0 (mod 3) when x₀ ≡ 2 (mod 3)
- x₀ ≡ 2 (mod 3) means (p+3)/4 ≡ 2 (mod 3), i.e., p ≡ 5 (mod 12) ∎

**Consequence**: Half of all primes p ≡ 1 (mod 4) succeed immediately at k=0!

| Primes p ≡ 1 (mod 4) | k=0 status |
|---------------------|------------|
| p ≡ 5 (mod 12) | ✓ Always works |
| p ≡ 1 (mod 12) | ✗ Never works |

---

## Three Key Lemmas (Constraints)

### Lemma 1: Finite Search Range
If k is good, then k ≤ (p-5)/12.

**Proof**: a + b ≤ x_k + 1, so m_k ≤ x_k + 1. Rearranging gives the bound. ∎

### Lemma 2: Coprimality Constraint
If k is good, then gcd(x_k, m_k) = 1.

**Proof**: If prime q | m_k and q | a, then since m_k | (a+b), we have q | b, contradicting gcd(a,b) = 1. ∎

### Lemma 3: Quadratic Congruence Form
Assume gcd(x_k, m_k) = 1. Then k is good iff there exists divisor a | x_k with gcd(a, x_k/a) = 1 and:
```
a² ≡ -x_k (mod m_k)
```

**Connection**: This is exactly Bradford's Type II condition with d = a².

---

## The Exact Gap (Character Sum Form)

Define:
- C(n) = #{a | n : gcd(a, n/a) = 1} = 2^ω(n)
- G(n, m) = #{a | n : gcd(a, n/a) = 1, a + n/a ≡ 0 (mod m)}

Using additive characters:
```
G(n,m) = (1/m) Σ_{r=0}^{m-1} S_r(n,m)
```

where:
```
S_r(n,m) = Σ_{a|n, gcd(a,n/a)=1} exp(2πir(a + n/a)/m)
```

The r=0 term gives S₀ = C(n) = 2^ω(n), so:
```
G(n,m) = 2^ω(n)/m + (1/m) Σ_{r=1}^{m-1} S_r(n,m)
```

### The Exact Missing Theorem

> There exists absolute δ > 0 such that for every prime p ≡ 1 (mod 4):
> ```
> Σ_{k=0}^{K} (1/m_k) Σ_{r=1}^{m_k-1} |S_r(x_k, m_k)| ≤ (1-δ) Σ_{k=0}^{K} 2^ω(x_k)/m_k
> ```
> This would imply Σ G(x_k, m_k) > 0, so at least one k is good.

**This is a uniform discrepancy bound for a divisor-restricted Kloosterman family.**

---

## Novel Reformulation: Subset-Product Hitting

By Lemma 3, we need a² ≡ -x_k (mod m_k).

This becomes: "Do the subset-products (divisors) of x_k generate enough of (Z/m_k Z)* to hit a prescribed quadratic residue target?"

This is **multiplicative combinatorics** in finite groups, related to:
- Erdős-Odlyzko-Sárközy problems
- Munsch-Shparlinski subset-product results

---

## Most Promising Approach

### Not Pointwise Bounds (Pólya-Vinogradov, Burgess)
These are for intervals or complete character sums, not divisor sets.

### Yes: DFI/BFI Bilinear Kloosterman Methods
- Duke-Friedlander-Iwaniec bilinear forms with Kloosterman fractions
- Fouvry-Iwaniec-Katz divisor function in APs
- Blomer's Kloosterman sums in residue classes

The specific need: an **averaged** cancellation estimate for S_r(x_k, m_k) as k ranges, strong enough to beat the main term.

---

## Key Literature

### ESC Reductions
- Bradford (2025): Type II divisor condition
- Salez (2014): Modular equations, verification to 10^17
- Mihnea-Dumitru (2025): Verification to 10^18

### Kloosterman/Divisor Technology
- Fouvry-Iwaniec-Katz (1992): Divisor function in APs via Weil bounds
- Duke-Friedlander-Iwaniec (1997): Bilinear Kloosterman fractions
- Blomer (2015): Kloosterman sums in residue classes
- Katz: Monodromy methods for Kloosterman

### Subset-Product Representation
- Friedlander (2007): Products in residue classes
- Martin (2022): Subproducts of small residue classes

---

## Summary

| What | Status |
|------|--------|
| k=0 works iff p ≡ 5 (mod 12) | ✓ PROVEN |
| Finite k range | ✓ PROVEN |
| Coprimality constraint | ✓ PROVEN |
| Quadratic form connection | ✓ PROVEN |
| Full "Type II always works" | Requires Kloosterman discrepancy bound |
