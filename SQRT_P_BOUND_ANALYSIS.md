# Analysis of d = O(√p) Bound for Type II Witnesses

## Date: January 21, 2025

## Setup

For p ≡ 1 (mod 4), write p = 4n + 1, so n = (p-1)/4.

For each admissible k ∈ K_COMPLETE:
```
m = m_k = 4k + 3
x = x_k = (p + m)/4 = n + k + 1
```

The x_k are literally "n plus a small offset".

---

## 1. Trivial O(p) Bound via Pairing Trick

**Lemma (Pairing Trick)**: If d | x², gcd(x,m) = 1, and d ≡ -x (mod m), then d' := x²/d is also a solution with d' ≡ -x (mod m).

**Proof**: Since gcd(x,m) = 1 and d | x², also gcd(d,m) = 1. Then:
```
d' ≡ x² · d⁻¹ ≡ x² · (-x)⁻¹ ≡ -x (mod m)
```

**Corollary**: Every solution comes in a pair (d, x²/d), so the smaller one is ≤ x. Hence:
```
d_min(x,m) ≤ x = (p+m)/4 ~ p/4
```

**Unconditional bound**: d = O(p)

---

## 2. Route to O(√p): Large Divisor in Residue Class

**Lemma (Large Divisor → Small Witness)**: If there exists u | x such that u ≡ -1 (mod m), then d := x/u is a Type II witness.

**Proof**: Since u | x, we have d | x | x². Modulo m:
```
d ≡ x · u⁻¹ ≡ x · (-1)⁻¹ ≡ -x (mod m)
```

**Corollary (Square-Root Consequence)**: If in addition u ≥ √x, then:
```
d = x/u ≤ √x ~ √p/2
```

**Key Insight**:
> Proving d = O(√p) reduces to proving that for some admissible (x,m) you can find a divisor u | x with u ≡ -1 (mod m) and u ≥ √x.

This is a "divisors in arithmetic progressions" / "divisor equidistribution mod m" problem.

---

## 3. Why √p is the Natural Worst-Case Scale

### Toy Obstruction

If x is a balanced semiprime (x = qr with q ≈ r ≈ √x):
- The smallest nontrivial divisors of x² are ≈ √x (namely q and r)
- If the residue constraint forces d ≠ 1, the smallest acceptable d is ≳ √x

### Conclusion

> If you want a worst-case deterministic upper bound, √p is a very plausible right order of magnitude, and improving it uniformly might be impossible without extra structure.

---

## 4. The "Drop-and-Square" Picture

Write the squarefree part of x as x = ∏ q_i. Any divisor of x² can be encoded by choosing exponents e_i ∈ {0, 1, 2}.

Relative to x (exponent 1 at each q_i), the adjustment exponents t_i = e_i - 1 live in {-1, 0, 1}:

| t_i | Effect |
|-----|--------|
| -1 | **Drop** q_i (remove from d) |
| 0 | Keep q_i once |
| +1 | **Square** q_i (multiply by extra copy) |

Then:
```
d = x · (∏_{t_i=+1} q_i) / (∏_{t_i=-1} q_i)
```

### To Make d Small

- **Drop** a product of primes that is **large** (ideally ≳ √x)
- Only **square** primes that are **small**

### Your Hardest Example

p = 76,719,889, x = 2 × 3 × 17 × 43 × 4373, d = 3 × 17² × 43 = 37,281

- **Dropped**: 2 and 4373 (big reduction: 2 × 4373 = 8746)
- **Squared**: 17 (moderate cost: extra factor of 17)
- Result: d ≈ 4.26 × √p

This mechanism naturally produces d on the √x scale: you drop "about half the log-mass" of x.

---

## 5. Three Conjectures

### Conjecture 1: Worst-Case Square-Root Law

There exists an absolute constant C such that for every prime p ≡ 1 (mod 4), there is an admissible k ∈ K_COMPLETE and a Type II witness d with:
```
d ≤ C√p
```

**Evidence**: Your data shows d/√p maxima ≈ 4.3, suggesting C might be single-digit.

### Conjecture 2: Square-Root with Polylog Safety Factor (Publishable)

A more conservative version:
```
d ≪ √p (log p)^A
```
for some fixed A, uniformly in p ≡ 1 (mod 4).

### Conjecture 3: Typical-Case is Much Smaller

For "almost all" primes p:
```
d ≤ (log p)^B
```
for some constant B.

The √p behavior only appears in rare extreme alignments (few useful prime factors and/or unlucky residue constraints).

---

## 6. Proof Strategy Requirements

To prove d ≪ √p, you need:

1. **Multiplicative structure**: For each p, at least one admissible x_k = n + k + 1 has "enough" multiplicative structure (not prime/near-prime), so x_k² has many divisors.

2. **Residue equidistribution**: Among divisors of x_k² in size range d ≤ C√p, residues mod m_k are not too biased, so class -x_k is hit.

This is where the "character sum / subgroup" perspective enters naturally.

---

## 7. Summary

| Bound Type | Result | Method |
|------------|--------|--------|
| Unconditional | d = O(p) | Pairing trick |
| Conditional | d = O(√p) | Large divisor u ≡ -1 (mod m) |
| Conjectured | d ≤ C√p | Empirical, C ≈ 4-5 |
| Typical case | d = O((log p)^B) | Most primes have small witnesses |

The √p scale emerges because the smallest feasible divisor in a constrained residue class is controlled by the existence of a divisor near √x.

---

## 8. Connection to Empirical Data

| p | d | d/√p | Mechanism |
|---|---|------|-----------|
| 2,521 | 8 | 0.16 | Easy case |
| 76,719,889 | 37,281 | 4.26 | Drop 2×4373, square 17 |
| 72,077,041 | 16,129 | 1.90 | Moderate difficulty |

The hardest cases occur when x_k has few small prime factors and no small combination hits the required residue.

---

## 9. Balanced Divisor Pair Reformulation (GPT Response B)

### The Key Algebraic Insight

Assume gcd(x,m) = 1. If d | x², set:
- g = gcd(d, x)
- a = d/g
- b = x/g

Then a | x, b | x, gcd(a,b) = 1, and **d = xa/b**.

The congruence d ≡ -x (mod m) becomes:
```
xa/b ≡ -x (mod m)
```

Cancel x (since gcd(x,m) = 1) and cancel b (since b | x implies gcd(b,m) = 1):

> **a ≡ -b (mod m)**

### Lemma (Witness ⟺ Opposite-Residue Divisor Pair)

For gcd(x,m) = 1, the condition d | x², d ≡ -x (mod m) is equivalent to finding **coprime divisors a, b | x** such that **a ≡ -b (mod m)**, with witness **d = xa/b**.

---

## 10. Explicit O(√p) Criterion

From d = xa/b:
```
d ≤ a√x  whenever  b ≥ √x
```

Since x ~ p/4, we have √x ~ √p/2, so d ≤ a√x ≈ a·√p.

### Sufficient Condition for O(√p)

> Find divisors a, b | x with:
> - a ≡ -b (mod m)
> - b ≥ √x
> - a ≤ A (constant)
>
> Then d ≤ A√x ≪ √p

---

## 11. Verification: Your Hardest Example

**p = 76,719,889, k = 5, m = 23**

x = 19,179,978 = 2 × 3 × 17 × 43 × 4373

Minimal witness: d = 3 × 17² × 43 = 37,281

**Best divisor pair**:
- a = 17
- b = 8746 = 2 × 4373

**Check**: a + b = 17 + 8746 = 8763 = 23 × 381 ≡ 0 (mod 23)

So a ≡ -b (mod 23). ✓

**Witness calculation**:
```
d = xa/b = (19,179,978 × 17) / 8746 = 37,281 ✓
```

**Why √p scale**: b = 8746 ≈ 2√x, while a = 17 is small. This forces d to be a constant multiple of √p.

---

## 12. Target Lemma for Proof

> **Target Lemma (Sufficient for O(√p))**
>
> For some fixed A and each prime p ≡ 1 (mod 4), there exists k ∈ K_COMPLETE such that for x = x_k, m = m_k, there are coprime divisors a, b | x with:
> - a ≤ A
> - a ≡ -b (mod m)
> - b ≥ √x
>
> Then d = xa/b ≤ A√x ≪ √p.

**Weaker target**: a ≤ (log p)^B gives d ≪ √p (log p)^B.

---

## 13. Three Proof Approaches

### (i) Divisors in Residue Classes (Analytic)

Show that for "most" x, every invertible residue class r (mod m) in the attainable subgroup has a representative divisor b | x with b ∈ [x^{1/2-δ}, x^{1/2+δ}].

Then take r ≡ -a for small divisor a to get d ≪ √x · x^δ = p^{1/2+ε}.

### (ii) Smoothness / Many-Divisors Heuristic

If x_k is reasonably smooth, it has many divisors, hence many residue values mod m_k.

Model: divisors b | x in range [√x, x] behave like random elements of subgroup H ⊆ (ℤ/m)*. Expected matches for fixed small a:
```
#{b | x : b ≥ √x} / |H|
```

Since |H| ≤ φ(m) ≤ 166, you don't need astronomically many divisors.

**Hard cases**: x_k has few prime factors → few divisors → must accept larger a.

### (iii) Character-Sum / Random-Walk View

Treat residues of prime factors as random walk on (ℤ/m)*. Use character sums to show mixing/equidistribution. Combine with balancing argument on log-sizes to ensure b ≥ √x.

**Hard cases**: Few primes → poor mixing → longer/less balanced representations → larger d.

---

## 14. Research-Level Summary

- **Unconditional O(√p) proof**: Genuinely difficult without serious results on divisors in arithmetic progressions
- **Clear structural reason**: After (a,b)-reformulation, witness size is √x × small factor a
- **Reasonable conjecture**: D_max(p) ≪ √p (log p)^B, perhaps even D_max(p) ≪ √p with absolute constant
- **Hard cases**: For every small a | x_k, the large divisors b | x_k miss residue class -a (mod m_k)
