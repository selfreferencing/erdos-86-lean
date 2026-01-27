# GPT Prompt 19: Formalizing the 0-Child Loss Lemma

## Context

We're proving the 86 Conjecture (2^86 is the last zeroless power of 2) via a sieving approach. We've verified computationally that no n ∈ [87, 6643] is zeroless. To complete the proof, we need to either:
1. Get a Baker-Matveev upper bound (see Prompt 18), OR
2. **Formalize the 0-Child Loss Lemma** to prove decay rigorously

This prompt addresses option 2.

## The Setup

### Survivor Structure
- **S_k** = residue classes r mod T_k = 4·5^(k-1) such that 2^n has k zeroless trailing digits for n ≡ r (mod T_k)
- **|S_k|** = 4 × 4.5^(k-1) exactly (by the 4-or-5 Children Theorem)
- **Density** = |S_k|/T_k = 0.9^(k-1)

### The 4-or-5 Children Theorem (PROVEN)
Each level-k survivor has exactly 5 children at level k+1 (residues r, r+T_k, r+2T_k, r+3T_k, r+4T_k mod T_{k+1}).

Of these 5 children:
- Exactly 4 or 5 survive (never 3 or 6)
- The split is 50/50: half of survivors have 4 children, half have 5
- This gives P(survive k+1 | survive k) = 9/10 = 0.9 exactly

### The Zero-Child Question

**Definition**: Let A_k ⊆ S_k be the survivors whose "child-0" (the child with the same residue r, not r+jT_k for j>0) also survives at level k+1.

**Empirical Finding** (verified for k = 1 to 50):
```
|A_k| / |S_k| ≈ 0.9 for all k ≥ 6
```

More precisely:
- For k ≥ 6, the ratio |A_k|/|S_k| is in [0.89, 0.91]
- The ratio converges to 0.9 as k → ∞

### Why This Matters

If a zeroless n > 86 exists with D(n) = k digits, then:
1. n survives to level k (i.e., n mod T_k ∈ S_k)
2. n ≡ n (mod T_j) for all j ≤ k, so n's "child-0" path must survive at EVERY level

This means n must be in the intersection:
```
n ∈ ⋂_{j=1}^{k} A_j (lifted appropriately)
```

If |A_j|/|S_j| ≤ 0.9 for all j, then the density of this intersection decays like 0.9^k, which for large k and the constraint n < 3.32k (from Digit Squeeze), forces emptiness.

## The Request

### Question 1: Prove the 0-Child Loss Lemma

**Conjecture**: For all k ≥ k_0 (some explicit constant), we have |A_k|/|S_k| ≤ 0.9.

Can you prove this? The key ingredients are:
- The digit d_k = 0 iff u_{k+1}(n) < 5^k/2 where u_{k+1}(n) = 2^(n-k-1) mod 5^(k+1)
- Among survivors at level k, the distribution of u_{k+1}(n) is "close to uniform" over 5^(k+1) residues
- Uniformity implies 10% land in the zero interval, so 90% survive

### Question 2: Killed-Index Uniformity

We observed that among 4-child survivors (those that lose exactly 1 child), the "killed index" (which of children 0,1,2,3,4 dies) is uniformly distributed:
```
P(killed = j | 4-child survivor) ≈ 1/5 for each j ∈ {0,1,2,3,4}
```

This converges rapidly (by k ≈ 6). Can you prove this uniformity?

### Question 3: Forced-Tail Decay

Suppose |A_j|/|S_j| ≤ c for all j ≥ j_0, where c < 1. Define:
```
F_k = {r ∈ S_k : r's child-0 survives at all levels 1,2,...,k}
```

Then |F_k|/|S_k| ≤ c^k. Combined with the Digit Squeeze Lemma (zeroless n must have n < 3.32k for k = D(n)), show this forces F_k ∩ [2, 3.32k) = ∅ for sufficiently large k.

## What We Know

### Computational Verification
```
k=1:  |A_1|/|S_1| = 1.0000 (trivial: all 4 survive)
k=2:  |A_2|/|S_2| = 0.9444
k=3:  |A_3|/|S_3| = 0.9259
k=4:  |A_4|/|S_4| = 0.9136
k=5:  |A_5|/|S_5| = 0.9049
k=6:  |A_6|/|S_6| = 0.9016
k=10: |A_{10}|/|S_{10}| = 0.9002
k=20: |A_{20}|/|S_{20}| = 0.9000
```

The ratio approaches 0.9 from above.

### The 5-adic Mechanism

The digit d_k depends on:
```
d_k = ⌊2^n / 10^k⌋ mod 10
```

This is determined by 2^n mod 10^(k+1). The key insight:

- Level-k survival constrains n mod T_k = 4·5^(k-1)
- The k-th digit depends on n mod T_{k+1} = 4·5^k
- Given n mod T_k, there are 5 equally-spaced options for n mod T_{k+1}
- These 5 options cycle through 5 "sectors" of 5^(k+1)
- One sector lands in the zero interval (size 5^k/2), so 1 of 5 children dies

### Why Uniformity Emerges

The map n ↦ 2^n mod 5^k is periodic with period 4·5^(k-1). Within each coset of T_k in T_{k+1}, the 5 values 2^r, 2^(r+T_k), ..., 2^(r+4T_k) mod 5^(k+1) are spaced by a fixed multiplier 2^(T_k) mod 5^(k+1).

Since 2 is a primitive root mod 5^k for all k, this multiplier cycles through residues, creating pseudo-random distribution.

## Desired Output

1. **Rigorous proof** (or proof sketch) that |A_k|/|S_k| ≤ 0.9 for k ≥ k_0
2. **Explicit k_0** if possible
3. **Alternative**: A discrepancy bound showing survivors are equidistributed enough that |A_k ∩ [0,M]| ≈ 0.9 × |S_k ∩ [0,M]| for intervals [0,M]
4. **Combined with Digit Squeeze**: Conclude that for k ≥ 27, the interval [2, 3.32k) contains no forced-tail survivors, completing the 86 Conjecture proof

## References

- The 4-or-5 Children Theorem proof uses that 2 is primitive root mod 5^k
- Digit uniformity among survivors is empirically exact by k ≈ 7
- The "killed-index uniformity" at 20% each suggests deep equidistribution

## Appendix: Key Definitions

```
T_k = 4·5^(k-1)           (period for k trailing digits)
S_k = level-k survivors    (|S_k| = 4 × 4.5^(k-1))
A_k = {r ∈ S_k : child-0 of r survives at k+1}
u_k(n) = 2^(n-k) mod 5^k  (5-adic orbit)
d_k(n) = k-th digit of 2^n from right (0-indexed)
d_k = 0 ⟺ u_{k+1}(n) < 5^k/2
```
