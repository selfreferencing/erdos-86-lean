# APPROACH 52B: Carry Markov Model — Confirmation & Compact Summary

## Confirms 52A with Same Key Numbers

| Quantity | Value |
|----------|-------|
| Zero-producing state | (5, 0) ⟺ killing pair (≤4, 5) |
| Baseline p₀ | 4/81 ≈ 0.0494 |
| Empirical p₀ | 0.78 × 4/81 ≈ 0.0385 |
| Correlation decay | |λ₂| ≈ 0.227 |
| Effective independence | After ~3-5 digits |
| Spectral radius ρ | 8.5311 |
| Per-digit survival | ρ/9 = 0.9479 |

## Explicit Survival Formula

```
P(no zero in k digits) = e₀ · (A/9)^k · 1

Where A = [[4, 4],
           [4, 5]]

Asymptotically: ~ 0.9341 × (0.9479)^k
```

Concrete values:
- k = 26: P(survive) ≈ 0.2324
- k = 27: P(survive) ≈ 0.2203

## Bridge to Proof (More Explicit)

### 1. Bulk Zero Forcing = Killing Pair Forcing
- Zero in 2^(n+1) at position i ⟺ killing pair at (i-1, i) in 2^n
- Goal: show 2^n contains at least one killing pair

### 2. Markov Large Deviation Bound
```
P(no killing pair in m digits) ≤ exp(-c·m)
```
Where c > 0 determined by p₀ and spectral gap (1 - |λ₂|).

### 3. Sparse Mesh Principle
- Events Eᵢ = "killing pair at (i-1, i)"
- Choose mesh with spacing ≥ L (where L ≈ 10 for safety)
- Then: P(∩ Eᵢᶜ) ≈ (1 - const·p₀)^r

### 4. Baker's Role
- Avoiding killing pairs on sparse mesh forces 2^n into small residue set mod 10^M
- Baker bounds show no n can keep landing in these sets beyond threshold

## What Experiments Provide

| Finding | Proof Use |
|---------|-----------|
| Killing suppression 0.78 | More accurate p₀ (hazard density) |
| Correlation length ~4 | How to thin constraints |
| Protection advantage 1.078 | Refines survival decay |

## Offer

If given the actual 9×9 pair matrix from Exp 70 (not just ratios), can:
1. Build literal 18×18 transition matrix P
2. Compute exact π̃ and p₀ (no heuristics)
3. Extract |λ₂| for full model (not just high/low reduction)
