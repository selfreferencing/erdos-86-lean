# APPROACH 52A: Carry Markov Model — Complete Construction

## The 18-State Markov Chain

### State Space
(digit, carry) ∈ {1,...,9} × {0,1} = 18 states

### Carry-Out Function (Deterministic)
```
τ(a) = 0  if a ∈ {1,2,3,4}
τ(a) = 1  if a ∈ {5,6,7,8,9}
```
Carry-out depends ONLY on digit, not carry-in.

### Zero-Producing State
**Unique killing state**: (5, 0)
- Only (a, c) = (5, 0) produces output 0
- Because 2×5 + 0 = 10 → output 0

### Transition Kernel
```
P((a,c) → (a',c')) = 𝟙{c' = τ(a)} · p_{c'}(a')
```
Where p₀(d), p₁(d) are digit distributions given carry.

### Stationary Distribution
```
π(d, c) = q_c · p_c(d)
```
With carry masses:
```
q₁ = H₀ / (1 + H₀ - H₁)
q₀ = 1 - q₁
```

---

## Q2: Effective Zero Rate

### Result
```
p₀^eff = π(5,0) = q₀ · p₀(5) ≈ 0.0385
```

### Comparison
| Model | Zero Rate |
|-------|-----------|
| Naive (uniform digits) | 0.100 |
| Uniform zeroless (4/81) | 0.049 |
| **Exp-calibrated** | **0.039** |

The 22% killing pair suppression reduces zero rate from 0.049 to 0.039.

---

## Q3: Correlation Length

### Carry Chain Eigenvalue
```
λ₂ = H₁ - H₀ ≈ 0.313 - 0.54 ≈ -0.227
```

### Correlation Decay
```
Corr(cᵢ, cᵢ₊ₖ) ~ |λ₂|^k ≈ 0.227^k
```

### Correlation Length
```
ℓ ≈ 1/(-log|λ₂|) ≈ 0.67 digits
```

**Operational**: After 3-4 digits, correlation < 1%. "Effectively independent" beyond ~4 digit steps.

---

## Q4: Survival Probability

### Survival Transfer Matrix
```
M = [[1-H₀,  H₀-δ  ],
     [1-H₁,  H₁    ]]
```
Where δ = p₀(5) = death probability when carry = 0.

### Calibrated Matrix
```
M ≈ [[0.46,  0.4712],
     [0.687, 0.313 ]]
```

### Spectral Radius (Survival Decay)
| Model | λ = ρ(M) | S(26) |
|-------|----------|-------|
| Uniform | 0.9479 | 0.232 |
| **Calibrated** | **0.9602** | **0.339** |

The calibrated model increases per-digit survival by ~1.3 percentage points.

---

## Q5: Bridge to Proof

### 1. Bulk Zero Forcing (Spectral → Exponential Smallness)
- Zeroless survival: S(k) ~ C·λ^k with λ < 1
- "Zeroless in block of length k" = membership in regular language
- Residues mod 10^k that survive have density ≈ λ^k
- Prove 2^n mod 10^k can't stay in density-λ^k set for large k

### 2. Borel-Cantelli (Correlation Length → Quasi-Independence)
- Events Eᵢ = {position i in state (5,0)}
- P(Eᵢ) ≈ p₀^eff ≈ 0.039
- Covariances decay exponentially (mixing)
- Second-moment argument forces zeros in long blocks

### 3. Sparse Mesh (Maximize Baker Leverage)
- Dependence tiny after spacing ≥ 3 digits
- **Recommended mesh**: i = 0, 4, 8, 12, ... (every 4 positions)
- Each position is "almost independent" constraint on 2^n mod 10^(i+1)
- Conjunction of constraints has exponentially small satisfying set

### 4. The Proof Target
Combine:
1. Exponentially small density of satisfying residues (spectral)
2. Lower bound on how often 2^n hits those residues (Baker/discrepancy)
3. Show impossibility beyond explicit n threshold

---

## Explicit Digit Distributions (Calibrated)

| digit d | p₀(d) = P(d|c=0) | p₁(d) = P(d|c=1) |
|---------|------------------|------------------|
| 1-4 | 0.115 each | 0.1718 each |
| 5 | 0.0688 | 0.118 |
| 6-9 | 0.1178 each | 0.04868 each |

This respects:
- Killing mass π(5,0) ≈ 0.0385
- Protection advantage 1.078× → π(5,1) ≈ 0.0519

---

## Next Step Suggested

Use full Exp 70 pair matrix to fit a **9-state digit Markov chain** T(d→d') directly, then lift to 18-state (d,c) chain. This would:
- Reproduce (7,7), (9,9) suppressions explicitly
- Give data-driven λ₂ (not just carry proxy)
- Yield better λ = ρ(M) for proof
