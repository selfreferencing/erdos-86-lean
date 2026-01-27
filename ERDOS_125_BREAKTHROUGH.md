# Erdős #125: Corrected Analysis

## Critical Correction (January 25, 2026)

**The original analysis below aimed at the wrong target.**

Initial goal: Prove d(C') = 0, hence d(A+B) = 1
Correct goal: Prove d(A+B) > 0 (positive lower density)

**Why density 1 is impossible:** Hasler-Melfi (2024) proved d̲(A+B) ≤ 0.696. The complement has positive density and doesn't vanish.

---

## Problem Statement

Let:
- A = {n : n has only digits 0,1 in base 3} = sums of distinct powers of 3
- B = {n : n has only digits 0,1 in base 4} = sums of distinct powers of 4 (Moser-de Bruijn)

**Question:** Does A + B have positive asymptotic density?

**Known bounds:**
- Lower: |A+B ∩ [1,x]| ≥ c·x^0.9777 (Hasler-Melfi)
- Upper on lower density: d̲(A+B) ≤ 0.696 (Hasler-Melfi)

---

## Computational Observations (Still Valid)

### Complement Clusters at Powers

The complement C' = ℕ \ (A+B) clusters near powers of 3 and 4.

| Power | Value | Run ending at Power-1 | Spike size |
|-------|-------|----------------------|------------|
| 3⁵ | 243 | 207-242 | 36 |
| 4⁷ | 16384 | 15303-16383 | 1081 |
| 3¹⁰ | 59049 | 57049-59048 | 2000 |

### Why This Happens

Numbers just below 3^k have base-3 representation **222...2xyz** (many 2s).
Numbers just below 4^k have base-4 representation **333...3xyz** (many 3s).

These are maximally far from {0,1}-digit representations, making decomposition n = a + b difficult.

### Spike Scaling

Spike size ~ Power^α where α ≈ 0.69

| Power | Spike size | log(Spike)/log(Power) |
|-------|------------|----------------------|
| 243 | 36 | 0.652 |
| 16384 | 1081 | 0.720 |
| 59049 | 2000 | 0.692 |

**However:** This scaling does NOT imply d(C') = 0. The spikes regenerate and the complement maintains positive density.

---

## Corrected Proof Strategy

### Goal: Show d̲(A+B) > 0

This requires showing the complement doesn't dominate, not that it vanishes.

### Primary Approach: Automaton + Transfer Operator (per GPT 5.2 Pro)

1. **Cycle Decomposition**: Group powers into "cycles" with bounded shapes (Melfi's approach)

2. **Finite State Machine**: Define frontier pattern F_n
   - State set S is finite (evidenced by run-length alphabet {2, 14, 22, 23, 36, ...})
   - Transition: F_{n+1} = T(F_n) is deterministic

3. **Transfer Operator**: Linear recursion v_{n+1} = M · v_n on state frequencies

4. **Perron-Frobenius**: Show recurrent "good states" have positive asymptotic frequency

5. **Density Extraction**: Good states contribute positive fraction to A+B

### Key Lemmas Required

| Lemma | Statement |
|-------|-----------|
| L1 | Cycle decomposition has uniformly bounded types |
| L2 | Symmetry: x ∈ C' ⟺ d(r,s) - x ∈ C' (from OEIS A367090) |
| L3 | Locality: frontier state determines next frontier |
| L4 | Primitivity of state transition graph |
| L5 | Existence of "good state" with positive representation rate |
| L6 | Density extraction from stationary distribution |

### Supporting Approach: Fourier/Energy

- Riesz product structure of 1_A and 1_B
- Energy bound: E(1_A * 1_B) controls representation count
- dim(A) + dim(B) ≈ 1.13 > 1 suggests transversality

---

## Technical Insights from AI Synthesis

### Convergent Findings (14 AI responses)

1. **State Space**: (81, 64) = (3⁴, 4³) cross-residue structure, 5184 total states

2. **Period**: 36 = lcm(ord₁₆(3), ord₂₇(4)) = lcm(4, 9)

3. **12-adic Structure**: lcm(3,4) = 12 governs base interaction

4. **OEIS Pseudo-symmetry**: x ∈ C' ⟺ d(r,s) - x ∈ C' is exploitable

5. **Multiplicative Escape**: Scaling by 3 or 4 usually exits complement, but doesn't force extinction

### Critical Difference from 86 Conjecture

| Aspect | 86 Conjecture | Erdős #125 |
|--------|---------------|------------|
| Goal | Survivors die | Complement doesn't dominate |
| Verification | Finite (k=27) | Infinite (asymptotic) |
| Spectral condition | ρ = 1 forces death | Need positive "good state" frequency |

---

## Computational Verification Targets

| Test | Purpose | Expected Outcome |
|------|---------|------------------|
| State closure | Does carry graph stabilize? | Finite state set |
| Substitution validation | Infer automaton from runs | Zero prediction errors to 10^7 |
| Density at cutoffs | |C ∩ [1, d(r,s)]| / d(r,s) | Uniform lower bound > ε |
| PF distribution | Compute implied density | Matches empirical |

---

## Known Unknowns (Any Would Suffice)

1. **Discrete Cantor sumset theorem**: dim(A) + dim(B) > 1 with multiplicatively independent bases implies d(A+B) > 0

2. **L^∞ bound on real convolution**: μ₃ * μ₄ bounded below on [0,1]

3. **Strong additive energy bound**: E(A_r, B_s) ≤ C·|A_r||B_s|·scale

4. **Automaticity of complement**: C' is k-automatic

---

## Assessment

**Difficulty:** Medium-Hard (upgraded from initial "recommended")

**M3 Tractability:** Yes, but harder than 86 Conjecture

**Next Steps:**
1. Consult Hasler-Melfi paper for their exact method
2. Implement computational verification targets
3. Attempt Lemma L5 (good state existence)

---

*Corrected: January 25, 2026*
*Original spike analysis valid; goal reframed*
*Method: M3 AI Synthesis with error correction*
