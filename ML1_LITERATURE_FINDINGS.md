# ML1 Literature Findings: Recent STP Research
**Date:** January 31, 2026
**Status:** Key papers identified, gap analysis complete

---

## Summary of Recent Literature (2023-2026)

### Most Relevant Papers

**1. [Hitting Times of Shrinking Targets (2025)](https://arxiv.org/html/2510.07450)** ⭐ MOST RELEVANT
- **Proves**: For **finite unions of intervals** with decreasing measure, shrinking target sets are "good" for ergodic averages
- **Key technique**: Transversality ensures geometric independence
- **Gap for us**: Only handles **FINITE** unions, we have **exponentially growing** (9^L)

**2. [Beresnevich-Datta-Ghosh-Ward (2023/24)](https://arxiv.org/abs/2307.10122)**
- Weighted effective analogue for **rectangles** (multidimensional tori)
- Uses **S-arithmetic properties** (algebraic structure matters!)
- Generalizes Kim (2007) continued fraction conditions

**3. [Shapira - Badly Approximable Grids (2024)](https://arxiv.org/abs/2402.00196)**
- **Shows**: Algebraic structure determines measure zero vs. full measure
- **Technique**: Parametric geometry of numbers + transference theorems
- **Insight**: Endpoints matter when they have special algebraic properties

**4. [Bad is Null (2023)](https://arxiv.org/abs/2307.10109)**
- General framework: badly approximable points have **measure zero** under mild conditions
- Relevant to understanding when STP fails

---

## The Critical Gap

**What exists:** STP for **finite** unions of intervals ✓

**What we need:** STP for **exponentially growing** unions (9^L intervals for L ~ 0.3n)

**The problem:**
- Standard STP: #{hits} ~ Σ μ(A_n) (when divergent)
- Our case: Σ (9/10)^n **converges** → expect finite hits
- BUT: Rotation has pure point spectrum → no mixing → convergence ≠ finiteness

---

## Potential Approaches Based on Literature

### Approach 1: Extend "Hitting Times" Techniques

**Paper:** [arXiv:2510.07450](https://arxiv.org/html/2510.07450)

**Their result:** Finite unions with shrinking measure are "good"

**Extension needed:**
- Can transversality argument extend to **growing number of components**?
- Key question: Does algebraic structure of endpoints (powers of 10) give extra control?

**Action items:**
- [ ] Read transversality proof in detail
- [ ] Check if their geometric independence argument scales with # of components
- [ ] Identify where "finite" assumption is used critically

### Approach 2: Algebraic Structure (Shapira + BDGW)

**Papers:**
- [Shapira 2024](https://arxiv.org/abs/2402.00196)
- [BDGW 2023](https://arxiv.org/abs/2307.10122)

**Key insight:** S-arithmetic properties and algebraic endpoints can change behavior

**Our advantage:**
- Endpoints of Z_L intervals are **algebraic**: log₁₀(k) where k has specific digit structure
- θ = log₁₀(2) is **logarithmic of algebraic**
- This might give special Diophantine properties

**Action items:**
- [ ] Analyze S-arithmetic properties of our setup
- [ ] Check if log₁₀(2) has special badly approximable properties
- [ ] See if interval endpoints (powers of 10) have useful structure

### Approach 3: Reduction to Finite Case

**Observation:** The periodic structure from Fourier analysis suggests mod 10 resonances

**Idea:**
- Could we prove that only finitely many "types" of intervals matter?
- Use algebraic structure to reduce infinite problem to finite certificate?

**Inspired by:** Bhargava's 290-theorem (finite test set for universal forms)

**Action items:**
- [ ] Investigate whether Z_L decomposes into finitely many "orbit types"
- [ ] Check if symmetries reduce the problem
- [ ] Look for finite certificate approach

### Approach 4: Diophantine Properties of θ = log₁₀(2)

**Papers:**
- [Kim 2007](https://www.aimsciences.org/article/doi/10.3934/dcds.2008.20.1111) - CF conditions
- BDGW effective results

**Question:** Does θ = log₁₀(2) have special continued fraction properties?

**Known:** θ ≈ 0.30103 is a logarithm of rational number

**Action items:**
- [ ] Compute continued fraction of log₁₀(2)
- [ ] Check if it's badly approximable (bounded partial quotients)
- [ ] See if this gives better bounds

---

## The Fundamental Obstacle

From Fourier analysis, we found:
- Z_L has **WORSE** Fourier decay than random unions (ratio 1.55)
- No power-law decay: α ≈ -0.005 (essentially flat)
- **Periodic spikes** at multiples of 10

This suggests:
- ❌ Fourier-based STP won't work
- ✓ Algebraic/arithmetic structure might be key
- ✓ Reduction to finite case worth pursuing

---

## Recommended Next Steps

### Priority 1: Read "Hitting Times" Paper in Detail
- Understand transversality proof
- Check if it extends to exponentially many intervals
- Identify critical bottlenecks

### Priority 2: Continued Fraction Analysis
- Compute CF expansion of log₁₀(2)
- Check badly approximable property
- See if Kim's 2007 conditions apply with modifications

### Priority 3: Algebraic Structure Exploitation
- Analyze S-arithmetic properties of setup
- Check if Shapira's techniques apply
- Look for symmetry reductions

### Priority 4: Contact Experts
- **Beresnevich, Datta, Ghosh, Ward** - rectangular targets, weighted STP
- **Shapira** - algebraic structure in Diophantine approximation
- Ask if they've considered exponentially growing target complexity

---

## Promising Signs

1. **Finite unions work** (2025 paper) - technique exists!
2. **Algebraic structure helps** (Shapira 2024) - we have it!
3. **No literature on exponential case** - potentially publishable if solved!

## Warning Signs

1. **Fourier analysis failed** - Z_L has poor regularity
2. **Pure point spectrum** - mixing arguments won't work
3. **Exponential growth** - all existing results are finite

---

## The Research Question

> **Can the transversality/algebraic structure techniques from recent STP literature (2023-2025) be extended to handle targets with exponentially growing complexity when the endpoints have algebraic structure?**

If YES → Proves Erdős 86 Conjecture
If NO → Establishes fundamental limitation of STP methods

---

*Next session: Deep dive into "Hitting Times" paper proof*
