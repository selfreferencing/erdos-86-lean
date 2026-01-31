# APPROACH 55A: GPT Response — Shrinking Target Survey

## One-Sentence Assessment

> "Existing shrinking-target theorems for rotations are powerful for **single-ball/interval targets** and **almost-every target point**, but they do not currently offer a path to handle **digit-cylinder targets with ~9^d(n) components** in a way that yields a **pointwise, effective cutoff** for the specific orbit n·log₁₀(2)."

---

## Survey of Shrinking-Target Theorems for Rotations

### Classical Results (All for Single Intervals)

| Author(s) | Year | Key Result |
|-----------|------|------------|
| Kurzweil | 1955 | BC 0-1 law for shrinking balls; tied to badly approximable θ |
| Fayad | 2005 | Monotone STP ⟺ constant type (torus translations) |
| Tseng | 2007/08 | MSTP and s-MSTP variants for toral translations |
| D.H. Kim | 2007+ | Strong recurrence via continued fractions/Ostrowski |
| Fuchs-Kim | 2015/16 | Necessary & sufficient CF condition containing above as special cases |
| Simmons | 2015 | Modified Kurzweil with monotonicity; CF criterion |
| Beresnevich-Datta-Ghosh-Ward | 2023/24 | Weighted effective analogue for rectangles |

**Critical limitation:** All these require targets that are **single intervals/balls**, not unions of exponentially many components.

---

## Why Rotations + 9^d Components is Out of Scope

### The Discrepancy Blowup

For Kronecker sequence x_n = {nθ} and set A = union of N intervals:
```
|#{n ≤ M : x_n ∈ A} - M·λ(A)| ≲ N × M × D_M(θ)
```

For our problem:
- N ~ 9^d (exponentially many components)
- d(n) ~ 0.301n
- Best discrepancy: D_M ~ (log M)/M

Error term: **9^d × (log n)/n >> main term M·λ(S_d)**

> "Discrepancy bounds in their standard form cannot 'pay for' exponentially many components."

### The Key Obstruction

> **Pure point spectrum + no decay of correlations + exponentially growing boundary complexity**

Rotations are NOT mixing — they have pure point spectrum. The mixing/expanding system theorems (Hill-Velani, Chernov-Kleinbock) don't apply.

---

## What About Duffin-Schaeffer / Mass Transference?

**Conceptually relevant but not directly helpful:**

- Duffin-Schaeffer is "for a.e. x" about approximation by rationals
- Our problem is about a **specific** θ = log₁₀(2) and **specific** orbit point x = 0
- Even refined rotation results conclude "for a.e. s" under divergence hypotheses

---

## What IS Provable (Weaker Results)

### 1. Natural Density Zero

Since S_{d+1} ⊆ S_d and d(n) → ∞, equidistribution gives upper density ≤ λ(S_D) for any D. Letting D → ∞ gives density 0.

**This uses only standard equidistribution (Benford-style), no shrinking-target theorems needed.**

### 2. Fixed-Prefix Statistics

For any fixed d, the set of n with first d digits of 2^n avoiding 0 has asymptotic frequency λ(S_d), computable exactly.

---

## Adjacent Literature Worth Investigating

### A. Benford / Significant-Digit Laws
- Diaconis (leading digits ↔ uniform distribution mod 1)
- Berger-Hill Benford primer

### B. "Missing Digit" Sets
- **Saavedra-Araya (2025)**: Distribution of missing-digit sets in arithmetic progressions
- Potential source for Fourier/exponential sum tools exploiting digit structure

### C. Shrinking Targets in Expanding Systems
- For base-10 map T(x) = 10x mod 1, Borel-Cantelli is far more accessible
- But our dynamics is **rotation**, not expanding map

---

## Search Terms for Further Research

**Rotations & Shrinking Targets:**
- "irrational rotation shrinking targets union of intervals"
- "moving targets rotation discrepancy bounded variation"
- "Borel Cantelli rotations Ostrowski expansion"

**Metric Limsup Technology:**
- "mass transference principle arbitrary shapes"
- "ubiquity limsup sets open sets"

**Digit-Restricted Sets:**
- "missing digit set exponential sums"
- "Fourier decay missing digit Cantor set"
- "digit restricted integers distribution"

---

## The Bottom Line

To make shrinking-target theory work for Erdős 86, you would need **mixing-like independence** or strong decorrelation at exponentially small scales for a rigid rotation.

> "That kind of input is essentially as hard as proving strong randomness/normality-type properties for the sequence 2^n in base 10 (which is far beyond what current rotation shrinking-target theorems deliver)."

---

## GPT's Offer

> "If you want, I can also sketch what a *hypothetical* 'right theorem' would need to look like (i.e., the minimal quantitative decorrelation/discrepancy statement that, if proven for θ = log₁₀(2), would force finiteness of hits to your S_{d(n)})."
