# ML1 Research Plan: Structured Shrinking-Target Property
**Date:** January 31, 2026
**Goal:** Prove or find path to proving finiteness of zeroless powers via structured STP theorem

---

## The Target Statement (ML1 / C1)

**Conjecture:** Let R_θ be rotation by θ = log₁₀(2). Let A_n = Z_{L(n)} where:
- Z_L = zeroless set = {f ∈ [0,1) : digits 2,...,L of 10^f all in {1,...,9}}
- L(n) = ⌊n·θ⌋ + 1 (number of digits of 2^n)

If we can show:
1. Σ μ(Z_{L(n)}) < ∞ ✓ (already proven: Σ (9/10)^n < ∞)
2. Z_L has ≤ 9^L intervals with algebraic endpoints ✓ (true by construction)
3. **Fourier spectrum of 1_{Z_L} is "sufficiently flat"** ❓
4. **Some additional structure condition** ❓

Then #{n : {nθ} ∈ Z_{L(n)}} < ∞ (would prove Erdős 86).

---

## What We Know

### From GPT 55A (Shrinking Target Survey):

**Existing STP results (all single-interval only):**
- Kurzweil (1955): BC 0-1 law for balls
- Fayad (2005): Monotone STP ⟺ constant type
- Tseng (2007/08): MSTP for toral translations
- D.H. Kim (2007+): Strong recurrence via continued fractions
- Fuchs-Kim (2015/16): Necessary & sufficient CF condition
- Simmons (2015): Modified Kurzweil with monotonicity
- Beresnevich-Datta-Ghosh-Ward (2023/24): Weighted effective for rectangles

**The Gap:** "Discrepancy bounds cannot 'pay for' exponentially many components"
- Error term: 9^d × (log n)/n >> main term

### From GPT 54A (Clean Architecture):

**Why rotations + 9^L components is hard:**
> "Rotations have pure point spectrum (no mixing). Therefore 'μ(A) → 0' does NOT imply 'orbit eventually avoids A.'"

**What would work:**
> "Either a structured STP theorem for digit cylinders OR a genuine lemma converting 'zeroless' into 'small linear form in log(2), log(5)'"

---

## Research Directions

### Direction 1: Fourier Decay for Digit-Restricted Sets

**Key question:** Does 1_{Z_L} have Fourier decay despite 9^L components?

**Literature to search:**
- "missing digit set Fourier decay"
- "Cantor set Fourier transform"
- "digit restricted integers exponential sums"
- Saavedra-Araya (2025): Distribution of missing-digit sets in APs

**Why this might work:**
- Z_L has very regular structure (product of digit constraints)
- Endpoints are algebraic (powers of 10)
- Possible cancelation in Fourier coefficients

### Direction 2: Complexity-Controlled STP

**Key question:** Recent work on STP with bounded complexity?

**Literature to search:**
- "shrinking targets bounded complexity"
- "irrational rotation exponentially many intervals"
- "moving targets rotation discrepancy bounded variation"
- "Borel Cantelli rotations Ostrowski expansion"

**Post-2024 searches:**
- arXiv: "shrinking target" + "rotation" (2024-2026)
- Papers citing Fuchs-Kim (2015/16)
- Papers citing Beresnevich et al. (2023/24)

### Direction 3: Benford Law / Significant Digit Theory

**Key question:** Does Benford law analysis give stronger structure?

**Literature to search:**
- Diaconis (leading digits ↔ uniform distribution mod 1)
- Berger-Hill Benford primer
- Recent work on higher-order digit correlations

**Why this might help:**
- θ = log₁₀(2) is THE canonical Benford example
- May have special properties not true for general θ

### Direction 4: Effective Equidistribution with Structure

**Key question:** Does algebraic structure of endpoints give effective bounds?

**Literature to search:**
- "effective equidistribution algebraic endpoints"
- "discrepancy bounds arithmetic progressions intervals"
- Work by Elkies, Duke, others on effective Weyl

---

## Concrete Next Steps

### Step 1: Fourier Analysis (Computational)
- [ ] Compute Fourier coefficients of 1_{Z_L} for L = 2,3,4,5
- [ ] Check for decay pattern
- [ ] Compare to random unions of same measure

### Step 2: Literature Search (2024-2026)
- [ ] arXiv search: "shrinking target" + "rotation" (last 2 years)
- [ ] Google Scholar: papers citing Fuchs-Kim 2015
- [ ] Google Scholar: papers citing Beresnevich-Datta-Ghosh-Ward 2023
- [ ] Search for Saavedra-Araya 2025 missing-digit paper

### Step 3: Structure Exploitation
- [ ] Can we prove Fourier flatness using digit structure?
- [ ] Does Benford/Diaconis give special properties for θ = log₁₀(2)?
- [ ] Can we reduce to finite case analysis using algebraic endpoints?

### Step 4: Weakened Versions
- [ ] What if we only prove "for θ = log₁₀(2)" not general θ?
- [ ] What if we use computational certificate for small L?
- [ ] Can we prove density 0 more strongly (explicit bound on #{n ≤ N})?

---

## Key Papers to Find

1. **Beresnevich-Datta-Ghosh-Ward (2023/24)**: "Weighted effective analogue for rectangles"
   - Most recent major STP result
   - May have techniques for multiple-interval targets

2. **Saavedra-Araya (2025)**: "Distribution of missing-digit sets"
   - Directly relevant to digit-restricted sets
   - May have Fourier/exponential sum tools

3. **Recent Diophantine approximation surveys**
   - May discuss open problems in STP
   - Could point to promising directions

---

## Success Criteria

**Minimal success:** Find a paper with techniques that seem applicable

**Good success:** Identify specific theorem that covers a special case

**Great success:** Formulate precise conjecture with evidence it might be provable

**Ideal success:** Prove ML1 for θ = log₁₀(2)

---

## Notes

- Focus on **post-2020 literature** (most likely to have new techniques)
- Prioritize **explicit/effective results** over asymptotic
- Look for **complexity control** in hypotheses
- Remember: we only need it for ONE specific θ, not all θ

---

*Session started: January 31, 2026*
