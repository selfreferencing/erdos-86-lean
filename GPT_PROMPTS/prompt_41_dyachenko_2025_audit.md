# Prompt 41: Critical Audit of Dyachenko 2025 Preprint Claim

## Background Warning

During our Lean formalization of Dyachenko's earlier work, we found errors. Thomas at erdosproblems.com independently confirmed the paper has problems. We have a standing policy: **Do not rely on Dyachenko's results without independent verification.**

## The Claim to Audit

GPT (Prompt 40A) flagged:

> "There is a 14 Oct 2025 arXiv preprint by E. Dyachenko that explicitly claims: 'The central result (Theorem 10.21) states that for every prime P there exists a representation … constructed explicitly by method ED2,' focusing on P ≡ 1 (mod 4)."
>
> arXiv:2511.07465

This would, if correct, completely resolve ES for primes ≡ 1 (mod 4) without any GRH assumption.

## Critical Questions

### Q1: What exactly does Theorem 10.21 claim?

Please quote the precise statement of Theorem 10.21 from the paper. What are:
- The hypotheses?
- The conclusion?
- Any conditions or assumptions (explicit or implicit)?

### Q2: What is the proof structure?

Outline the key steps of the proof. Specifically:
1. What lemmas/propositions does it depend on?
2. Which steps involve existential claims (∃ statements)?
3. Which steps involve uniform bounds?
4. Where does the "explicit construction" come from?

### Q3: Gap Analysis - Known Problem Areas

From our previous investigation, Dyachenko's lattice argument has these known issues:

**Remark 9.4 gap:** The lattice density argument requires that the lattice point (b', c') found by Proposition 9.25 actually produces valid (A, d) parameters. This requires:
- A = α·b'·c' falls in the window [(p+3)/4, (3p-3)/4]
- Some divisor d of A² satisfies d ≡ -A (mod δ) where δ = 4A - p

**The divisor distribution problem:** Finding such a divisor d requires that the divisors of A² hit the residue class -A (mod δ). This is not automatic and was the source of errors in the earlier version.

**Questions:**
- Does Theorem 10.21 address or circumvent these issues?
- Is there a new argument for why divisors hit the required residue class?
- Or does it implicitly assume something that isn't proven?

### Q4: Comparison with our (A, d) formulation

Our GRH axiom states:

```
For p ≡ 1 (mod 24) with p ≥ certBound, ∃ A, d such that:
  - (p+3)/4 ≤ A ≤ (3p-3)/4
  - 0 < d and d | A²
  - (4A - p) | (d + A)
```

Does Theorem 10.21 actually prove this, or does it prove something different (e.g., existence of (δ, b, c) in the ED2 parameterization that doesn't directly translate)?

### Q5: Specific red flags to check

1. **Does the proof use "for sufficiently large P" without specifying how large?**
   - If so, it may not actually prove unconditional existence for all primes.

2. **Does the proof invoke a covering argument with finite families?**
   - Our analysis showed finite covering systems cannot work for the hard residue classes (Chebotarev obstruction, 21A/29A).

3. **Does the proof use averaging/density arguments?**
   - Such arguments typically give "almost all primes" not "all primes."

4. **Does the proof rely on effective bounds from analytic number theory?**
   - If so, what are the dependencies? Could they hide a GRH assumption?

5. **Is there a computational verification claim?**
   - If so, what bound? How does it interact with the theoretical claim?

### Q6: Cross-reference with erdosproblems.com

Is there any discussion of this paper on erdosproblems.com or similar forums? What do other mathematicians say about it?

### Q7: Bottom line assessment

Rate the likelihood that Theorem 10.21 is:
- (A) Correct and provides an unconditional proof of ES for P ≡ 1 (mod 4)
- (B) Correct but conditional on something not made explicit
- (C) Contains a gap similar to the known issues
- (D) Fundamentally flawed

## Desired Output

1. Exact statement of Theorem 10.21 with all conditions
2. Proof outline identifying potential weak points
3. Specific analysis of whether the known gap areas are addressed
4. Assessment of reliability given the history of errors
5. Recommendation: Should we investigate further, or maintain our GRH-conditional approach?
