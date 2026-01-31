# Prompt 58: Verify Residue-Side Methods for Effective ES

## Context Update

From prompts 53-57, we've clarified a critical issue:

**The Sign Problem:**
- Burgess/Pollack/Treviño give primes with χ(ℓ) = **-1** (nonresidues)
- ED2 needs (−P/ℓ) = **+1** (residues/split primes)
- **These are different!** The Burgess-product approach was a red herring.

**Viable paths (residue side):**
1. **P+1 trick (56B):** Take odd prime ℓ | (P+1), automatically get (−P/ℓ) = +1
2. **Linnik-Vinogradov (56A):** Claimed P^{1/4} bound for least prime quadratic residue

## The Critical Verification Questions

### Q1: Verify the P+1 Trick Works

**Claim (56B):** For P prime > 2:
- P+1 is composite (even, > 2)
- Any composite has a prime factor ≤ its square root
- If ℓ | (P+1) is odd, then -P ≡ 1 (mod ℓ), so (−P/ℓ) = (1/ℓ) = 1

**Question 1a:** Is this argument correct? Does (−P/ℓ) = 1 follow from ℓ | (P+1)?

**Question 1b:** The ℓ = 2 case: For P ≡ 5 (mod 8), we have (−P/2) = -1. In this case:
- If P+1 = 2 × (large prime q), the only odd factor is q > √P
- Does this create exceptions? How many P have this form?

**Question 1c:** For the "typical" P, does the P+1 trick give q = ℓ ≤ √P?

### Q2: Verify Linnik-Vinogradov for Residues

**Claim (56A):** "The least prime quadratic residue r_q modulo prime q satisfies r_q ≤ q^{1/4+o(1)} unconditionally."

**Question 2a:** Is this claim correct? What's the precise statement?

**Question 2b:** Does this apply to our specific character (−P/·)?

Specifically: For the quadratic character χ(ℓ) = (−P/ℓ), is there an unconditional bound saying:
> ∃ prime ℓ ≤ P^{1/4+o(1)} with (−P/ℓ) = +1?

**Question 2c:** If yes, is this effective (explicit constants)?

**Question 2d:** How does this compare to the Burgess bound P^{0.151} for nonresidues?

### Q3: ED2 Bridge Verification

**The bridge problem (from 57A):**

Having s² ≡ -P (mod q) is NOT the same as having an admissible ED2 triple (δ, b, c).

ED2 requires:
- Identity: (4b-1)(4c-1) = 4Pδ + 1
- Divisibility: δ | bc

**Question 3a:** What conditions on q (beyond just (−P/q) = 1) ensure an admissible ED2 triple exists?

**Question 3b:** Does the P+1 construction (q = prime factor of P+1) satisfy these conditions?

**Question 3c:** Is there evidence that "natural" ED2 covering schemes fail? (57A mentioned a Lean refutation)

### Q4: The Sophie Germain Exception

For P ≡ 5 (mod 8) where (P+1)/2 is prime:
- The only prime factor of P+1 that's ≤ √P is 2
- But (−P/2) = -1 for P ≡ 5 (mod 8)

**Question 4a:** How dense are these exceptional P? (Sophie Germain primes in 5 mod 8 class)

**Question 4b:** For these exceptions, does Linnik-Vinogradov provide an alternative?

**Question 4c:** Can we state: "For all P > P₀, at least one of {P+1 trick, Linnik-Vinogradov} works"?

### Q5: End-to-End Effective Theorem

If the verifications succeed, state:

> **Theorem (Effective ES).** For all primes P > P₀, the equation 4/P = 1/x + 1/y + 1/z has a solution in positive integers.

With:
- Explicit P₀ (or at least qualitative: "effectively computable")
- Which method applies when
- The ED2 bridge made explicit

### Q6: What's Still Missing?

List any remaining gaps:
1. Is the ED2 bridge from q to (δ, b, c) actually proven?
2. Are there P for which neither method works?
3. Are explicit constants available?

## Summary Table

| Method | Character | Scale | ED2 compatible? | Covers all P? |
|--------|-----------|-------|-----------------|---------------|
| P+1 trick | +1 ✓ | ≤ √P | ? (need bridge) | Most (not Sophie Germain ∩ 5 mod 8) |
| Linnik-Vinogradov | +1 (claimed) | P^{1/4} | ? (need bridge) | All (if claim holds) |
| Burgess product | -1 ✗ | P^{0.45} | N/A (wrong sign) | N/A |

## Desired Output

1. **P+1 trick:** Fully verified or identify gaps
2. **Linnik-Vinogradov:** Confirm or refute the P^{1/4} claim for residues
3. **ED2 bridge:** What's actually needed to go from q to a solution?
4. **Effective theorem:** If possible, state it; if not, identify exactly what's missing
