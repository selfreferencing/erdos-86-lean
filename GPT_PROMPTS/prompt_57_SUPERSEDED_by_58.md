# Prompt 57: Verify ED2 Works with Burgess-Scale Auxiliary Modulus

## Context

From prompts 54A/B, we identified a potentially effective path to ES:

**The Burgess-Product Construction:**
1. Use Pollack/Burgess to find k small primes ℓᵢ ≤ P^{0.151} with (−P/ℓᵢ) = 1
2. Take q = ∏ℓᵢ ≤ P^{0.151k}
3. For k = 3: q ≤ P^{0.453} < √P

This avoids Siegel because Burgess bounds are effective at power scale (P^θ), unlike polylog scale ((log P)²).

## The Critical Verification

We need to check that ED2 (Dyachenko's parameterization) actually produces valid ES decompositions when q ≈ P^{0.45}.

### Q1: Review ED2's Window Constraint

From prompt 46 ED2, the key constraint was q << √P.

But "<<" hides constants. What is the PRECISE requirement?

Specifically, if ED2 needs:
- α · s² < c · P for some constant c
- And q ~ s in the relevant regime

What is the actual upper bound on q/√P that ED2 tolerates?

Is q ≤ P^{0.45} = √P / P^{0.05} sufficient margin?

### Q2: Trace Through ED2 with Specific q

Let's trace through ED2 with:
- P a large prime ≡ 1 (mod 4)
- q = ℓ₁ℓ₂ℓ₃ where each ℓᵢ ≤ P^{0.151}
- So q ≤ P^{0.453}

At each step:
1. Solve s² ≡ −P (mod q) via CRT
2. Pick α in the allowed window
3. Compute the ES denominators

Do all denominators come out as positive integers?

### Q3: What Are the Explicit Constants?

**From Pollack/Burgess side:**
- Treviño: For D > 1596, ∃ prime p ≤ D^{0.45} with (D/p) = −1
- Pollack: Many primes ≤ m^{1/(4√e)+ε} ≈ m^{0.151}

**From ED2 side:**
- What is the explicit constant in the window bound?
- For P > P₀, what P₀ makes the construction work?

### Q4: Does ω(q) = 3 Cause Issues?

ED2 was originally stated for prime q. We established squarefree q works via CRT (prompt 46 ED2, 50A/B).

But does having exactly 3 prime factors create any complications?
- Extra factors in divisibility conditions?
- Issues with the lift lemma?

### Q5: End-to-End Effective Statement

If this works, state the effective theorem:

> **Theorem (Effective ES via Burgess-ED2):** For all primes P > P₀, the Erdős-Straus equation 4/P = 1/x + 1/y + 1/z has a solution in positive integers x, y, z.

With:
- Explicit P₀
- No GRH or Siegel assumptions
- Fully effective proof

### Q6: What Could Go Wrong?

List potential failure modes:
1. The window constant in ED2 might be too tight for q ≈ P^{0.45}
2. The Pollack/Burgess constants might not compose well
3. There might be positivity issues for denominators
4. The "many primes" in Pollack might not include ones with (−P/ℓ) = 1

### Q7: If This Fails, What's the Minimum k?

If k = 3 primes doesn't work (because P^{0.453} is too close to √P), what about k = 2?

k = 2 gives q ≤ P^{0.302}, which is well below √P.

But then we need two primes each ≤ P^{0.151} with (−P/ℓ) = 1. Is existence of TWO such primes effective?

## Desired Output

1. **YES/NO:** Does ED2 work with q ≈ P^{0.45}?
2. If YES: State the effective theorem with explicit P₀
3. If NO: Identify exactly what fails and whether k = 2 might work
4. **Bottom line:** Is the Burgess-ED2 path viable for effective ES?
