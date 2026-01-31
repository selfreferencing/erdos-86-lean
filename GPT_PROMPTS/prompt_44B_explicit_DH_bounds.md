# Prompt 44B: Explicit Deuring-Heilbronn Bounds

## Context

From 44A, we know Pollack's proof uses Siegel's theorem at one specific point. The replacement is explicit Deuring-Heilbronn repulsion.

The key reference is: **Benli-Goel-Twiss-Zaman (2024)**, arXiv:2410.06082

## The Dichotomy Structure

**Case 1 (No exceptional zero):**
- Use explicit zero-free region: σ > 1 - c/log(qT)
- Get explicit lower bound: L(1,χ) >> 1/log f

**Case 2 (Exceptional zero β₁ exists):**
- Deuring-Heilbronn: All other zeros are repelled from β₁
- The bias HELPS us (favors the quadratic residue condition we want)

## Questions

### Q1: What does Benli-Goel-Twiss-Zaman give explicitly?

From arXiv:2410.06082:
- What is their main theorem on zero repulsion?
- What explicit constants do they provide?
- What is the dependence on conductor f?

### Q2: Kadiri's zero-free region

From arXiv:math/0510570:
- What is the explicit zero-free region?
- What constant c appears in σ > 1 - c/log(qT)?
- What lower bound on L(1,χ) follows in Case 1?

### Q3: Case 2 quantification

If χ_p has exceptional zero β₁ with 1 - β₁ < c/log f:
- How does Benli-Goel-Twiss-Zaman quantify the repulsion?
- What explicit bound do we get on other zeros?
- How does this translate to a bound on primes q with (q/p) = -1?

### Q4: The bias effect

When an exceptional zero exists for χ_p:
- The bias favors primes q with (q/p) = -1
- How strong is this bias quantitatively?
- What explicit bound on the least such q follows?

### Q5: Combining with q ≡ 3 (mod 4)

We need BOTH conditions: (p/q) = -1 AND q ≡ 3 (mod 4).

- Does χ₄χ_p also have an exceptional zero when χ_p does?
- What does DH repulsion give for the product character?
- Can both conditions be satisfied with explicit bounds?

## Desired Output

1. Statement of Benli-Goel-Twiss-Zaman main theorem with constants
2. Kadiri's explicit zero-free region with constants
3. Explicit bounds in Case 1 (no exceptional zero)
4. Explicit bounds in Case 2 (exceptional zero exists)
5. How the two conditions combine
