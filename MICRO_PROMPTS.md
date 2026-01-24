# Micro-Prompts: Breaking Down the Hard Steps

## Date: January 21, 2025

## Context

We've decomposed Lemma 5 (independence across moduli) into 10 micro-steps. Steps 1-3, 5, 7-8 are trivial or standard. The remaining gaps are:

- **Micro-Step 4**: Large prime independence (precise statement)
- **Micro-Step 6**: Conditional independence formulation (THE CRUX)
- **Micro-Step 9**: Assembly into rigorous theorem
- **Micro-Step 10**: CRT reduction alternative

---

## Micro-Prompt 6a: Character Independence on Disjoint Support

```
CHARACTER INDEPENDENCE ON DISJOINT PRIME SUPPORT

Setup:
- Let χ_1, χ_2 be quadratic characters mod m_1, m_2 respectively (m_1 ≠ m_2)
- Let L_1, L_2 be positive integers with gcd(L_1, L_2) = 1
- Both L_1, L_2 are squarefree (or have bounded exponents)

Question: Is it true that:

P(χ_1(L_1) = +1 AND χ_2(L_2) = +1) = P(χ_1(L_1) = +1) × P(χ_2(L_2) = +1)

when L_1, L_2 are "random" integers with disjoint prime support?

More precisely: Let L_1 range over squarefree integers ≤ X with all prime factors in set S_1. Let L_2 range over squarefree integers ≤ Y with all prime factors in set S_2, where S_1 ∩ S_2 = ∅.

Then:

#{(L_1, L_2) : χ_1(L_1) = +1, χ_2(L_2) = +1} / #{(L_1, L_2)}
≈ [#{L_1 : χ_1(L_1) = +1} / #{L_1}] × [#{L_2 : χ_2(L_2) = +1} / #{L_2}]

Is this exact? Approximately true? What's the error?

The intuition is that since S_1 ∩ S_2 = ∅ and the characters are independent (different moduli), there should be no correlation.
```

---

## Micro-Prompt 6b: Conditioning on Small Primes

```
CONDITIONING ON SMALL PRIME FACTORS

Setup:
- Fix a finite set T of "small" primes (e.g., T = {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41})
- For integer n, write n = S(n) · L(n) where S(n) = ∏_{p ∈ T, p|n} p^{v_p(n)} and L(n) has no prime factors in T
- Let χ be a quadratic character mod m

Question: What is:

P(χ(L(n)) = +1 | χ(S(n)) = s)

for various values of s ∈ {±1}?

Intuitively, conditioning on small primes shouldn't affect large primes. But is this exactly true?

Potential subtlety: The size of L(n) depends on S(n). If S(n) is large, then L(n) = n/S(n) is smaller, affecting the distribution.

Can you:
1. State whether the conditional probability equals the unconditional probability
2. If not, quantify the error
3. Indicate if this matters for our application (where n ~ p/4)
```

---

## Micro-Prompt 9: Assembly into Theorem

```
ASSEMBLING THE INDEPENDENCE BOUND

We have established (or assume):

(A) For x_k = n + k + 1, write x_k = S_k · L_k (small × large primes, threshold 42)

(B) For j ≠ k with j, k ∈ K_COMPLETE: gcd(L_j, L_k) = 1 (large primes don't overlap)

(C) The characters χ_k mod m_k are independent (different moduli)

(D) P(χ_k(L_k) = +1) ≈ (log p)^{-c} for some c > 0 (Selberg-Delange)

(E) Conditional on small prime values, the events {χ_k(L_k) = +1} are approximately independent

TASK: Combine (A)-(E) into a rigorous theorem:

#{p ≤ X : p ≡ 1 (mod 4), all 23 k fail} ≤ C · X / (log X)^A

What value of A can we achieve?

Specifically:
1. How do we handle the "approximately" in (E)?
2. What explicit bounds are needed?
3. Does the theorem hold unconditionally, or require GRH?
```

---

## Micro-Prompt 10: CRT Reduction for Explicit Verification

```
CRT REDUCTION FOR ESC VERIFICATION

We want to verify: For every prime p ≡ 1 (mod 4), some k ∈ K_COMPLETE has a witness.

Direct approach: Check all residue classes of p mod M where M = lcm(m_k for k ∈ K_COMPLETE).

Problem: M = lcm(3, 7, 11, 15, 19, 23, 27, 31, 39, 47, 55, 59, 67, 71, 79, 87, 95, 103, 107, 119, 127, 159, 167) is astronomically large.

Question: Can we use CRT structure to factor this verification?

Observation: The failure condition for k is:
"All prime factors of x_k = (p + m_k)/4 have χ_k(q) = +1"

This depends on p mod m_k AND the factorization of x_k.

Possible approach:
1. For each m_k, identify which p (mod m_k) could possibly fail
2. Intersect these conditions using CRT
3. Check if the intersection is empty or small

Alternative: Instead of verifying all p, verify all PATTERNS of quadratic residues.

There are at most 2^{23} = 8 million patterns of which quadratic characters take +1 vs -1 on the generators.

For each pattern, check if it corresponds to an actual failure.

Can you:
1. Describe how to implement this CRT/pattern reduction
2. Estimate the computational complexity
3. Indicate if this would yield a complete proof
```

---

## Micro-Prompt 4: Large Prime Independence (Precise Statement)

```
LARGE PRIME INDEPENDENCE FOR SHIFTED INTEGERS

Setup:
- Fix K_COMPLETE = {0, 1, 2, 3, 4, 5, 6, 7, 9, 11, 13, 14, 16, 17, 19, 21, 23, 25, 26, 29, 31, 39, 41}
- For n = (p-1)/4, define x_k = n + k + 1
- Call a prime q "large" if q > 42

Claim: For j ≠ k both in K_COMPLETE, gcd(L_j, L_k) = 1 where L_j, L_k are the "large prime parts" of x_j, x_k.

Proof: If large prime q > 42 divides both x_j and x_k, then q | (x_j - x_k) = j - k. But |j - k| ≤ 41 < 42 < q. Contradiction.

Therefore large primes partition across the x_k values.

Question: Can you formalize this into a statement about independence of character values?

Specifically: If {L_k : k ∈ K_COMPLETE} have pairwise coprime entries, and χ_k are independent characters, what can we say about:

E[∏_k 𝟙(χ_k(L_k) = +1)] vs ∏_k E[𝟙(χ_k(L_k) = +1)]

The expectation is over primes p (equivalently, over n = (p-1)/4).
```

---

## Summary

| Micro-Prompt | Target | Key Question |
|--------------|--------|--------------|
| 4 | Large prime independence | Formalize coprimality → independence |
| 6a | Character independence | Disjoint support → independent values? |
| 6b | Small prime conditioning | Does conditioning affect large part? |
| 9 | Assembly | Combine into theorem with explicit A |
| 10 | CRT reduction | Factor verification via patterns |

## Recommended Order

1. **6a first** - This is the conceptual core
2. **4 and 6b in parallel** - Supporting lemmas
3. **9 after 4, 6a, 6b** - Assembly
4. **10 as alternative track** - May be easier than probabilistic

If 6a yields a clean answer ("yes, they're independent"), the proof essentially writes itself.
