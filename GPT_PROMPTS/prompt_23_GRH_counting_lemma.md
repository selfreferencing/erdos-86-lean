# GPT Prompt 23: GRH-Conditional Counting Lemma Template for Lean

## Context (follow-up to your previous response)

In your previous response (prompt 14), you offered to "sketch a precise GRH-conditional counting lemma template that would fit our Lean workflow (statement: if explicit inequality holds for X, then no primes P > X fail all s <= S), pointing to exact analytic ingredients." We are accepting that offer.

## Background

We are proving the Erdos-Straus conjecture for primes P === 1 (mod 24), P >= 10^6. The key results so far:

1. **Theorem B (prompt 13, GRH):** For each prime P === 1 (mod 4), some s << (log P)^2 makes P + 4s^2 have a prime factor q === 3 (mod 4). Via effective Chebotarev / LLS.

2. **Character-kernel lemma (prompt 14):** Failure for pair (alpha, s) means all prime factors of P + 4*alpha*s^2 land in ker(chi) for some odd quadratic character chi (mod 4*alpha*s) with chi(-1) = -1.

3. **Theorem D (prompt 16, unconditional):** density-zero exceptional set via sieve.

4. **The "sufficient conjecture" (prompt 19):** exists s <= P^eps with prime q | (P+4s^2), q === -1 (mod 4s).

## What I need from you

### Task 1: State the GRH-conditional per-prime theorem precisely

Prove (or state with proof sketch) the following under GRH:

**Theorem B+ (GRH):** There exist explicit constants C, c > 0 such that for every prime P >= C, there exist alpha, s with 4*alpha*s^2 <= c*(log P)^4 such that (4*alpha*s*r - 1) divides (P + 4*alpha*s^2) for some positive integer r.

In other words: under GRH, a budget of K = O((log P)^4) suffices for EVERY prime.

The proof should proceed via:
(a) GRH gives: the least prime q in the Frobenius class {q : q === 3 (mod 4), (P/q) = -1} satisfies q <= c_1*(log P)^2 (LLS bound).
(b) Such q divides P + 4s^2 for some s < q (since -P is a QR mod q, so P + 4s^2 === 0 (mod q) is solvable).
(c) q === 3 (mod 4) means q === -1 (mod 4) (taking alpha=1, s as found), so q is a divisor of P + 4s^2 with q === -1 (mod 4*1*s)... wait, we need q === -1 (mod 4s), not just q === -1 (mod 4).

ADDRESS THIS GAP: the GRH bound gives a prime q with q === 3 (mod 4) and q | (P + 4s^2), but we need q === -1 (mod 4s), which is a STRONGER condition (moving modulus). How do you bridge this?

### Task 2: The moving-modulus problem

The key difficulty: for alpha=1, we need a divisor d of P + 4s^2 with d === -1 (mod 4s). The modulus 4s DEPENDS on s.

Under GRH, can you find s and a prime factor q of P + 4s^2 satisfying q === -1 (mod 4s) simultaneously? This requires q to be in a specific Frobenius class in a number field that depends on s.

Two approaches:
(a) Fix s first, then find q === -1 (mod 4s) dividing P + 4s^2. This needs q in the intersection of {q : q | (P+4s^2)} and {q : q === -1 (mod 4s)}. Under GRH, the smallest q === -1 (mod 4s) is O((s*log(sP))^2), but we need it to DIVIDE P + 4s^2.

(b) Find q first (small, with useful properties), then find s such that q | (P+4s^2) AND q === -1 (mod 4s). The second condition means s === (q+1)/4 (mod q)... but s must also satisfy q | (P + 4s^2).

Work through both approaches. Which one gives a concrete bound?

### Task 3: State the counting lemma for Lean

Write the precise statement that would be axiomatized in Lean 4:

```
axiom GRH_counting_lemma :
  ∀ P : Nat, P.Prime → P % 24 = 1 → P ≥ 10^6 →
  ∃ α s r : Nat, α ≥ 1 ∧ s ≥ 1 ∧ r ≥ 1 ∧
    4 * α * s^2 ≤ C * (Nat.log P)^4 ∧
    (4 * α * s * r - 1) ∣ (P + 4 * α * s^2)
```

(with C an explicit constant).

Then state: "This axiom is a consequence of the Generalized Riemann Hypothesis applied to Hecke L-functions of quadratic characters, via the Lamzouri-Li-Soundararajan effective Chebotarev bound."

### Task 4: Can the exponent be reduced?

Under GRH, the LLS bound gives q << (log P)^2. This means s << (log P)^2 and K = 4s^2 << (log P)^4.

Can we do better? Specifically:
- If we allow alpha > 1, does the search space enlarge enough to reduce the exponent?
- Is there a bound of the form K << (log P)^{2+eps}?
- What is the theoretical minimum exponent under GRH?

### Task 5: What would make this unconditional?

The LLS bound is conditional on GRH. Unconditionally:
- Burgess gives the least QNR << P^{1/(4*sqrt(e)) + eps} ~ P^{0.152}
- But Ma-McGown-Rhodes-Wanner (2019) give q << P^{1/4} * log P for the first prime QNR
- Forcing q === 3 (mod 4) simultaneously is harder

Under what unconditional hypothesis (weaker than GRH but stronger than current technology) would the counting lemma hold with polynomial savings? State the weakest sufficient hypothesis.

## Constraints

- The main value is the precise STATEMENT of the GRH lemma, suitable for Lean axiomatization
- Address the moving-modulus gap honestly (Task 2)
- If the gap cannot be bridged, say so clearly and state what additional input is needed
- Explicit constants wherever possible
