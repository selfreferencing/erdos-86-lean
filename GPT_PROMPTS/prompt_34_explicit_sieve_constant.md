# GPT Prompt 34: Pin Down the Absolute Constant C_1 in the Sieve Upper-Bound Function

## Context (follow-up to prompts 33A-1, 33A-2, 33B-1, 33B-2)

We have established (from prompt 33, four responses all verified) that the growing-K Borel-Cantelli argument for the Erdos-Straus conjecture works with:

**Theorem A'' (Uniform, from 33B):**
#{P <= x prime : P === 1 (mod 24), all pairs in F_K fail}
<= C_0 * exp(C_1 * delta(F_K)) * x / (log x)^{1 + delta(F_K)},

where C_0 and C_1 are ABSOLUTE constants and delta(F_K) ~ 0.18 * (log K)^2.

Equivalently: C(K) = exp(O((log K)^2)) = K^{O(log K)} (quasi-polynomial).

This was proved via the large sieve + BDH approach (33B), where:
- The large sieve constant (N + Q^2) is absolute
- The BDH constant is absolute
- For q > K, the forbidden residue classes are collision-free (shifts distinct)
- The sieve upper-bound function F(kappa, 2) <= exp(C_1 * kappa) for absolute C_1

The growing-K Borel-Cantelli gives finiteness of failures above certBound provided:
- A > sqrt(log 2 / 0.18) ~ 1.96 (threshold for main decay)
- The absolute constant C_1 is not too large

**THE REMAINING QUESTION:** What is C_1?

Our numerical verification shows:
- C_1 = 1 (effective C3 = 0.18): tail from certBound = 10^6 is 0.354 < 1. WORKS.
- C_1 ~ 2.8 (effective C3 = 0.5): crossover at n ~ 1924 (certBound ~ 10^579). IMPRACTICAL.
- C_1 ~ 5.6 (effective C3 = 1.0): crossover beyond n = 2000. FAILS practically.

So the question is not whether the argument converges (it does for any C_1, with A large enough), but whether our current certBound = 10^6 suffices. For that we need C_1 to be explicitly bounded.

## What we know about C_1

From 33B-2: "The sieve upper function F(kappa, u) with u = log D / log z = 2 gives F(kappa, 2) <= exp(C_1 * kappa)." The constant C_1 comes from the Selberg/beta-sieve upper-bound theory.

From 33A-2: "The Selberg sieve overhead is exp(O(kappa))" and separately "the collision primes and Mertens constants each contribute exp(O(delta * log log K))." In the large sieve framework (33B), the Mertens constant issue is absorbed into the BDH averaging, so only the sieve function F(kappa, 2) matters.

So C_1 is really the constant in the classical upper-bound sieve function.

## The specific question

The classical linear sieve (Iwaniec, Friedlander-Iwaniec, Opera de Cribro) gives for the upper-bound sieve function:

F(s) = 2e^gamma / s    for s >= 2  (in dimension kappa = 1).

More generally, the kappa-dimensional Selberg sieve upper-bound function satisfies:

f_kappa(s) * V(z) <= S(A, z) / X  (approximately)

where f_kappa is the continuous solution to a delay-differential equation.

For our application, kappa = delta(F_K) is large and growing, and s = log D / log z = 2 (fixed). The question is: how does f_kappa(2) behave as kappa grows?

## Tasks

### Task 1: The sieve upper-bound function for general dimension kappa

State the classical result for the upper-bound sieve function f_kappa(s) (or F_kappa(s), or sigma_kappa(s), depending on notation) in dimension kappa >= 1, with s >= 2.

Specifically:
(a) What is the classical formula or bound for f_kappa(2) as a function of kappa?
(b) Standard references give f_kappa(s) in terms of solutions to the adjoint equation. For s = 2, what is the explicit dependence on kappa?
(c) Is f_kappa(2) bounded by exp(c * kappa) for some explicit c? If so, what is c?
(d) Is f_kappa(2) bounded by (c * kappa)^kappa / Gamma(kappa + 1) (Stirling-type)? That would also give exp(O(kappa)) but with a different constant.

### Task 2: Opera de Cribro and Iwaniec's formulas

In Friedlander-Iwaniec "Opera de Cribro" (or Iwaniec's "The sieve method"):
(a) What is the explicit formula for the upper-bound sieve constant in dimension kappa at level s = 2?
(b) Chapter 11 (or equivalent) treats the kappa-dimensional sieve. Quote or derive the relevant bound.
(c) The "beta-sieve" (Iwaniec) with parameters beta chosen for dimension kappa: what is the resulting constant?

### Task 3: Numerical evaluation for our kappa range

For our application, delta(F_K) ranges from about 4.79 (K=200) to about 8.5 (K=1000) to about 18 (K=10000).

(a) Evaluate f_kappa(2) numerically for kappa = 5, 10, 15, 20, 50, 100.
(b) Fit: is f_kappa(2) better described as exp(c * kappa), or as kappa^kappa / Gamma(kappa+1), or something else?
(c) Extract the effective C_1 from the data: if f_kappa(2) ~ exp(C_1 * kappa), what is C_1?

### Task 4: The exact sources of exp(C_1 * delta) in our bound

In our specific application (33B's proof), the constant C(K) arises from:

1. **Sieve upper-bound function:** f_kappa(2) where kappa = delta(F_K)
2. **Collision primes correction:** Prod_{q <= K} (1 - rho(q)/q)^{-1}, bounded by exp(O(delta * log log K)) (from 33A-2)
3. **z-to-x conversion:** (log z / log x)^delta = 4^delta (from 33B-2)
4. **BDH remainder:** absorbed, contributing at most a polylog factor

Which of these is the dominant contributor to C_1? In particular:
(a) Is the sieve function f_kappa(2) the dominant term, or is the collision correction dominant?
(b) If the sieve function dominates, what is its effective C_1?
(c) If the collision correction dominates (via Mertens constants), then 33A-2's O(delta * log log K) applies and C_1 effectively depends on log log K (weakly). In that case, what is the effective constant for K = 200..10000?

### Task 5: Can we get C_1 <= 1?

The magic number: if C_1 <= 1, then with A = 3 the tail from certBound = 10^6 is 0.354 < 1, and we're done.

(a) Is C_1 <= 1 achievable? What would it require?
(b) If the sieve function gives f_kappa(2) = (2e^gamma)^kappa / Gamma(kappa + 1) (or similar), then log f_kappa(2) ~ kappa * log(2e^gamma) - kappa*log(kappa) + kappa. For large kappa, the -kappa*log(kappa) term dominates and we get f_kappa(2) -> 0, meaning C_1 is effectively NEGATIVE for large kappa. Is this correct?
(c) Alternatively, does the sieve function have a lower bound that prevents f_kappa(2) from decaying? The Selberg sieve is an UPPER bound sieve, so f_kappa(s) should be >= 1 (it overcounts). What is the truth?

### Task 6: The Richert-Selberg explicit constants

For a completely explicit approach:
(a) Selberg's original work gives explicit constants for the upper-bound sieve. What are they for dimension kappa and level s = 2?
(b) Richert's improvements (1976) and later work: any explicit evaluations?
(c) Is there a reference that gives a NUMERICAL table of f_kappa(2) for various kappa?

### Task 7: Lean axiom with explicit C_1

Given your findings, state the cleanest axiom for the Lean formalization:

```lean
axiom uniform_density_bound :
  exists (C0 C1 : Real) (x0 : Real),
    C0 > 0 /\ C1 > 0 /\ C1 <= ??? /\  -- what is the bound on C1?
    x0 >= 3 /\
    forall (K : Nat) (x : Real),
      K >= 2 -> x >= x0 ->
      failure_count K x <=
        C0 * Real.exp (C1 * delta K) *
        x / (Real.log x) ^ (1 + delta K)
```

What should ??? be? Give the tightest bound you can justify from classical sieve theory.

## Key constraints

- The sieve dimension kappa = delta(F_K) grows: it is NOT fixed. Bounds that are "O_kappa(1)" with hidden kappa-dependence are useless. We need EXPLICIT dependence on kappa.
- The level parameter s = log D / log z = 2 is FIXED. We are not optimizing over s.
- We are using the UPPER-bound sieve (counting primes that AVOID certain residue classes). Not the lower-bound sieve.
- The underlying sieve is for PRIMES (restricted to P === 1 mod 24), so we use BDH/BV for the distribution level. The BDH/BV constants are absolute and already accounted for.
- We need the EXPLICIT numerical value (or a tight upper bound) for C_1, not just "C_1 exists."

## What makes this tractable

Several features of our specific problem should help:

1. **s = 2 is fixed.** We're not asking about f_kappa(s) for general s, just s = 2. This is the simplest non-trivial case.

2. **The delay-differential equation simplifies for large kappa.** The DDE solutions for the sieve functions have known asymptotics as kappa -> infinity with s fixed. The upper-bound function typically decays like 1/Gamma(kappa+1) times an exponential, which is VERY favorable.

3. **We have numerical verification available.** Whatever formula you give, I will check it numerically for kappa = 5, 10, 20, 50. So approximate formulas are fine as long as they can be evaluated.

4. **We only need an UPPER bound on C_1.** We don't need the exact value. An upper bound C_1 <= 2 (or even C_1 <= 5) would be useful, since we can then choose A large enough to compensate.

## The payoff

If C_1 <= 1: we're done. The sorry is filled with certBound = 10^6.

If 1 < C_1 <= 5: we need to choose A > sqrt((log 2 + C_1 * 0.18) / 0.18), which is still feasible, and may need to extend certBound somewhat.

If C_1 > 5: we need to investigate whether the Mertens constant correction (33A-2) or the collision correction is the true bottleneck, and whether a more careful analysis can reduce C_1.

In any case, having an EXPLICIT C_1 turns the remaining problem from a theoretical gap into a computation.
