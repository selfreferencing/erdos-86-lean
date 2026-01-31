# GPT Prompt 33B: Reprove Theorem A' via Large Sieve for Uniform C(K)

## Context (follow-up to prompts 22A, 25A, 30A/30B, 32A, 32B)

We have a density-zero theorem (Theorem A', from 22A) proved via the Selberg sieve. We have a growing-K Borel-Cantelli framework (from 32A/32B) that converts density-zero into finiteness, provided the implied constant C(K) in Theorem A' grows at most polynomially in K. The Selberg sieve proof was written for FIXED F, and tracking C(K) through its steps is delicate (collision lemma, Mertens product, sieve dimension all depend on K).

32B's "repair strategy #1" suggested an alternative: reprove Theorem A' using the arithmetic large sieve instead of the Selberg sieve. The large sieve handles many excluded residue classes simultaneously and gives bounds that depend on LOCAL DENSITIES rather than the size of the excluded set. This should bypass the C(K) uniformity problem entirely.

This prompt asks you to carry out that reproof.

## The problem setup

### What Theorem A' says

For F = F_K (all pairs (alpha, s) with 4*alpha*s^2 <= K), define:

- m_{alpha,s} = 4*alpha*s (the modulus for pair (alpha, s))
- h_{alpha,s} = 4*alpha*s^2 (the shift for pair (alpha, s))
- delta(F_K) = Sum_{(alpha,s) in F_K} 1/phi(m_{alpha,s})

The "failure" event for prime P and pair (alpha, s): the integer N = P + h_{alpha,s} has NO prime factor q with q === -1 (mod m_{alpha,s}).

**Theorem A' (22A):** #{P <= x prime : P === 1 (mod 24), all pairs in F_K fail} << C(K) * x / (log x)^{1 + delta(F_K)}.

The original Selberg sieve proof leaves C(K) implicit. We need C(K) <= K^B for some absolute constant B. (Or even C(K) <= exp(c*(log K)^2), which is quasi-polynomial and still sufficient.)

### The character-kernel reformulation (from 14A, verified)

"All prime factors of N coprime to m land in a specific index-2 subgroup of (Z/mZ)*" is equivalent to: "there exists an odd quadratic character chi (mod m) with chi(-1) = -1 and chi(q) = +1 for every prime q | N with gcd(q, m) = 1."

So the failure event for pair (alpha, s) at prime P is:

exists chi (mod m_{alpha,s}), chi odd, chi(-1) = -1, such that chi(q) = +1 for ALL primes q | (P + h_{alpha,s}) with gcd(q, m_{alpha,s}) = 1.

### The key numbers

- K = 200: |F_K| = 74 pairs, delta = 4.7908, 49 distinct moduli
- K = 500: |F_K| ~ 190 pairs, delta ~ 6.55
- K = 1000: |F_K| ~ 410 pairs, delta ~ 8.5
- Growth: delta(F_K) ~ 0.18 * (log K)^2
- Critical K for finiteness: K*(x) = exp(2.357 * sqrt(log x / log log x))
- K*(10^6) = 223

### What we need

A version of Theorem A' where C(K) is EXPLICIT and at most polynomial in K (or quasi-polynomial). The large sieve is the natural tool because:

1. It handles MANY excluded residue classes simultaneously
2. Its constants depend on the TOTAL density of excluded classes, not their count
3. The Gallagher/Barban-Davenport-Halberstam version gives square-mean bounds that are naturally uniform

## What I need from you

### Task 1: State the large sieve inequality in our setting

(a) The multiplicative large sieve inequality (Gallagher 1968, or Montgomery-Vaughan 1973):

Sum_{q <= Q} Sum_{chi (mod q), chi != chi_0} |Sum_{n <= N} a_n chi(n)|^2 <= (N + Q^2) * Sum |a_n|^2.

State the version most relevant to our problem. We are summing over SPECIFIC characters chi (the odd quadratic characters with chi(-1) = -1) for SPECIFIC moduli m_{alpha,s}.

(b) The additive large sieve (dual formulation):

Sum_{q <= Q} Sum_{a (mod q)} |Sum_{n <= N, n === a (mod q)} a_n - (1/q) Sum a_n|^2 <= ...

Which formulation is better for our problem?

(c) Gallagher's larger sieve: for integers n <= N, if for each prime q in a set Q we exclude a set of residue classes A_q (mod q) with |A_q| residues excluded, then:

#{n <= N : n not in A_q (mod q) for all q in Q} <= N * Prod_{q in Q} (1 - |A_q|/q) * (1 + error)

where the error depends on Q and the structure of A_q. State this precisely.

### Task 2: Apply the large sieve to count failures

For each pair (alpha, s), define the "bad primes q" for that pair: primes q with q === -1 (mod m_{alpha,s}). The failure event is: P + h_{alpha,s} has NO bad prime factor.

(a) **Single-pair bound via large sieve:** For a single pair (alpha, s), bound:

#{P <= x prime, P === 1 (mod 24) : P + h has no prime factor q === -1 (mod m)}.

This is sieving the sequence {P + h : P <= x prime, P === 1 (mod 24)} to remove those with all prime factors in the "good" classes mod m. The density of "bad" primes among all primes <= z is 1/phi(m) (by Dirichlet/Mertens). So the Selberg sieve gives (log x)^{-1/phi(m)} and BFL gives (log x)^{-3/2}. What does the large sieve give?

(b) **Multi-pair bound via large sieve:** For ALL pairs in F_K failing simultaneously: the failure event is an INTERSECTION of |F_K| single-pair failure events. Each event excludes primes q in different arithmetic progressions (q === -1 mod m_{alpha,s}).

Can the large sieve bound this intersection? The key question: are the exclusion events for different pairs INDEPENDENT or correlated?

For large primes q, a single q satisfies q === -1 (mod m_i) for AT MOST one modulus m_i (by the collision lemma from 22A: for q > max(m_i)^2, the congruences are distinct). So the exclusion conditions decouple for large q. Does the large sieve exploit this?

(c) **The large sieve approach to the product V(z):** The Mertens product V(z) = Prod (1 - rho(q)/q) over sieve primes q is the key quantity. In the Selberg sieve, the constant C(K) comes from the gap between the actual sieve output and the heuristic V(z).

In the large sieve: the bound is of the form #{failures} <= (N + Q^2) / (Sum of sieve weights). The denominator grows as V(z)^{-1} without any mysterious constant. Is this right?

### Task 3: The Barban-Davenport-Halberstam theorem

The BDH theorem (Barban 1964, Davenport-Halberstam 1966) says: for "most" moduli q <= Q, the distribution of primes in arithmetic progressions is close to the expected value, with SQUARE-MEAN control.

(a) State BDH precisely:

Sum_{q <= Q} Sum_{a (mod q), gcd(a,q)=1} |pi(x; q, a) - li(x)/phi(q)|^2 << x^2 / (log x)^A

for Q <= x^{1/2} / (log x)^B, for any A (with B depending on A).

(b) How does BDH apply to our problem? We need: for each pair (alpha, s) and prime P, the integer P + h_{alpha,s} either has or doesn't have a prime factor q === -1 (mod m). The distribution of these prime factors is controlled by primes in arithmetic progressions mod m.

(c) BDH gives UNIFORM control over moduli q up to Q. In our setting, the moduli m_{alpha,s} range up to K. As K grows, we have MORE moduli to handle. BDH handles this naturally because it sums over ALL moduli up to Q.

(d) Does the BDH constant depend on the NUMBER of moduli we care about? Or is it uniform? This is the central question. If BDH gives a bound with an ABSOLUTE constant (independent of |F_K|), then C(K) = O(1) and we're done.

### Task 4: Gallagher's hybrid large sieve

Gallagher (1971, "A large sieve density estimate near sigma = 1") combines the large sieve with character sum estimates to give density results for primes avoiding prescribed residue classes.

(a) State Gallagher's result. For a set S of moduli, define the set of primes P <= x that avoid certain residue classes mod each m in S. What bound does Gallagher give on |{P <= x : P avoids all classes}|?

(b) Apply to our setting: S = {m_{alpha,s} : (alpha,s) in F_K}, and the avoided classes are {-1 mod m}. Gallagher's result should give:

#{P <= x : for all m in S, P + h_m has no prime factor === -1 (mod m)} <= ???

(c) Does Gallagher's constant depend on |S| (the number of moduli)? On Sum 1/phi(m) (our delta)? Or is it absolute?

(d) If the constant depends on |S| polynomially: what is the polynomial degree?

### Task 5: Direct large sieve for our sieve product

Here is a direct approach, bypassing the general theorems. Consider:

(a) Define the sifting set B = {P <= x prime, P === 1 (mod 24)}. For each prime q with q === -1 (mod m) for some m in moduli(F_K), define:

A_q = {P in B : q | (P + h_{alpha,s})} = {P in B : P === -h_{alpha,s} (mod q)}.

This is an AP condition. By PNT in APs: |A_q| = |B|/q + O(x^{1/2} log x) (GRH) or on average by BV.

(b) The sifted set (failures) is S = {P in B : P not in A_q for any sieve prime q}. The large sieve gives:

|S| <= |B| * Prod_{q} (1 - 1/q) * (1 + R)

where R is the large sieve remainder. Compute Prod_{q} (1 - 1/q) over all relevant primes q. This is the Mertens product, giving (log x)^{-delta(F_K)}. The key question: what is R?

(c) In the large sieve formulation (Montgomery-Vaughan), the remainder R satisfies:

R <= Sum_{d > D} |r_d| / g(d)

where r_d is the sieve remainder for modulus d and g(d) is the local density. The large sieve controls Sum |r_d|^2 rather than Sum |r_d|, which is why it gives BETTER uniformity.

(d) Compute the large sieve remainder R as a function of K. Specifically: does R depend on |F_K|, on delta(F_K), on the number of distinct moduli, or is it independent of K?

(e) The PUNCHLINE: if R is independent of K (or at most polylog in K), then:

#{failures} <= (1 + polylog(K)) * x / (log x)^{1 + delta(F_K)}

giving C(K) = polylog(K). This is MUCH better than needed for the growing-K argument.

### Task 6: Comparison and conclusion

(a) Compare the bounds from:
- Selberg sieve (original Theorem A' proof)
- Multiplicative large sieve
- BDH
- Gallagher's hybrid
- Direct large sieve (Task 5)

Which gives the best uniformity in K?

(b) For whichever approach gives the best C(K): state the result as a clean theorem.

**Desired form:**

Theorem A'' (Uniform version): For all K >= 2 and x >= x_0:

#{P <= x prime : P === 1 (mod 24), all pairs in F_K fail} <= C_0 * K^{B_0} * x / (log x)^{1 + delta(F_K)}

with explicit C_0, B_0, x_0.

(c) If NO approach gives polynomial C(K): identify the precise obstruction. Is it:
- The sieve dimension growing?
- The number of distinct moduli growing?
- The Mertens product accumulating errors?
- The BV level of distribution being insufficient?
- Something else?

(d) State the Lean axiom:

```
axiom uniform_density_bound (K : Nat) (x : Real) (hK : K >= K_0) (hx : x >= x_0) :
  failure_count K x <= C_0 * K ^ B_0 * x / (Real.log x) ^ (1 + delta K)
```

with all constants filled in.

### Task 7: The nuclear option (if needed)

If BOTH the Selberg sieve and the large sieve fail to give polynomial C(K), consider:

(a) **Weaken the goal:** Instead of ALL pairs failing simultaneously, bound the probability that a RANDOM pair fails. This gives a per-pair bound without the multi-pair intersection problem. Then show that ENOUGH random pairs are checked that at least one succeeds with high probability.

(b) **Use the character-kernel directly:** The failure event is that chi(q) = +1 for all q | N, for some specific character chi. This is equivalent to N being a quadratic residue mod m (in a specific sense). The large sieve for quadratic characters (the Polya-Vinogradov or Burgess family) gives bounds on how often this can happen.

(c) **Heath-Brown's quadratic large sieve:** Heath-Brown (1995, "The largest prime factor of the integers in an interval") used a large sieve for quadratic characters to bound the number of integers in an interval whose prime factors all satisfy a quadratic residue condition. This is EXACTLY our problem.

State Heath-Brown's result and apply it.

## What a successful response looks like

- A reproof of Theorem A' using the large sieve (or variant) where C(K) is EXPLICIT
- Clean answer: "The large sieve gives C(K) = [formula] because [reason]"
- If C(K) is independent of K: celebrate and state the theorem
- If C(K) = polylog(K): state it and verify summability
- If C(K) = poly(K): state the degree and verify summability
- If the large sieve ALSO gives exponential C(K): explain why and identify what's fundamentally hard
- Comparison of at least 3 approaches (Selberg, large sieve, BDH)
- Lean axiom with all constants
- If Heath-Brown's quadratic large sieve applies: state the application explicitly

## Important notes

- Use the CORRECTED D.6 formula: x = alpha*s*t, y = alpha*r*s*P, z = alpha*r*t*P.
- Do NOT rely on Dyachenko's paper.
- The sieve dimension is kappa = delta(F), NOT |F|. When applying the large sieve, the relevant quantity is the TOTAL density of excluded classes, not the NUMBER of excluded classes. This is WHY the large sieve should give better uniformity than the Selberg sieve.
- Key distinction: the Selberg sieve optimizes POINTWISE (giving the best bound for each modulus separately), while the large sieve optimizes in the MEAN (giving the best bound averaged over moduli). For uniformity in K, mean-value bounds are likely better.
- Key references: Montgomery-Vaughan "Multiplicative Number Theory I" (Chapter 7), Gallagher (1968 "The large sieve"), Bombieri (1974 "Le grand crible"), Iwaniec-Kowalski (Chapter 7), Heath-Brown (1995 "Largest prime factor of integers in an interval"), Tao 254A supplementary notes on the large sieve, Ford (2008 Annals).
- The BDH constant is ABSOLUTE (does not depend on which moduli are selected). This is the key structural advantage over the Selberg sieve, where the constant depends on the sieve dimension. Verify this claim or correct it.
- For computational context: K*(10^6) = 223 and the current computational certificate covers P < 10^6. If C(K) <= K^{10}, the growing-K argument still gives a tail bound far below 1, so even a crude polynomial suffices.
