# GPT Prompt 33A: Uniformity of Theorem A' in the Budget K (Selberg Sieve Constant Tracking)

## Context (follow-up to prompts 22A, 25A, 32A, 32B)

Theorem A' (from 22A, independently verified) gives density zero for the set of primes P where all (alpha, s) pairs in a FIXED finite budget F fail to produce an Erdos-Straus decomposition. The growing-K Borel-Cantelli argument (from 32A/32B, verified) shows that if the budget K(P) grows as K*(P) = exp(2.357 * sqrt(log P / log log P)), the failure sum converges and only finitely many primes can fail. But there is ONE gap: the implied constant C(K) in Theorem A' depends on the set F, and when F = F_K grows with K, C(K) might grow too fast and destroy convergence.

This prompt asks you to determine the K-dependence of C(K) by tracking every constant through the proof.

**This is the single remaining obstruction to closing the Erdos-Straus conjecture in our formalization.**

## The established results (all verified)

### Theorem A' (from 22A, unconditional)

**Statement:** Let F be a finite set of pairs (alpha_i, s_i). Define delta(F) = Sum_{(alpha,s) in F} 1/phi(4*alpha*s). Then:

#{P <= x prime : P === 1 (mod 24), all pairs in F fail} << x / (log x)^{1 + delta(F)}.

**The full proof (from 22A/25A, verified in detail):**

Step 1 (Setup): Sifting set A = {n <= X : n === 1 (mod 24)}, |A| = X/24 + O(1). For each pair (alpha,s) in F, define h_{alpha,s} = 4*alpha*s^2, m_{alpha,s} = 4*alpha*s. The "forbidden" event for pair (alpha,s) is: n + h_{alpha,s} has NO prime factor q with q === -1 (mod m_{alpha,s}).

Step 2 (Local densities): For each prime q === -1 (mod m_{alpha,s}) with gcd(q, 24) = 1, the set {n in A : q | (n + h_{alpha,s})} has density 1/q relative to A. Define Omega_q = {(alpha,s) in F : q === -1 (mod m_{alpha,s})}, and rho(q) = |Omega_q|.

Step 3 (Collision lemma): For q not in a finite exceptional set E_F (depending only on F), the residues {-h_{alpha,s} (mod q)} for (alpha,s) in Omega_q are all distinct, so there are rho(q) genuinely distinct forbidden classes mod q.

Step 4 (Mertens estimate): By Mertens' theorem in arithmetic progressions:

Sum_{q <= z, q === -1 (mod m)} 1/q = (1/phi(m)) * log log z + C_m + O(1/log z).

The sieve product V(z) = Prod_{q <= z, q not in E_F} (1 - rho(q)/q) satisfies V(z) << 1/(log z)^{delta(F)}.

Step 5 (Conclusion): Selberg upper-bound sieve gives |S(A,z)| << |A| * V(z), so:

#{n <= X : n === 1 (mod 24), all pairs fail} << X / (log X)^{delta(F)}.

For primes, replace A with primes via Bombieri-Vinogradov to get exponent 1 + delta(F).

### The growing-K argument (from 32A/32B, verified)

For P in dyadic block (2^n, 2^{n+1}], use fixed budget K_n = K(2^n) where K(x) = exp(A * sqrt(log x / log log x)) with A > 1/sqrt(0.18) = 2.357.

The failure count in this block is bounded by Theorem A':

Fail_n << C(K_n) * 2^n / (log 2^n)^{1 + delta(K_n)}.

The dyadic sum Sum_n Fail_n converges iff C(K_n) does not grow too fast. Specifically:

- If C(K) <= K^B for some B, the polynomial factor K_n^B is subexponential in n (since K_n = exp(A*sqrt(n log 2 / log(n log 2))))), while the denominator (n log 2)^{1+delta(K_n)} is super-polynomial (since delta(K_n) ~ 0.18*(A*sqrt(n log 2/log(n log 2)))^2 ~ 0.18*A^2*n*log 2/log(n log 2) >> n/log n). So the sum converges.

- If C(K) >= exp(cK), then C(K_n) itself grows super-polynomially, potentially overwhelming the denominator. The argument fails.

**VERIFIED TAIL BOUNDS (with C(K) = 1):**
- A = 3: tail from 10^6 is ~ 2e-5
- A = 4: tail ~ 2e-13
- A = 5: tail ~ 2e-23

These have enormous margin. Even C(K) = K^{10} would be easily absorbed.

### 32B's sieve anatomy observations (verified)

32B identified three key structural points about C(K):

1. **Sieve dimension is kappa = delta(F), not |F|.** The Selberg sieve constant depends on the dimension parameter kappa, which for our sieve is delta(F) ~ 0.18*(log K)^2. This grows MUCH more slowly than |F| ~ 0.41*K. An analysis that treats the constant as depending on |F| would be too pessimistic.

2. **Collision lemma primes are bounded.** E_F consists of primes q <= K^{O(1)} where residue collisions can occur. The Mertens product over these exceptional primes is Prod_{q in E_F} q/(q-1) ~ e^gamma * log(max E_F) ~ polylog(K). This is benign.

3. **BV level of distribution is safe.** The sieve moduli are bounded by 24*D^2 where D = X^{1/4-eps/2}. Since K(x) = x^{o(1)}, all moduli m_{alpha,s} = 4*alpha*s <= K are well within the BV range.

## What I need from you

### Task 1: Track the Selberg sieve constant in Steps 1-5

Go through each step of the Theorem A' proof above and make the implied constant EXPLICIT as a function of K (where F = F_K = all pairs with 4*alpha*s^2 <= K).

(a) **Step 2 (Local densities):** The density of {n in A : q | (n + h)} in A is 1/q + O(1/|A|). The error O(1/|A|) contributes O(1) per prime q, summed over all sieve primes. When we have |F_K| ~ 0.41*K pairs, how does the total remainder term from local density errors depend on K?

(b) **Step 3 (Collision lemma):** The exceptional set E_F depends on F. For F = F_K:
- What is |E_{F_K}| as a function of K? Give an upper bound.
- What is max(E_{F_K}) as a function of K? (All exceptional primes q satisfy q <= ??? in terms of K.)
- The factor contributed by primes in E_F to the sieve product: Prod_{q in E_F} (1 - rho(q)/q)^{-1}. This is a correction factor that multiplies the main term. Bound it as a function of K.

(c) **Step 4 (Mertens estimate):** The Mertens estimate gives V(z) = C_F / (log z)^{delta(F)} where C_F is a constant depending on F. This constant comes from:

C_F = Prod_{pairs (alpha,s) in F} Prod_{q <= z, q === -1 (mod m)} (1 - 1/q) * (log z)^{1/phi(m)}.

By Mertens' theorem, each inner product converges to a constant depending only on the modulus m. So C_F = Prod_{pairs} c_{m_{alpha,s}} where c_m is Mertens' constant for the AP q === -1 (mod m).

- How does Prod_{pairs in F_K} c_m grow with K? Is it polynomial? Exponential?
- Note: many pairs share the same modulus m, so this is NOT simply c_m raised to the |F|-th power. Group the pairs by modulus and compute.

(d) **Step 5 (Conclusion):** The Selberg sieve upper bound is:

S(A, z) <= |A| / (Sum_{d <= D} lambda_d^2 / g(d))

where lambda_d are the Selberg weights and g(d) is the multiplicative density function. The denominator is >> V(z)^{-1} * correction_terms. What are these correction terms as a function of K?

(e) **Bombieri-Vinogradov step:** When restricting to primes via BV, the sieve level D and remainder terms must accommodate moduli up to 24*K^2 (since the moduli m_{alpha,s} up to K contribute to the sieve). Is 24*K^2 safely within the BV range X^{1/2-eps}? For K = K(x) = exp(2.357*sqrt(log x/log log x)) = x^{o(1)}, yes. But quantify the loss.

### Task 2: Assemble the constant C(K)

Combining the outputs of Task 1:

(a) Write C(K) = (collision lemma factor) * (Mertens product factor) * (Selberg sieve overhead) * (BV remainder absorption).

(b) Give an EXPLICIT upper bound: C(K) <= ??? (as a function of K).

(c) Is C(K) polynomial in K? I.e., does C(K) <= K^B for some absolute B? If so, state B (or an upper bound on B).

(d) Is C(K) polynomial in delta(F_K) = 0.18*(log K)^2? This is a WEAKER requirement that still suffices for convergence.

(e) Could C(K) be exponential in K? If so, identify which step in Task 1 contributes the exponential growth and whether it can be avoided.

### Task 3: The Mertens product in detail

This is the most likely source of large C(K). The Mertens constant for the AP q === -1 (mod m) is:

c_m = Prod_{q === -1 (mod m)} (1 - 1/q) * (log z)^{1/phi(m)}   [as z -> infinity]

For F_K, the product over ALL pairs is:

C_{Mertens}(K) = Prod_{(alpha,s) in F_K} c_{m_{alpha,s}}.

(a) Group the pairs by their modulus m = 4*alpha*s. For each m, let n(m, K) = number of pairs in F_K with modulus m. Then:

C_{Mertens}(K) = Prod_{m} c_m^{n(m,K)}.

Wait: this is WRONG. Each pair contributes INDEPENDENTLY to the sieve, but pairs with the same modulus m contribute the SAME sieve condition (they exclude the same primes q === -1 mod m). So pairs sharing a modulus do NOT multiply the Mertens factor. Clarify this.

(b) The CORRECT grouping: the sieve excludes primes q with q === -1 (mod m) for at least one pair (alpha,s) in F_K. Different pairs with different moduli m contribute DIFFERENT sieve conditions. So the Mertens product is:

V(z) = Prod_{m in moduli(F_K)} Prod_{q <= z, q === -1 (mod m)} (1 - 1/q).

The number of DISTINCT moduli in F_K is the number of distinct values of m = 4*alpha*s for (alpha,s) in F_K. How does this grow with K?

(c) Each modulus m <= K contributes a factor to V(z) that behaves like (log z)^{-1/phi(m)}. The product of correction constants is bounded. But the number of moduli grows. Give the explicit bound on the product of all correction constants as a function of K.

(d) KEY QUESTION: is the product Prod_{m in moduli(F_K)} c_m bounded by a polynomial in K? Or does it grow exponentially?

### Task 4: Alternative: exponential in kappa, not K

32B suggested that the sieve constant might depend exponentially on the sieve dimension kappa = delta(F_K) ~ 0.18*(log K)^2, rather than on K itself or on |F_K|. If so:

(a) C(K) ~ exp(O(kappa)) = exp(O((log K)^2)) = K^{O(log K)}.

This is QUASI-POLYNOMIAL in K: faster than any polynomial but slower than any exponential exp(cK).

(b) Does C(K) = K^{O(log K)} still allow the dyadic sum to converge?

Check: C(K_n) = K_n^{O(log K_n)}. With K_n = exp(A*sqrt(n*log 2/log(n*log 2))):

log C(K_n) = O(log K_n * log K_n) = O(A^2 * n * log 2 / log(n*log 2)).

The denominator exponent is delta(K_n) * log(n*log 2) ~ 0.18*A^2*n*log 2/log(n*log 2) * log(n*log 2) = 0.18*A^2*n*log 2.

So numerator growth log C(K_n) ~ A^2*n/log n is dominated by denominator growth ~ A^2*n. The sum still converges.

IS THIS CORRECT? Verify this calculation and state the conclusion clearly.

(c) What if C(K) = exp(c*kappa^{1+eps}) for some eps > 0? At what growth rate of C(K) does the argument break down?

### Task 5: Ford's sieve theorem and varying dimension

The standard Selberg sieve upper bound (as in Halberstam-Richert "Sieve Methods" or Ford's survey "The distribution of integers with a divisor in a given interval") gives:

S(A, z) <= (1 + epsilon) * |A| * V(z) * (1 + R)

where the implied constant and remainder R depend on the sieve dimension kappa and the sieve support level D.

(a) In Halberstam-Richert, Theorem 5.1 (or equivalent), the upper bound is:

S(A, z) <= X * V(z) * {F(s) + O((log D)^{-1/3})}

where F(s) is the Selberg sieve function (F(s) = 2e^gamma / s for s >= 2 in 1-dimensional sieve), s = log D / log z, and the O-term depends on the sieve dimension kappa. State how the O-term depends on kappa.

(b) For our sieve: the dimension kappa is not fixed; it is delta(F_K) which grows with K. The standard theorems are proved for BOUNDED kappa. What happens when kappa grows?

- Does the Selberg sieve still give an upper bound of the correct order of magnitude?
- Does the sieve function F(s) change with kappa?
- Is there a kappa-dependent loss factor?

(c) Reference: Ford, "The distribution of integers with a divisor in a given interval" (Annals of Math, 2008). Ford's Theorem 2.4 handles varying sieve dimension. What does it give in our setting?

(d) Alternative reference: Tao, "254A Supplementary Notes: The Large Sieve" or "A remark on partial sums involving the Mobius function." Does Tao's large sieve formulation handle varying dimension more naturally?

### Task 6: State the result for Lean

Regardless of the exact growth rate:

(a) If C(K) <= K^B: state the Lean axiom precisely.

```
axiom uniform_theorem_A_prime (K : Nat) (x : Real) (hK : K >= K_0) (hx : x >= x_0) :
  failure_count K x <= C_0 * K ^ B_0 * x / (Real.log x) ^ (1 + delta K)
```

What are the BEST values of C_0, B_0, K_0, x_0 you can give?

(b) If C(K) = K^{O(log K)}: the axiom needs a different form. State it.

(c) If C(K) grows exponentially in K: state that the Selberg-sieve approach to uniformity FAILS, and identify what alternative (large sieve? different sieve?) should be used instead.

## What a successful response looks like

- Explicit tracking of every K-dependent factor in the Theorem A' proof
- A clean answer: "C(K) grows as [polynomial / quasi-polynomial / exponential] in K because [specific factor]"
- If polynomial: explicit B (or bound on B)
- If quasi-polynomial: verification that the dyadic sum still converges
- If exponential: identification of which proof step causes the blowup and whether it can be repaired
- The Mertens product computation grouped by distinct moduli, not by pairs
- Ford's theorem applied with varying dimension, or an explanation of why it doesn't apply
- Lean axiom statement with all quantifiers filled in

## Important notes

- Use the CORRECTED D.6 formula: x = alpha*s*t, y = alpha*r*s*P, z = alpha*r*t*P.
- Do NOT rely on Dyachenko's paper.
- The sieve dimension is kappa = delta(F), NOT |F|. Do not conflate these.
- When grouping the Mertens product, be careful: pairs with the same modulus m = 4*alpha*s contribute to the SAME sieve primes. The sieve dimension delta(F) = Sum 1/phi(m) counts with multiplicity over PAIRS, but the Mertens product groups by MODULI. These are different.
- Key references: Halberstam-Richert "Sieve Methods" (Theorem 5.1 and Chapter 7), Ford "Distribution of integers with a divisor in a given interval" (Annals 2008, Theorem 2.4), Iwaniec-Kowalski "Analytic Number Theory" (Chapter 6 on Selberg sieve), Tao 254A notes on large sieve.
- The BV level of distribution is NOT a concern since K(x) = x^{o(1)}. Do not spend time on this unless you find a genuine obstruction.
- This is THE critical question for our project. If C(K) is polynomial, the Erdos-Straus conjecture is proved (modulo computational verification below certBound = 10^6, already done). If C(K) is exponential, we need a fundamentally different approach.
