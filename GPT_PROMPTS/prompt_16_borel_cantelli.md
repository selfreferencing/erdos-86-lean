# GPT Prompt 16: Borel-Cantelli and Independence of Shifted Quadratic Values

## Background

We are trying to prove the Erdos-Straus conjecture for primes P === 1 (mod 24). Through extensive analysis, we've reduced this to:

**For every prime P === 1 (mod 24), there exist positive integers alpha and s such that P + 4*alpha*s^2 has a divisor d with d === -1 (mod 4*alpha*s).**

We are aware this is equivalent to the Erdos-Straus conjecture for the hard residue class. We have proven computationally that this holds for all P < 10^7.

## This prompt focuses on one specific approach

We believe the most promising path to a conditional or unconditional result is a **Borel-Cantelli / independence argument** showing that only finitely many primes fail. Here is the detailed setup.

## The probabilistic framework

### Individual failure probabilities

For fixed (alpha, s), define:

E_{alpha,s}(P) = event that P + 4*alpha*s^2 has NO divisor === -1 (mod 4*alpha*s).

For alpha = 1, s = 1: E_{1,1}(P) = {P + 4 has all prime factors === 1 (mod 4)} = {P + 4 is a sum of two squares}.

By the Landau-Ramanujan theorem: #{n <= X : n is a sum of two squares} ~ C * X / sqrt(log X), where C = 1/(sqrt(2)) * prod_{p === 3 (mod 4)} (1 - 1/p^2)^{-1/2} approx 0.7642...

So for a "random" number N near P: Pr[N is a sum of two squares] ~ C / sqrt(log P).

Empirically: 46.7% of primes P === 1 (mod 24) up to 10^7 have E_{1,1}(P) true (P + 4 is a sum of two squares). The Landau-Ramanujan density at N = 10^7 gives C/sqrt(log 10^7) ~ 0.764/sqrt(16.1) ~ 0.190. The discrepancy (0.467 vs 0.190) is because P + 4 is constrained to be === 5 (mod 8), which biases toward sums of two squares.

For alpha = 1, s = 2: E_{1,2}(P) = {P + 16 has no divisor === 7 (mod 8)}. The analogous density involves numbers whose prime factors all avoid certain residue classes mod 8.

### Joint failure probabilities (empirical)

Using all (alpha, s) with 4*alpha*s^2 <= K:

```
K=   4:  1 pair   -> 46.7% fail
K=   8:  2 pairs  -> 16.9% fail  (ratio: 0.362)
K=  16:  5 pairs  -> 4.8% fail   (ratio: 0.284)
K=  32: 10 pairs  -> 0.78% fail  (ratio: 0.163)
K=  64: 22 pairs  -> 0.095% fail (ratio: 0.122)
K= 100: 35 pairs  -> 0.025% fail (ratio: 0.263)
K= 128: 46 pairs  -> 0.006% fail (ratio: 0.240)
K= 200: 74 pairs  -> 0.000% fail (zero in 82,887 primes up to 10M)
```

The decay is roughly geometric with ratio ~0.3 per additional pair. This suggests approximate independence.

## The Borel-Cantelli argument (what needs to be made rigorous)

### Step 1: Define the failure event

For a prime P, define:

F_K(P) = AND_{(alpha,s) : 4*alpha*s^2 <= K} E_{alpha,s}(P)

This is the event that ALL (alpha, s) pairs with budget <= K fail simultaneously.

### Step 2: Bound Pr[F_K(P)]

**If the events E_{alpha,s}(P) were independent**, then:

Pr[F_K(P)] = prod Pr[E_{alpha,s}(P)] ~ prod (C_{alpha,s} / sqrt(log P)) = C^{N(K)} / (log P)^{N(K)/2}

where N(K) = #{(alpha,s) : 4*alpha*s^2 <= K} and C_{alpha,s} depends on the specific congruence conditions.

For K = 200, N(K) = 74, so Pr[F_{200}(P)] ~ C^{74} / (log P)^{37}.

For P >= 10^6, log P >= 13.8, so (log P)^{37} >= 10^{42}. Even with C^{74} being substantial, this is astronomically small.

### Step 3: Sum over primes (Borel-Cantelli)

Sum_{P prime, P >= 10^6} Pr[F_K(P)] <= Sum_{P >= 10^6} C^{N(K)} / (log P)^{N(K)/2}

By the prime number theorem, the number of primes up to X is ~X/log X. So:

Sum_{P <= X} 1/(log P)^{N(K)/2} ~ integral from 10^6 to X of dt / ((log t)^{N(K)/2} * log t)
                                   = integral of dt / (log t)^{N(K)/2 + 1}

For N(K)/2 + 1 > 1, i.e., N(K) >= 2, this integral CONVERGES as X -> infinity!

So by Borel-Cantelli: **at most finitely many primes P have F_K(P) true**, i.e., at most finitely many primes fail with budget K.

### Step 4: The gap - independence

The above argument assumes the events E_{alpha,s}(P) are independent. They are NOT exactly independent because they all involve the same prime P. However:

- E_{alpha_1, s_1}(P) depends on the prime factorization of P + 4*alpha_1*s_1^2
- E_{alpha_2, s_2}(P) depends on the prime factorization of P + 4*alpha_2*s_2^2
- These are DIFFERENT numbers (unless 4*alpha_1*s_1^2 = 4*alpha_2*s_2^2)

The correlation between the prime factorizations of N and N + h (for fixed h) is a deep topic in analytic number theory, related to:

- **Hardy-Littlewood conjecture** (prime patterns)
- **Chowla's conjecture** (Liouville function correlations)
- **Elliott's conjecture** (multiplicative function correlations)

## What I need proven (in decreasing order of ambition)

### Level 1 (full result): Independence with explicit error

**Prove:** For K = 200 (or some explicit K), and for all primes P >= 10^6 with P === 1 (mod 24):

Pr[F_K(P)] <= C / (log P)^A for some A > 1.

This doesn't require FULL independence. It only requires that the joint probability decays faster than 1/P, so that Borel-Cantelli applies.

**Possible approach:** Use the large sieve inequality. For each (alpha, s), the set of primes P where E_{alpha,s}(P) holds is determined by local conditions (P mod q for various primes q). The large sieve gives:

Sum_{P <= X} prod_{i=1}^{k} 1_{E_i(P)} <= (X + Q^2) / L

where Q is related to the moduli and L is related to the number of "forbidden" residues. If Q is small relative to X, this gives the desired bound.

### Level 2 (conditional): Under GRH or Elliott-Halberstam

**Prove (under GRH):** Pr[F_K(P)] << 1/(log P)^A for all P >= 10^6.

GRH gives strong control over the distribution of primes in arithmetic progressions, which controls the distribution of prime factors of P + 4*alpha*s^2 in congruence classes. Under GRH, the error terms in the Chebotarev density theorem are O(sqrt(X) log X), which might suffice.

The Elliott-Halberstam conjecture (that the Bombieri-Vinogradov theorem holds with exponent 1 instead of 1/2) would give even stronger results.

### Level 3 (almost all): Density zero exceptional set

**Prove:** #{P <= X prime, P === 1 (mod 24), F_K(P)} = o(pi(X; 24, 1)) as X -> infinity.

In words: the set of primes where budget K fails has density zero among primes === 1 (mod 24).

This is weaker than Levels 1-2 but still useful: combined with extended computation (checking all primes up to 10^9, say), it would show ES holds for all P <= 10^9 and for a density-one subset of all primes.

**This should follow from the Erdos-Kac theorem.** The Erdos-Kac theorem says that omega(n) (number of distinct prime factors) has approximately normal distribution with mean log log n and standard deviation sqrt(log log n). The condition "all prime factors === 1 (mod 4)" becomes increasingly restrictive as the number of prime factors grows. For typical n near P, omega(n) ~ log log P ~ 3.4 for P ~ 10^7, and the probability that ALL of them are === 1 (mod 4) is roughly (1/2)^{omega(n)} ~ (1/2)^{3.4} ~ 0.09.

### Level 4 (explicit finite check): Effective bound on exceptions

**Prove:** There are at most N_0 primes P === 1 (mod 24) with F_K(P), where N_0 is an explicitly computable number.

This is the most practically useful: if N_0 is small enough, we can check all exceptions computationally.

## Critical technical questions

1. **What is the correct model for the correlation between omega(P + a) and omega(P + b) for distinct shifts a, b?** The Erdos-Kac theorem gives the marginal distribution of each, but what about the joint distribution?

2. **Does the Barban-Davenport-Halberstam theorem** give sufficient control on the average of multiplicative functions over shifted primes?

3. **Is Hildebrand's work on smooth numbers in short intervals** relevant? The condition "all prime factors in a specific class" is related to smoothness.

4. **Can the Selberg sieve** be adapted to give a LOWER bound on the number of (alpha, s) pairs that work for a given P? The Selberg sieve is usually used for upper bounds, but the Selberg-Delange method gives asymptotics for sums of multiplicative functions.

5. **The key independence result we need:** For FIXED P, are the events "P + a_i has all prime factors in class C_i" (for distinct shifts a_1, ..., a_k and possibly different classes C_1, ..., C_k) approximately independent? Is this known? Under what conditions?

## Specific references to investigate

- Granville & Soundararajan, "Multiplicative number theory: the pretentious approach" - may have relevant correlation estimates
- Matomaki & Radziwill (2016), "Multiplicative functions in short intervals" - breakthrough on correlations
- Tao (2016), "The logarithmically averaged Chowla conjecture" - partial results on multiplicative correlations
- Green & Tao, "Linear equations in primes" - may give relevant equidistribution
- Fouvry, Kowalski & Michel, "Algebraic twists of modular forms" - trace functions over shifted primes

## Constraints

- A proof for ALL primes P >= 10^6 is ideal. "All but finitely many" is acceptable if the finite set is computable.
- Conditional results (under GRH, Elliott-Halberstam, Chowla) are acceptable if clearly stated.
- The argument must be rigorous, not heuristic.
- We are formalizing in Lean 4, but the Lean formalization of the analytic argument can wait - we first need the mathematical argument.
