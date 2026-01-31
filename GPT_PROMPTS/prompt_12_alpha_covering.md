# GPT Prompt 12: Alpha-Varying Covering System for Erdos-Straus

## The state of knowledge (exhaustive summary)

We are trying to prove the Erdos-Straus conjecture for primes P === 1 (mod 24). After extensive analysis, we know this reduces to exactly one statement:

**Target theorem.** For every prime P === 1 (mod 24), there exist positive integers alpha, s, r such that M := 4*alpha*s*r - 1 divides P + 4*alpha*s^2.

This is Dyachenko's Lemma D.6 parametrization. Given such (alpha, s, r), set d = alpha*s^2, A = alpha*s*(m*r - s) where m = (P + 4*alpha*s^2)/M. Then d | A^2 and (4A-P) | (d+A), which gives an ED2 solution to 4/P = 1/A + 1/(bP) + 1/(cP).

## The character rigidity obstruction (proven)

For alpha = 1 and any prime p | M where M = 4sr - 1:

(-4s^2 / p) = (-1/p)

This means the covered residue class a = -4s^2 (mod M) is forced to be a QNR mod every prime factor p === 3 (mod 4) of M. But M === 3 (mod 4) implies M has at least one such factor.

Consequence: for any FINITE set of (s, r) triples with alpha = 1, the arithmetic progression P === 1 (mod 24 * prod(p : p === 3 mod 4, p | some M_i)) contains infinitely many uncovered primes (by Dirichlet). No finite alpha=1 covering system exists.

## What alpha > 1 buys you

For general alpha, the character becomes:

(-4*alpha*s^2 / p) = (-alpha / p)

So:
- alpha = 1: need (-1/p) = -1 for p === 3 (mod 4). ALWAYS a QNR. Can only match P that are QNR mod p.
- alpha = 2: need (-2/p). By quadratic reciprocity, (-2/p) depends on p mod 8.
- alpha = 3: need (-3/p). Depends on p mod 12.
- alpha = 5: need (-5/p). Depends on p mod 20.
- alpha = 6: need (-6/p). Depends on p mod 24.
- alpha = q (prime): need (-q/p). Depends on p mod 4q by QR.

Key insight: DIFFERENT alpha values impose DIFFERENT character constraints. A prime P that is a QR mod every small prime (making alpha=1 fail) might be a QNR mod some primes for alpha=2, because (-2/p) has a different pattern than (-1/p).

## The precise combinatorial question

For each prime p === 3 (mod 4), define the "bad set" B_alpha(p) as the set of residues x mod p such that (x/p) = (-alpha/p). A prime P is "covered by alpha" at prime p if P mod p is in B_alpha(p) for SOME modulus M divisible by p that arises from some (alpha, s, r) triple.

Actually, let me state this more carefully.

For a prime P to be covered by a triple (alpha, s, r), we need M | (P + 4*alpha*s^2) where M = 4*alpha*s*r - 1. This means P === -4*alpha*s^2 (mod M).

For each prime factor p of M, this forces P === -4*alpha*s^2 (mod p), and the quadratic character of -4*alpha*s^2 mod p is (-alpha/p) (since -4s^2 has character (-1/p) * (2s/p)^2 = (-1/p), wait let me redo this).

Actually: -4*alpha*s^2 = -1 * 4 * alpha * s^2. Since 4 and s^2 are perfect squares, (-4*alpha*s^2 / p) = (-alpha / p). So the character is (-alpha/p).

For P to satisfy P === -4*alpha*s^2 (mod p), we need (P/p) = (-alpha/p).

Now, fix a small prime p === 3 (mod 4). The obstruction for alpha=1 was that (-1/p) = -1, so P must be a QNR mod p. But P === 1 (mod p) is a QR, so it can't be covered.

For alpha=2: (-2/p) depends on p. If p === 3 or 5 (mod 8), then (-2/p) = 1, so we need P to be a QR mod p. Now P === 1 (mod p) IS a QR, so alpha=2 CAN cover P === 1 (mod p) when p === 3 or 5 (mod 8).

THIS IS THE KEY. Alpha=2 can cover some residues that alpha=1 cannot!

## The question I need answered

### Part 1: For each small prime p === 3 (mod 4), which alpha values can cover P === 1 (mod p)?

We need (-alpha/p) = (1/p) = 1, i.e., -alpha must be a QR mod p.

- p = 3: need -alpha === QR mod 3. QRs mod 3 are {1}. So -alpha === 1, alpha === 2 (mod 3). Works for alpha = 2, 5, 8, 11, ...
- p = 7: need -alpha === QR mod 7. QRs mod 7 are {1, 2, 4}. So -alpha in {1,2,4}, alpha in {3, 5, 6} (mod 7). Works for alpha = 3, 5, 6, 10, 12, 13, ...
- p = 11: need -alpha === QR mod 11. QRs mod 11 are {1, 3, 4, 5, 9}. So -alpha in {1,3,4,5,9}, alpha in {2, 6, 7, 8, 10} (mod 11).
- p = 19: QRs mod 19 are {1,4,5,6,7,9,11,16,17}. So -alpha in those, alpha in {2,3,8,10,12,13,14,15,18} (mod 19). 9 out of 18 values.
- p = 23: QRs mod 23 are {1,2,3,4,6,8,9,12,13,16,18}. So -alpha in those, alpha in {5,7,10,11,14,15,17,19,20,21,22} (mod 23). 11 out of 22 values.

### Part 2: Does EVERY prime p === 3 (mod 4) have some alpha <= B that covers P === 1 (mod p)?

From Part 1:
- p = 3: alpha = 2 works.
- p = 7: alpha = 3 works.
- p = 11: alpha = 2 works.
- p = 19: alpha = 2 works.
- p = 23: alpha = 5 works.

So far, very small alpha suffices. In general, for prime p === 3 (mod 4), we need alpha such that -alpha is a QR mod p. The QRs mod p form a subgroup of index 2 in (Z/pZ)*. So -alpha is a QR iff alpha is in -QR = {-q : q in QR}. Since |QR| = (p-1)/2, there are (p-1)/2 valid alpha values mod p. The smallest one is at most p/(something), probably O(log p) on average by the least QR estimates.

### Part 3: The grand covering question

Consider the set of primes p_1 = 3, p_2 = 7, p_3 = 11, p_4 = 19, p_5 = 23, p_6 = 31, ...

For each p_i, there exists alpha_i <= p_i such that -alpha_i is a QR mod p_i. By CRT, can we find a SINGLE alpha that works for ALL p_i simultaneously?

If we take primes p_1, ..., p_k, by CRT we need alpha to simultaneously satisfy:
- alpha === 2 (mod 3)
- alpha === 3 (mod 7) [or 5 or 6]
- alpha === 2 (mod 11) [or 6, 7, 8, 10]
- ...

Since for each p_i we have (p_i-1)/2 valid residues, and the primes are coprime, by CRT the density of valid alpha is prod((p_i-1)/(2*(p_i-1))) = prod(1/2) = 1/2^k. Wait, that's not right. For each p_i, the density of valid alpha mod p_i is (p_i-1)/(2*(p_i-1)) = 1/2. So the density of alpha satisfying ALL conditions is 1/2^k. For k primes, we expect the smallest valid alpha to be around 2^k.

Hmm, that grows exponentially. But we don't need ONE alpha for all primes p_i. We need: for each PRIME P, some (alpha, s, r) works. Different P can use different alpha.

### Part 4: The real question (reformulated)

For each prime P === 1 (mod 24), consider the set of prime factors of the numbers {P + 4*alpha*s^2 : alpha = 1..A, s = 1..S}. We need at least one of these numbers to have a divisor d === -1 (mod 4*alpha*s) for the corresponding (alpha, s).

The character rigidity lemma tells us that for each pair (alpha, s), the "compatible" prime factors p of P + 4*alpha*s^2 are those where (-alpha/p) = (P/p). Since P is given, this is a condition on p.

Now, P + 4*alpha*s^2 is a specific number. Its prime factors are what they are. The question is whether SOME prime factor p satisfies the character condition.

For alpha = 1: need a prime factor p with (-1/p) = (P/p), i.e., p === 3 (mod 4) if P is a QNR mod p, or p === 1 (mod 4) if P is a QR mod p. Actually this simplifies to: need p with (P/p) = (-1/p).

For the "hard" case P === 1 (mod p) (P is a QR mod p), we need (-1/p) = 1, so p === 1 (mod 4). But P + 4 might have all prime factors p === 1 (mod 4) (this is what makes alpha=1, s=1 fail 47% of the time).

For alpha = 2: need a prime factor p of P + 8s^2 with (-2/p) = (P/p). For P === 1 (mod p), this means (-2/p) = 1, so p === 1 or 3 (mod 8). Now 3 (mod 8) primes are 3 mod 4, and those were EXCLUDED by alpha=1! So alpha=2 can use exactly the prime factors that alpha=1 could not.

THIS IS THE BREAKTHROUGH INSIGHT. Alpha=1 can only use prime factors p === 1 (mod 4). Alpha=2 can use prime factors p === 1 or 3 (mod 8). Alpha=3 can use yet another set. Different alpha values are sensitive to different prime factor patterns.

### Part 5: Can you prove the following?

**Conjecture (Alpha Complementarity).** For every odd prime p, there exists alpha in {1, 2, 3, ..., p-1} such that (-alpha/p) = 1. (This is trivially true: (p-1)/2 such alpha exist.)

Stronger: **For every SET of odd primes {p_1, ..., p_k}, and every choice of signs epsilon_i in {+1, -1}, there exist infinitely many alpha such that (-alpha/p_i) = epsilon_i for all i.**

This follows from CRT + Dirichlet's theorem. The valid alpha form an arithmetic progression (union of progressions).

But what we ACTUALLY need is more subtle. We need:

**For every prime P === 1 (mod 24) with P >= B, there exist alpha, s >= 1 such that P + 4*alpha*s^2 has a prime factor p with (-alpha/p) = (P/p).**

Note that we don't get to choose p freely. p must be a prime factor of the SPECIFIC number P + 4*alpha*s^2. So the question is about the prime factorization of shifted values.

## What I want you to do

1. **Verify** my computation in Part 1 (which alpha values work for each small prime p).

2. **Explore** whether the complementarity between different alpha values can be turned into a proof. Specifically: if alpha=1 fails (all prime factors of P+4 are === 1 mod 4), does alpha=2 provably succeed? (Meaning: does P+8 necessarily have a prime factor p with (-2/p) = (P/p)?)

3. **State and prove** (or disprove) the strongest theorem you can about the existence of (alpha, s) for all primes P in the hard class. If a full proof is out of reach, give the strongest conditional result.

4. **Identify** whether there is a FINITE set of alpha values {alpha_1, ..., alpha_k} such that for every prime P, at least one alpha_i makes the character condition satisfiable. This would reduce the problem to a finite combinatorial check.

5. If a proof seems genuinely within reach, give every detail. If it amounts to an open problem, say so clearly and explain what the minimal additional input would be.

## Key data

- alpha=1 alone fails for 46.7% of primes P === 1 (mod 24) up to 10M
- alpha=1 AND alpha=2 together fail for 16.9%
- Using all (alpha,s) with 4*alpha*s^2 <= 200, failure rate is 0.000%
- The failure rates decay exponentially with the number of (alpha,s) pairs
- No finite covering mod any Q <= 10^6 achieves zero uncovered residues
- The uncovered residues are EXACTLY the perfect squares mod Q
- The character rigidity lemma explains this: alpha=1 forces QNR character, matching only QNR primes P (mod p), excluding P === 1 (mod p) which are QR
