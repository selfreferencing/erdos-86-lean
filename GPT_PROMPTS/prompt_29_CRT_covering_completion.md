# GPT Prompt 29: Complete the CRT Small-Modulus Covering Theorem

## Context (follow-up to prompts 27A/27B and 21A)

Prompts 27A and 27B established the sigma(N,m) divisor-counting framework and computed root tables for small prime moduli. Prompt 21A proved that no finite covering works when restricted to a fixed set of alpha values (Chebotarev obstruction). But nobody has actually tried to combine the small-modulus root tables via CRT with ALPHA FLEXIBILITY to see how much of the P-residue space they cover.

This prompt asks: can a finite set of small moduli, exploiting alpha flexibility, cover ALL primes P === 1 (mod 24)?

## The setup (verified results from prior prompts)

### The D.6 condition (corrected formula, cross-validated in 26A and 28A)

For prime P === 1 (mod 24), the Erdos-Straus conjecture holds iff there exist positive integers alpha, s, r with M = 4*alpha*s*r - 1 dividing P + 4*alpha*s^2. Equivalently:

ES holds for P iff there exists A in [(P+3)/4, (P+1)/3] and alpha | A such that N = A/alpha has a divisor s with s + N/s === 0 (mod m), where m = 4A - P.

Note: 27A proved the tightened window A <= (P+1)/3 (not (3P-3)/4). This means m = 4A - P <= (P+4)/3.

### sigma(N,m) definition and CRT structure (from 27A, verified)

sigma(N, m) = #{s | N : s + N/s === 0 (mod m)}.

CRT prime-power local structure (for odd prime p, p^a || m):
- v_p(N) < a, coprime case: need s^2 === -N (mod p^a), 2 roots if (-N/p) = 1, 0 if (-N/p) = -1
- a <= v_p(N) <= 2a-1: NO solutions (mixed divisibility)
- v_p(N) >= 2a: solutions exist trivially

CRT combines: |R_m(-N)| in {0, 2^omega(m)} for squarefree m.

### Root tables for small prime moduli (from 27A, ALL VERIFIED)

For prime modulus p, sigma(N, p) > 0 iff (-N/p) = 1, i.e., -N is a QR mod p.

Solvable residues of N:
- m=3: N === 2 (mod 3) [i.e., -N === 1 (mod 3), QR]. Also 9 | N works.
- m=7: N mod 7 in {3, 5, 6} [i.e., -N mod 7 in {1, 2, 4} = QR mod 7]
- m=11: N mod 11 in {2, 6, 7, 8, 10} [i.e., -N mod 11 in {1, 3, 4, 5, 9} = QR mod 11]
- m=19: N mod 19 in {2, 3, 8, 10, 12, 13, 14, 15, 18} [QR set for -N]
- m=23: N mod 23 in {5, 7, 10, 11, 14, 15, 17, 19, 20, 21, 22}

### m=3 with alpha flexibility (from 27A, corrected from 27B's error)

For P === 1 (mod 24), m = 3 gives A = (P+3)/4. Then:
- alpha = 1: N = A === 1 (mod 3), so sigma = 0. DEAD.
- alpha = 2: requires 2 | A. If A is even, N = A/2. If A === 2 (mod 3), then N === 1 (mod 3), still dead. But if A === 0 (mod 6), then N = A/2 === 0 (mod 3) and need to check valuation.
- alpha === 2 (mod 3): N = A/alpha. Since A === 1 (mod 3), N === 1 * (alpha^{-1} mod 3) = 1 * 2 = 2 (mod 3). So sigma(N, 3) > 0!

KEY INSIGHT (27A): m=3 is alive when alpha === 2 (mod 3) divides A. Not all A have such a divisor (e.g., A prime with A === 1 mod 3).

### The no-finite-covering result (from 21A, verified)

For any finite set of alpha values {alpha_1, ..., alpha_k}, Chebotarev density gives infinitely many primes P where ALL alpha_i are QRs mod P, making the character-kernel obstruction active for all pairs simultaneously. Verified: for alphas {1,2,3,5,6}, found bad primes {71, 191, 239, 311, 359, 431, 479}.

However, this result restricts to FIXED alpha values with FIXED moduli. It does NOT rule out a covering where the modulus m varies with A (and hence with P).

### Forced-divisor constructions (from 27B, verified)

m=7, A = (P+7)/4:
- P === 1 (mod 8) forces 2 | A
- s=1 covers P === 3 (mod 7)
- s=2 covers P === 5 (mod 7)

m=11, A = (P+11)/4:
- P === 1 (mod 3) forces 3 | A
- s=1 covers P === 7 (mod 11)
- s=3 covers P === 8 (mod 11)

## What I need from you

### Task 1: Systematic CRT coverage analysis with alpha flexibility

For each m in {3, 5, 7, 11, 13, 15, 17, 19, 23} (all odd m up to 23 that can arise as 4A - P for P === 1 mod 24):

(a) For this m, which A value gives m = 4A - P? Answer: A = (P + m)/4. What conditions on P ensure A is a positive integer? (Need P === -m (mod 4), i.e., P + m === 0 (mod 4).)

(b) For this A = (P + m)/4, what divisors alpha of A are guaranteed to exist (based on P mod small primes)? For instance, if m === 3 (mod 8) and P === 1 (mod 8), then A = (P+m)/4 is even, so alpha = 2 is available.

(c) For each available alpha, compute N = A/alpha (mod m) as a function of P mod lcm(24, m). Then check: is (-N/p) = 1 for each prime p | m?

(d) Record which residue classes of P (mod lcm(24, m)) are "covered" by this (m, alpha) pair.

### Task 2: Combine coverage via CRT

Let L = lcm(24, 3, 7, 11) = lcm(24, 231) = 1848 (or the appropriate lcm for your modulus set).

(a) List ALL residue classes of P (mod L) that satisfy P === 1 (mod 24).

(b) For each such class, determine whether ANY of the small-modulus coverings from Task 1 handles it.

(c) Compute the union of covered classes. What fraction of the P === 1 (mod 24) classes are covered?

(d) If full coverage is not achieved with m up to 23: extend to m up to 47 (next few primes) and recompute. Is there a threshold where coverage becomes complete?

### Task 3: Characterize the uncovered residue classes

If the CRT union from Task 2 does NOT achieve full coverage:

(a) Identify the uncovered residue classes of P explicitly.

(b) For each uncovered class, explain WHY all small moduli fail. Is it because:
   - P is a QR mod all small primes (making -N a QNR for all m)?
   - No suitable alpha divides A for any m?
   - Something else?

(c) Estimate the density of uncovered primes via Chebotarev. Is it 1/2^k for some k (number of QR conditions)?

(d) Prove or disprove: for ANY finite set of moduli, uncovered classes exist. (This would establish that the CRT approach alone cannot solve the problem, confirming 21A/27A's conclusion but now with alpha flexibility included.)

### Task 4: What would close the gap?

If finite covering fails:

(a) What additional input would make it work? (E.g., if we could guarantee alpha | A with alpha a QNR mod some prime p | m, would that suffice?)

(b) Does the tightened window A <= (P+1)/3 create any new constraints that help or hurt?

(c) Is there a hybrid approach: finite covering handles "most" residue classes, and a counting/density argument handles the rest?

(d) State precisely what the remaining uncovered set looks like, so that prompts 30-32 (Banks-Friedlander-Luca adaptation, Erdos-Hall subset product, Borel-Cantelli finiteness) can target it exactly.

### Task 5: Explicit computation for P up to 10^4

As a sanity check:

(a) For each prime P === 1 (mod 24) up to 10^4, determine the smallest m (i.e., the smallest offset k such that m = 3 + 4k gives sigma > 0 with some alpha). What is the distribution of "winning m" values?

(b) Are there any primes P up to 10^4 that require m > 23? If so, list them and their winning (m, alpha, s) triples.

(c) Does the data suggest that a finite number of moduli suffice, or does the needed m grow with P?

## What a successful response looks like

- Explicit tables showing coverage by residue class of P for each (m, alpha) pair
- A clear YES/NO answer on whether finite CRT covering works with alpha flexibility
- If NO: the precise uncovered set, with proof that it's non-empty for any finite modulus bound
- If YES: the explicit theorem statement and which (m, alpha) pairs suffice
- Computational sanity check matching the theoretical analysis

## Important notes

- Use the CORRECTED D.6 formula: x = alpha*s*t, y = alpha*r*s*P, z = alpha*r*t*P where t = mr - s.
- Do NOT rely on Dyachenko's paper (errors found during formalization; confirmed by Thomas at erdosproblems.com).
- The 21A no-finite-covering result used FIXED alpha with FIXED m. The question here is whether VARYING alpha with VARYING m (both depending on P) changes the picture.
- The Yamamoto condition (28A): (M/P) = -1 is necessary for D.6 solutions. Equivalently, (m/P) = -(alpha/P). This may constrain which (m, alpha) pairs can work for a given P.
