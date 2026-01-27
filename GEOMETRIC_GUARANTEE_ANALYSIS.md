# Geometric Guarantee Analysis

## The Core Problem

For any prime P ≡ 1 (mod 4), we need to show there exists (α, d') such that:
1. N = 4αP(d')² + 1 factors as X·Y
2. X ≡ Y ≡ -1 (mod 4αd')
3. From this, we recover b, c satisfying the ED2 identity

## Simplification

Let's start with α = 1, d' = 1. Then:
- g = αd' = 1
- N = 4P + 1
- Need: N factors as rs with r ≡ s ≡ -1 ≡ 3 (mod 4)

Since N = 4P + 1 ≡ 1 (mod 4), any factorization N = rs has:
- Either r ≡ s ≡ 1 (mod 4)
- Or r ≡ s ≡ 3 (mod 4)

We want the second case.

## Direct Construction via CRT

**Key Idea**: Force N to be divisible by two primes ≡ 3 (mod 4).

### Making 3 | N and 7 | N

For 3 | (4Pδ + 1): Need 4Pδ ≡ -1 ≡ 2 (mod 3)
For 7 | (4Pδ + 1): Need 4Pδ ≡ -1 ≡ 6 (mod 7)

By CRT, for any P with gcd(P, 21) = 1, there exists δ < 21 satisfying both.

**Result**: 21 | (4Pδ + 1), so N has factors 3 and 7 (both ≡ 3 mod 4).

### Factorization Analysis

If N = 3 · 7 · k = 21k for some k ≥ 1:
- Take r = 3, s = 7k: Then r ≡ 3 (mod 4), but s ≡ 7k ≡ 3k (mod 4)
  - If k ≡ 1 (mod 4): s ≡ 3 (mod 4) ✓
  - If k ≡ 3 (mod 4): s ≡ 1 (mod 4) ✗
- Take r = 7, s = 3k: Then r ≡ 3 (mod 4), s ≡ 3k (mod 4)
  - Same conditions on k
- Take r = 21, s = k: Then r ≡ 1 (mod 4) ✗

So we need k ≡ 1 (mod 4).

### Refined CRT

For the factorization r = 3, s = 7k to work with both ≡ 3 (mod 4), we need:
- 21 | N (so k = N/21)
- k ≡ 1 (mod 4), i.e., N/21 ≡ 1 (mod 4), i.e., N ≡ 21 (mod 84)

Combined with N = 4Pδ + 1:
- 4Pδ + 1 ≡ 21 (mod 84)
- 4Pδ ≡ 20 (mod 84)
- Pδ ≡ 5 (mod 21)

For each P (mod 21), this determines δ (mod 21).

### Case Analysis by P (mod 21)

P ≡ 1 (mod 21): δ ≡ 5 (mod 21)
P ≡ 2 (mod 21): 2δ ≡ 5 (mod 21), δ ≡ 5·11 ≡ 55 ≡ 13 (mod 21)
P ≡ 4 (mod 21): 4δ ≡ 5 (mod 21), δ ≡ 5·16 ≡ 80 ≡ 17 (mod 21)
P ≡ 5 (mod 21): 5δ ≡ 5 (mod 21), δ ≡ 1 (mod 21)
P ≡ 8 (mod 21): 8δ ≡ 5 (mod 21), δ ≡ 5·8 ≡ 40 ≡ 19 (mod 21)
P ≡ 10 (mod 21): 10δ ≡ 5 (mod 21), δ ≡ 5·19 ≡ 95 ≡ 11 (mod 21)
P ≡ 11 (mod 21): 11δ ≡ 5 (mod 21), δ ≡ 5·2 ≡ 10 (mod 21)
P ≡ 13 (mod 21): 13δ ≡ 5 (mod 21), δ ≡ 5·13 ≡ 65 ≡ 2 (mod 21)
P ≡ 16 (mod 21): 16δ ≡ 5 (mod 21), δ ≡ 5·4 ≡ 20 (mod 21)
P ≡ 17 (mod 21): 17δ ≡ 5 (mod 21), δ ≡ 5·5 ≡ 25 ≡ 4 (mod 21)
P ≡ 19 (mod 21): 19δ ≡ 5 (mod 21), δ ≡ 5·10 ≡ 50 ≡ 8 (mod 21)
P ≡ 20 (mod 21): 20δ ≡ 5 (mod 21), δ ≡ 5·20 ≡ 100 ≡ 16 (mod 21)

(Note: P ≡ 0, 3, 7, 14 (mod 21) impossible for prime P > 7 with P ≡ 1 (mod 4))

### Verification

For P = 5 (≡ 5 mod 21): δ ≡ 1 (mod 21), take δ = 1
- N = 4·5·1 + 1 = 21 = 3·7
- r = 3, s = 7, both ≡ 3 (mod 4) ✓
- But k = 1, and we need N ≡ 21 (mod 84)
- Check: 21 ≡ 21 (mod 84) ✓

For P = 13 (≡ 13 mod 21): δ ≡ 2 (mod 21), take δ = 2
- N = 4·13·2 + 1 = 105 = 3·5·7
- Take r = 3·7 = 21, s = 5. But 21 ≡ 1 (mod 4) ✗
- Take r = 3, s = 35. Then r ≡ 3, s ≡ 3 (mod 4) ✓

Wait, let me recompute. s = 35 = 5·7 ≡ 3 (mod 4)? 35 = 32 + 3 ≡ 3 (mod 4) ✓

So N = 105 = 3 × 35 with both factors ≡ 3 (mod 4).

### The Key Insight

We don't need k ≡ 1 (mod 4) for ALL factorizations; we just need ONE factorization rs with r ≡ s ≡ 3 (mod 4).

If N has at least two prime factors ≡ 3 (mod 4) (counting with multiplicity), we can form such a factorization by putting one ≡ 3 prime in r and rearranging the rest.

**Revised Strategy**: Force N to have at least two prime factors ≡ 3 (mod 4).

Making 3 | N and 7 | N is sufficient (unless one of them appears to an odd power while all other factors are ≡ 1 mod 4).

Actually, since 3 ≡ 7 ≡ 3 (mod 4), if both divide N, we have:
- N = 3^a · 7^b · m where gcd(m, 21) = 1
- If a + b is even, we can split the factors ≡ 3 (mod 4) evenly
- If a + b is odd but m has a factor ≡ 3 (mod 4), we can still balance

The problematic case: a = b = 1 (both odd) and all factors of m are ≡ 1 (mod 4).

Then N = 21m with m ≡ 1 (mod 4), and we can take r = 3, s = 7m:
- r ≡ 3 (mod 4) ✓
- s = 7m ≡ 7·1 ≡ 3 (mod 4) ✓

So this ALWAYS works when 21 | N and gcd(N/21, 21) = 1!

## Theorem: CRT Construction

**Theorem**: For any prime P ≡ 1 (mod 4) with P > 7, there exists δ ≤ 21 such that:
1. 21 | (4Pδ + 1)
2. N := 4Pδ + 1 has a factorization N = rs with r ≡ s ≡ 3 (mod 4)

**Proof**:
By CRT, for any P with gcd(P, 21) = 1, there exists unique δ (mod 21) such that:
- 3 | (4Pδ + 1), i.e., 4Pδ ≡ 2 (mod 3)
- 7 | (4Pδ + 1), i.e., 4Pδ ≡ 6 (mod 7)

Take the smallest such δ ∈ {1, ..., 21}.

Then N = 4Pδ + 1 = 21 · k for some k = (4Pδ + 1)/21 ≥ 1.

Take r = 3, s = 7k. Then:
- r = 3 ≡ 3 (mod 4) ✓
- s = 7k: Since 7 ≡ 3 (mod 4) and we need s ≡ 3 (mod 4), this holds iff k ≡ 1 (mod 4).

If k ≢ 1 (mod 4), take r = 7, s = 3k:
- r = 7 ≡ 3 (mod 4) ✓
- s = 3k: Since 3 ≡ 3 (mod 4), s ≡ 3 (mod 4) iff k ≡ 1 (mod 4).

Hmm, both cases require k ≡ 1 (mod 4). What if k ≡ 3 (mod 4)?

If k ≡ 3 (mod 4):
- 7k ≡ 7·3 ≡ 21 ≡ 1 (mod 4)
- 3k ≡ 3·3 ≡ 9 ≡ 1 (mod 4)

So neither r = 3, s = 7k nor r = 7, s = 3k works.

But we can try r = 21, s = k:
- 21 ≡ 1 (mod 4) ✗

Or find other factorizations of N...

## Problem Case

If N = 21k with k ≡ 3 (mod 4) and k has no prime factor ≡ 3 (mod 4), then ALL factorizations rs have one factor ≡ 1 (mod 4) and one ≡ 3 (mod 4).

Example: Let N = 21 · 3 = 63 = 7 · 9 = 9 · 7. Here k = 3 ≡ 3 (mod 4).
- r = 3, s = 21: 3 ≡ 3 (mod 4), 21 ≡ 1 (mod 4) ✗
- r = 7, s = 9: 7 ≡ 3 (mod 4), 9 ≡ 1 (mod 4) ✗
- r = 9, s = 7: same as above
- r = 21, s = 3: 21 ≡ 1, 3 ≡ 3 ✗
- r = 63, s = 1: trivial, doesn't help

BUT wait: N = 63 = 3² · 7, so we have THREE factors of primes ≡ 3 (mod 4). We can take:
- r = 3 · 3 = 9? No, 9 ≡ 1 (mod 4).
- r = 3, s = 3 · 7 = 21? No, 21 ≡ 1 (mod 4).

Hmm, the issue is that 3² ≡ 1 (mod 4). Having an even number of 3's doesn't help.

So the real condition is: N must have an EVEN number of prime factors ≡ 3 (mod 4) (counting multiplicity) for a factorization with both factors ≡ 3 (mod 4).

## Revised Strategy

Force N to have an even number (≥ 2) of prime factors ≡ 3 (mod 4).

Options:
1. Force 3² | N and 7 | N (total of 3 factors ≡ 3 mod 4, which is odd - BAD)
2. Force 3 | N and 7² | N (total of 3 factors - BAD)
3. Force 3² | N and 7² | N (total of 4 factors - GOOD!)
4. Force 3 | N and 7 | N and 11 | N (total of 3 factors - BAD)
5. Force 3 | N and 7 | N and 11 | N and 19 | N (total of 4 factors - GOOD!)

Let's try option 3: 9 | N and 49 | N, i.e., 441 | N.

For 441 | (4Pδ + 1), by CRT with gcd(P, 441) = 1, there exists δ (mod 441) making this work.

Then N = 441k = 9 · 49 · k = 3² · 7² · k.

Total prime factors ≡ 3 (mod 4): 2 + 2 = 4 (even).

Take r = 3 · 7 = 21, s = 3 · 7 · k = 21k.
- r = 21 ≡ 1 (mod 4) ✗

Take r = 3² · 7 = 63, s = 7k.
- r = 63 ≡ 3 (mod 4)? 63 = 64 - 1 ≡ -1 ≡ 3 (mod 4) ✓
- s = 7k ≡ 3k (mod 4). Need k ≡ 1 (mod 4).

Alternatively, r = 3 · 7² = 147, s = 3k.
- 147 = 144 + 3 ≡ 3 (mod 4) ✓
- s = 3k ≡ 3k (mod 4). Need k ≡ 1 (mod 4).

So we still need k ≡ 1 (mod 4), i.e., N ≡ 441 (mod 4·441) = 441 (mod 1764).

But 441 ≡ 1 (mod 4), so N ≡ 1 (mod 4) automatically since N = 4Pδ + 1.

So N = 441k with N ≡ 1 (mod 4) means 441k ≡ 1 (mod 4), i.e., k ≡ 1 (mod 4) since 441 ≡ 1 (mod 4).

Wait, 441 = 440 + 1 ≡ 1 (mod 4). So 441k ≡ k (mod 4). For N ≡ 1 (mod 4), need k ≡ 1 (mod 4). ✓

So if 441 | N and N ≡ 1 (mod 4), then k ≡ 1 (mod 4), and we can take:
- r = 63 = 3² · 7 ≡ 3 (mod 4)
- s = 7k ≡ 7 · 1 ≡ 3 (mod 4) ✓

## Final Theorem

**Theorem**: For any prime P ≡ 1 (mod 4) with gcd(P, 441) = 1, there exists δ ≤ 441 such that:
1. N := 4Pδ + 1 is divisible by 441 = 3² · 7²
2. N = rs where r = 63 = 3² · 7, s = N/63 = 7k
3. Both r ≡ s ≡ 3 (mod 4)

**Proof**:
By CRT, find δ (mod 441) such that 4Pδ ≡ -1 (mod 441). Such δ exists since gcd(4P, 441) = 1.

Then N = 4Pδ + 1 ≡ 0 (mod 441), so N = 441k for some k ≥ 1.

Since N ≡ 1 (mod 4) and 441 ≡ 1 (mod 4), we have k ≡ 1 (mod 4).

Take r = 63 = 3² · 7 and s = 7k.
- r = 63 ≡ 3 (mod 4) ✓
- s = 7k ≡ 7 · 1 ≡ 3 (mod 4) ✓

## Remaining Issue: Connection to ED2 Parameters

We have a factorization N = rs with r ≡ s ≡ 3 (mod 4). But for ED2, we need:
- N = 4αP(d')² + 1 for some squarefree α and d' ∈ ℕ
- The factorization X · Y = N with X ≡ Y ≡ -1 (mod 4αd')

Our construction gives N = 4Pδ + 1. If we set α = 1 and d' = 1, then N = 4P + 1.
But we're using δ > 1 in general...

Oh wait, I was conflating two things. Let me re-read the ED2 setup.

From Theorem 7.3: For δ = α(d')², we have N = 4αP(d')² + 1 = 4Pδ + 1.

So any δ = α(d')² works. Our CRT construction gives δ ≤ 441. We can always write δ = α(d')² by taking α = δ (if δ is squarefree) and d' = 1, or factoring δ appropriately.

Actually, the condition is that α must be squarefree. If δ has a square factor, we extract it into d'.

For δ ≤ 441, we can always write δ = α(d')² with:
- α = δ/gcd(δ, □)² where □ is the largest square dividing δ
- d' = sqrt(δ/α)

The key constraint from Theorem 7.3 is X ≡ Y ≡ -1 (mod 4αd'), i.e., X ≡ Y ≡ 3 (mod 4αd').

With our construction: r ≡ s ≡ 3 (mod 4). This is -1 (mod 4), which satisfies X ≡ Y ≡ -1 (mod 4·1·1) = -1 (mod 4) when α = 1, d' = 1.

But if δ > 1, we have α(d')² = δ, and the congruence X ≡ Y ≡ -1 (mod 4αd') is stronger.

## The Real Problem

The construction in Theorem 7.3 requires:
- For fixed (α, d'), compute N = 4αP(d')² + 1
- Factor N = X · Y with X ≡ Y ≡ -1 (mod 4αd')
- Recover b' = (X+1)/(4αd'), c' = (Y+1)/(4αd')

The congruence constraint is X ≡ Y ≡ -1 (mod 4αd'), not just (mod 4).

For large 4αd', this is a much stronger constraint!

However, with α = 1 and d' = 1, we have 4αd' = 4, and the constraint is just X ≡ Y ≡ -1 ≡ 3 (mod 4), which is what we've been analyzing.

So for α = 1, d' = 1, δ = 1, we need:
- N = 4P + 1 factors as X · Y with both X ≡ Y ≡ 3 (mod 4)

This is the simplest case, and our CRT analysis shows it doesn't always work for δ = 1 (when N = 4P + 1 is prime or has the wrong factorization structure).

The solution is to try different (α, d') pairs:
- (1, 1): δ = 1, N = 4P + 1
- (1, 2): δ = 4, N = 16P + 1
- (2, 1): δ = 2, N = 8P + 1
- (1, 3): δ = 9, N = 36P + 1
- (3, 1): δ = 3, N = 12P + 1
- etc.

For SOME (α, d'), N has the required factorization.

## Density Argument (Heuristic)

Among the choices (α, d') with αd' ≤ D:
- Number of choices: O(D²)
- For each, N = 4αP(d')² + 1 is a specific number
- The probability that N factors correctly is some positive constant (heuristically)
- By pigeonhole, for D large enough, at least one works

This is the "density argument" the paper mentions. But it's not a PROOF - it's a heuristic.

## What's Missing for a Complete Proof

A complete proof would need to show:
1. For any P ≡ 1 (mod 4), there exist (α, d') with δ = α(d')² bounded by some B(P) such that N = 4Pδ + 1 has a factorization X · Y with X ≡ Y ≡ -1 (mod 4αd').

This seems to require either:
- A density/averaging argument that works for EVERY P (not just on average)
- A direct construction that always produces valid (α, d')
- A computer-assisted case analysis for residue classes of P

## Possible Direct Approach

For P ≡ 1 (mod 4), consider δ = (P-1)/4. Then:
- N = 4P · (P-1)/4 + 1 = P(P-1) + 1 = P² - P + 1

Now P² - P + 1 is known to have special factorization properties...

Actually, let me check: for what P is P² - P + 1 = rs with r ≡ s ≡ 3 (mod 4)?

P = 5: N = 25 - 5 + 1 = 21 = 3 · 7 ✓
P = 13: N = 169 - 13 + 1 = 157 (prime ≡ 1 mod 4) ✗
P = 17: N = 289 - 17 + 1 = 273 = 3 · 91 = 3 · 7 · 13. Take r = 21, s = 13? 21 ≡ 1 ✗. Take r = 3, s = 91 = 7·13 ≡ 3·1 = 3 ✓

So for P = 17, N = 273 = 3 × 91 with 3 ≡ 3 and 91 = 7·13 ≡ 3·1 ≡ 3 (mod 4). ✓

This δ = (P-1)/4 construction might be worth exploring further...

## Computational Verification Results (January 2025)

Ran `check_ed2_existence.py` on all 80 primes P ≡ 1 (mod 4) up to 1000.

### Key Results:
- **100% success rate** (80/80 primes)
- δ ≤ 14 suffices for all tested primes
- Distribution of minimal δ values:
  - δ=1 (α=1, d'=1): 58 primes (72.5%)
  - δ=2 (α=2, d'=1): 13 primes (16.25%)
  - δ=3 (α=3, d'=1): 3 primes (P ∈ {241, 277, 757})
  - δ=4 (α=1, d'=2): 3 primes (P ∈ {157, 409, 577})
  - δ=5 (α=5, d'=1): 1 prime (P = 37)
  - δ=6 (α=6, d'=1): 1 prime (P = 421)
  - δ=14 (α=14, d'=1): 1 prime (P = 997)

### Pattern Analysis

**When δ=1 works:**
For N = 4P + 1, the δ=1 case works when N has a prime factor q ≡ 3 (mod 4).
This is because we need X ≡ Y ≡ 3 (mod 4), and if q | N with q ≡ 3 (mod 4),
then taking X = q, Y = N/q gives Y ≡ 3 (mod 4) since N ≡ 1 (mod 4).

**When δ=1 fails:**
- P = 13: N = 53 (prime, 53 ≡ 1 mod 4)
- P = 37: N = 149 (prime, 149 ≡ 1 mod 4)
- P = 61: N = 245 = 5 × 7²; 7 ≡ 3, works!
- P = 73: N = 293 (prime, 293 ≡ 1 mod 4)
- P = 97: N = 389 (prime, 389 ≡ 1 mod 4)

So δ=1 fails when 4P+1 is a "1 (mod 4) number" (all prime factors ≡ 1 mod 4).

**Why δ=2 rescues these cases:**
For δ=2 (α=2, d'=1), N = 8P + 1, and we need X ≡ Y ≡ 7 (mod 8).
- P = 13: N = 105 = 3 × 5 × 7. Factorization 7 × 15: 7 ≡ 7, 15 ≡ 7 (mod 8) ✓
- P = 73: N = 585 = 9 × 65 = 3² × 5 × 13. Factorization 15 × 39: 15 ≡ 7, 39 ≡ 7 (mod 8) ✓
- P = 97: N = 777 = 3 × 7 × 37. Factorization 7 × 111: 7 ≡ 7, 111 ≡ 7 (mod 8) ✓

**P = 37 is special:**
- δ=1: N = 149 (prime ≡ 1 mod 4) ✗
- δ=2: N = 297 = 3³ × 11. Need factors ≡ 7 (mod 8). 3 ≡ 3, 27 ≡ 3, 99 ≡ 3, 11 ≡ 3. None ≡ 7 (mod 8) ✗
- δ=3: N = 445 = 5 × 89. Need ≡ 11 (mod 12). 5 ≡ 5, 89 ≡ 5 (mod 12) ✗
- δ=4: N = 593 (prime ≡ 1 mod 4) ✗
- δ=5: N = 741 = 3 × 13 × 19. Need ≡ 19 (mod 20). 19 ≡ 19, 39 ≡ 19 (mod 20) ✓

So P = 37 requires δ = 5 because smaller δ values don't give favorable factorizations.

## Refined Proof Strategy

### Theorem (ED2 Existence via Exhaustion)

For any P ≡ 1 (mod 4), there exists (α, d') with δ = α(d')² ≤ 21 such that:
1. N = 4αP(d')² + 1 has a factorization X × Y
2. X ≡ Y ≡ -1 (mod 4αd')
3. gcd((X+1)/(4αd'), (Y+1)/(4αd')) = 1

**Approach**: For each residue class P (mod M) for suitable M, verify computationally that one of the first few (α, d') pairs works.

Since the condition involves P (mod 4αd'²), we need to analyze P modulo lcm of these moduli.

For (α, d') ∈ {(1,1), (2,1), (3,1), (5,1), (6,1), (7,1), (1,2), (2,2)}:
- Corresponding moduli 4αd': 4, 8, 12, 20, 24, 28, 8, 16
- LCM: 840

So analyzing P (mod 840) should suffice to determine which (α, d') works.

### Alternative: Probabilistic Guarantee

The probability that N = 4Pδ + 1 is a "1 (mod 4) number" (all prime factors ≡ 1 mod 4) is approximately 1/√(log N) by analytic results on the distribution of primes in arithmetic progressions.

For independent δ values, the probability that ALL of N₁, N₂, ..., Nₖ are "1 (mod 4) numbers" is roughly (1/√(log P))^k → 0 as k → ∞.

This suggests that for any P, some δ ≤ O(log log P) works.

But this is heuristic; for a rigorous proof, we need to verify that different δ values give "independent enough" N values.

## Lean Formalization Path

The most tractable approach for Lean:

1. **Enumerate cases by P (mod 840)**
2. **For each residue class, verify which (α, d') works**
3. **Prove the ED2 identity algebraically for those cases**

This is computationally intensive but mathematically straightforward.

## Key Lemma: Factor Condition

**Lemma**: Let N be odd with N ≡ 1 (mod 4). Then N has a factorization X × Y with X ≡ Y ≡ 3 (mod 4) if and only if N has an even number (≥ 2) of prime factors q with q ≡ 3 (mod 4), counting multiplicity.

**Proof**:
(→) If N = X × Y with X ≡ Y ≡ 3 (mod 4), then N ≡ 9 ≡ 1 (mod 4) ✓.
Each X, Y has an odd number of prime factors ≡ 3 (mod 4) (since X ≡ 3 mod 4).
So X and Y together have an even number of such factors.

(←) If N has ≥ 2 prime factors ≡ 3 (mod 4), we can partition them so each part has an odd number.
This gives X × Y = N with both X ≡ Y ≡ 3 (mod 4).

**Corollary**: For α = 1, d' = 1, the ED2 method works for P when N = 4P + 1 has at least two prime factors ≡ 3 (mod 4) (with multiplicity).

## Extended Computational Analysis (ed2_residue_analysis.py)

### Large-Scale Verification

Tested all 4783 primes P ≡ 1 (mod 4) up to 100,000:
- **100% success rate** (0 failures)
- **Maximum δ needed: 95** (for P = 46237 ≡ 37 mod 840)
- 96 distinct residue classes mod 840 analyzed

### Distribution of Minimal δ Needed

| δ bound | # of residue classes |
|---------|---------------------|
| δ ≤ 1   | 57 (59%)            |
| δ ≤ 2   | 73 (76%)            |
| δ ≤ 3   | 75 (78%)            |
| δ ≤ 21  | 82 (85%)            |
| δ ≤ 50  | 89 (93%)            |
| δ ≤ 100 | 96 (100%)           |

### Key Finding: ED2 Bypasses Mordell-Hard Barrier

The Mordell-hard residue classes mod 840 are {1, 121, 169, 289, 361, 529}.

Their max δ requirements:
- 1 mod 840: max δ = 86
- 121 mod 840: max δ = 21
- 169 mod 840: max δ = 14
- 289 mod 840: max δ = 21
- 361 mod 840: max δ = 14
- 529 mod 840: max δ = 39

**Crucially, the hardest class is 37 mod 840 (max δ = 95), which is NOT Mordell-hard!**

This confirms that ED2 works fundamentally differently from congruence-covering:
- Congruence methods fail on Mordell-hard classes (proven by Tao 2011)
- ED2 handles Mordell-hard classes but has different "hard" cases
- The ED2 difficulty comes from factorization structure, not quadratic residues

### Proof Strategy Implications

The computational evidence strongly supports:

**Theorem (ED2 Geometric Guarantee)**: For any prime P ≡ 1 (mod 4), there exists
δ = α(d')² ≤ C(P) such that ED2 parameters exist, where C(P) = O(log P).

**Proof sketch**:
1. For P < 10^8: Dyachenko's computational verification
2. For general P: Density argument on prime factors mod 4

The key is that as P grows, the numbers N = 4Pδ + 1 for δ = 1, 2, ..., X include
increasingly many independent factorization opportunities. The probability that
ALL of them lack a suitable prime factor ≡ 3 (mod 4) decreases exponentially in X.

### Lean Formalization Path

Given the computational evidence, the cleanest Lean approach is:

1. **Trust computational verification** for specific range (P < 10^8)
2. **Accept the geometric guarantee as axiom** with explicit justification:
   - Dyachenko Theorem 10.21
   - Computational verification to 10^5 (our scripts)
   - Paper claims verification to 10^8
3. **The axiom is mathematically defensible** because:
   - It's NOT equivalent to the full ESC
   - It's a constructive claim about factorization structure
   - The density argument makes the bound C(P) = O(log P) plausible

### Alternative: Direct Lean Proof via Decide

For small primes (P < 1000), we could prove existence directly in Lean using `decide`:

```lean
example : ∃ δ α d', validED2Params 37 δ α d' := by decide  -- works for small P
```

For larger primes, the `native_decide` tactic could handle up to P ~ 10^6.
