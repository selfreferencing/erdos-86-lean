# Prompt: Micro Decomposition — Prove ED2 Existence for p ≡ 1 (mod 24)

## Context

We are formalizing the Erdős-Straus Conjecture (4/n = 1/x + 1/y + 1/z) in Lean 4 with Mathlib. We have reduced the entire conjecture to ONE sorry: proving that for every prime p ≡ 1 (mod 24) with p ≥ 5, there exist natural numbers offset, b, c with:

```
offset % 4 = 3 ∧ b > 0 ∧ c > 0 ∧
(↑p + ↑offset : ℤ) * (↑b + ↑c) = 4 * ↑offset * ↑b * ↑c
```

This is the "Type II Diophantine equation." Setting A = (p + offset)/4 and doing substitution, it's equivalent to: A² has a positive divisor d ≡ -A (mod offset), where offset = 4A - p.

We've already proven Cases 1 and 2 (p ≡ 5,17 mod 24 and p ≡ 13 mod 24) using explicit algebraic constructions with offset = 3. Case 3 (p ≡ 1 mod 24) cannot use a fixed offset — counterexample p = 73.

## The Mathematical Problem (Restated Cleanly)

**For every prime p ≡ 1 (mod 24) with p ≥ 5, there exists an odd integer δ ≡ 3 (mod 4) with δ ≥ 3 and positive integers b, c such that:**

**(p + δ)(b + c) = 4δbc**

Equivalently, setting A = (p + δ)/4:

**A² has a positive divisor d with d ≡ -A (mod δ)**

Equivalently, rephrasing the divisor condition:

**There exist positive integers d₁, d₂ with d₁ · d₂ = A² and d₁ + d₂ ≡ 0 (mod δ)**

(Since d₁ ≡ -A (mod δ) and d₂ = A²/d₁ ≡ -A (mod δ), so d₁ + d₂ ≡ -2A (mod δ). Actually this needs care — see the algebra below.)

### More careful reformulation

Given A and δ = 4A - p:
- We need d | A² with d ≡ -A (mod δ)
- Then b = (A + d)/δ and c = (A + A²/d)/δ are positive integers
- The condition d ≡ -A (mod δ) ensures δ | (A + d)
- Since d | A² and d ≡ -A (mod δ), we get A²/d ≡ A²/(-A) ≡ -A (mod δ), so δ | (A + A²/d) too

### What makes it hard

For a FIXED δ (say δ = 3), the condition "A² has a divisor ≡ -A (mod 3)" fails when A is prime and A ≡ 1 (mod 3), because all divisors of A² are ≡ 1 (mod 3).

The proof must VARY δ (equivalently, vary A) to find one that works.

## Task: Break This Into Individually Provable Lean Lemmas

I want you to decompose the proof into a sequence of lemmas, each of which is:
1. Mathematically precise (stated as a Lean 4 theorem signature)
2. Self-contained (provable without the others, given standard Mathlib)
3. Small enough that an AI can prove it in one shot
4. Together, they chain to prove the sorry

### Suggested decomposition layers:

**Layer 1: Algebraic infrastructure**
- Lemma: The Type II equation (p+δ)(b+c) = 4δbc with A = (p+δ)/4 is equivalent to BC = A² where B = δb-A, C = δc-A.
- Lemma: If d | A² and d ≡ -A (mod δ) and d > 0, then b := (A+d)/δ > 0 and c := (A+A²/d)/δ > 0 and they satisfy the Type II equation.

**Layer 2: Offset coverage characterization**
- Lemma: For offset δ = 3 and A = (p+3)/4, a solution exists iff A² has a divisor ≡ 2A (mod 3), iff A has a prime factor ≡ 2 (mod 3).
- Lemma: For offset δ = 7 and A = (p+7)/4, a solution exists iff A² has a divisor ≡ 6A (mod 7), which holds whenever A is even (since 2|A gives divisor 2...).
- Similar for offset 11, 15, etc.

**Layer 3: Finite computation**
- Lemma: For all primes p with 5 ≤ p ≤ B and p ≡ 1 (mod 24), the existential holds. (By native_decide or decide for some explicit bound B.)

**Layer 4: Large prime coverage**
- Lemma: For p > B, one of the offsets {3, 7, 11, ...} must work, by a counting/density argument.

### Key questions for each layer:

1. **Layer 1**: What exact Lean types and theorem signatures should these have?
2. **Layer 2**: For offset = 7 specifically, when A = (p+7)/4 and p ≡ 1 (mod 24), is A always even? (Since p ≡ 1 mod 8, p+7 ≡ 0 mod 8, so A = (p+7)/4 is even. Yes!) And does A being even suffice? (We need a divisor of A² ≡ -A mod 7. A is even, so 2|A, thus 2|A². We need to check if 2 ≡ -A mod 7, i.e., A ≡ -2 ≡ 5 mod 7. This only works when A ≡ 5 mod 7, not always.)
3. **Layer 3**: How large does B need to be? Can native_decide handle it? Empirically, offset ≤ 63 suffices for p ≤ 100,000. What if we set B = 100,000 or even 1,000,000?
4. **Layer 4**: What is the simplest density argument? Options include:
   - Sieve theory (Landau-Ramanujan: density of numbers with all factors ≡ 1 mod 3 is O(1/√log n))
   - Erdős-Ginzburg-Ziv theorem (every 2n-1 integers have n summing to 0 mod n)
   - Ad hoc pigeonhole on the window of ~p/2 values of A
   - Dyachenko's original lattice density argument from arXiv:2511.07465

## Output Format

Please provide:

1. **A numbered list of lemma statements** (in Lean 4 syntax or precise mathematical notation) that together prove the sorry.
2. **For each lemma**: a 1-2 sentence proof sketch.
3. **Difficulty rating** for each lemma: Easy (omega/native_decide), Medium (requires some Mathlib), Hard (requires substantial argument), Very Hard (may need new mathematical ideas).
4. **The critical bottleneck**: which lemma is hardest and what mathematical machinery does it require?
5. **An honest assessment**: Is this decomposition achievable? What's the weakest link?

## Important Notes

- The proof is in Lean 4 with Mathlib (not Lean 3).
- `native_decide` can handle large finite decidable propositions efficiently.
- `omega` handles linear arithmetic over ℕ and ℤ.
- `linear_combination` handles polynomial identities in ℤ.
- We do NOT need constructive witnesses for the AI proof — `sorry`-free existential proofs are fine.
- Lean 4's `Decidable` instances propagate through ∃ over `Finset` ranges, ∧, etc.

## Computational Data

Offsets needed for primes p ≡ 1 (mod 24) up to 1000:
- p=73: offset=7 (A=20, b=3, c=60)
- p=97: offset=7 (A=26, b=4, c=338)
- p=193: offset=7 (A=50, b=10, c=25)
- p=241: offset=7 (A=62, b=9, c=558)
- p=313: offset=7 (A=80, b=12, c=240)
- p=337: offset=3 (A=85, b=170, c=17)
- p=409: offset=7 (A=104, b=15, c=1560)
- p=433: offset=7 (A=110, b=16, c=880)
- p=457: offset=3 (A=115, b=2530, c=23)
- p=529: not prime
- p=577: offset=3 (A=145, b=2030, c=29)
- p=601: offset=3 (A=151, b=15100, c=302)
- p=625: not prime
- p=673: offset=7 (A=170, b=25, c=1700)
- p=697: not prime (17*41)
- p=745: not prime
- p=769: offset=3 (A=193, b=37249, c=386)
- p=793: not prime
- p=937: offset=7 (A=236, b=34, c=13924)
- p=1009: offset=3 (A=253, b=23, c=64009)

Most primes work with offset=3. Those that don't have A=(p+3)/4 prime with A ≡ 1 (mod 3).
