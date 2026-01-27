# Prompt: Macro Strategy — What Is the Simplest Proof Path for p ≡ 1 (mod 24)?

## Context

We are formalizing the Erdős-Straus Conjecture (4/n = 1/x + 1/y + 1/z for all n ≥ 2) in Lean 4 with Mathlib. We have reduced the ENTIRE conjecture to a single sorry:

**For every prime p ≡ 1 (mod 24) with p ≥ 5, there exist natural numbers offset, b, c with offset ≡ 3 (mod 4), b > 0, c > 0, and (p + offset)(b + c) = 4 · offset · b · c.**

Everything else compiles with zero sorries: the full ESC proof for all n ≥ 2, conditional only on this one statement.

## What We Know

### The algebraic reformulation
Setting A = (p + offset)/4, the equation becomes BC = A² where B = offset·b - A, C = offset·c - A. A solution exists iff A² has a positive divisor d ≡ -A (mod offset).

### What's already proven in Lean 4
- **p ≡ 2 (mod 3)** (i.e., p ≡ 5 or 17 mod 24): offset=3 works. Explicit algebraic proof.
- **p ≡ 1 (mod 3), p ≡ 5 (mod 8)** (i.e., p ≡ 13 mod 24): offset=3 works. Explicit algebraic proof.
- **WindowLattice.lean**: ED2 kernel lattice, window lemma (rectangles ≥ d' × d' contain lattice points), index calculation. Zero sorries.
- **Bridge.lean**: Type II equation implies Type III solution, ℕ↔ℤ conversion. Zero sorries.

### Why p ≡ 1 (mod 24) is hard
- offset=3 fails when A = (p+3)/4 is prime and ≡ 1 (mod 3). Example: p = 73, A = 19.
- No SINGLE fixed offset works for all primes in this class.
- Different primes need different offsets: 87% need offset=3, 10% need offset=7, 1.7% need offset=11, remainder need offset=15/19/23/31/etc.
- Max offset needed for p ≤ 100,000: 63 (for p = 87481).

### Relevant existing infrastructure
- Mathlib has `Nat.Prime`, `Nat.Coprime`, `Nat.gcd`, divisibility, modular arithmetic, `ZMod`, `Finset`, Chinese Remainder Theorem.
- Mathlib has `MeasureTheory.Group.GeometryOfNumbers` (Blichfeldt, Minkowski) but these apply to convex bodies with positive VOLUME, not to the 1D hyperbola BC = A².
- `native_decide` can verify decidable propositions computationally (large finite checks are feasible).
- `omega` handles linear arithmetic; `linear_combination` handles polynomial ℤ identities.

### Key reference
Dyachenko 2025 preprint (arXiv:2511.07465): "Constructive Proofs of the Erdős–Straus Conjecture for Prime Numbers ≡ 1 (mod 4)." Uses lattice density arguments (Theorems 9.21 and 10.21).

## The Question

**What is the simplest self-contained mathematical proof that for every prime p ≡ 1 (mod 24), there exists an integer A with (p+3)/4 ≤ A ≤ (3p-3)/4 such that A² has a positive divisor d ≡ -A (mod 4A-p)?**

Please consider:

### Approach 1: Pure computation + finite bound
Can we find B such that:
- For p ≤ B: verify by finite computation (we have `native_decide`)
- For p > B: the proof becomes trivial by some simple argument

What would the simple argument for large p be? Is there a B where the large-p case is genuinely easy?

### Approach 2: Modular cascade to exhaustion
Keep splitting p ≡ 1 (mod 24) into finer residue classes (mod 120, mod 840, mod 2520, etc.) and prove each with a specific offset. Does this process TERMINATE? Is there a finite set of residue classes that covers everything?

Key obstacle: Mordell's theorem says this CAN'T work with a single offset. But can it work with a finite LIST of offsets where you try offset=3, then 7, then 11, etc.?

### Approach 3: Density/counting argument
Among ~p/2 values of A in the window, show that at least one has a suitable factorization. What's the simplest way to do this?

Possible tools:
- **Landau-Ramanujan theorem**: Numbers with all prime factors ≡ 1 (mod 3) have density ~C/√(log n). So for large p, most A values have a factor ≡ 2 (mod 3), making offset=3 work.
- **Erdős-Ginzburg-Ziv**: Every 2n-1 integers contain n whose sum is 0 (mod n).
- **Pigeonhole on divisor residues**: A with k prime factors has 2^k divisors, at least one in each residue class mod small numbers.
- **The window itself**: Among p/2 consecutive integers, the one that's divisible by 3 but not by 9 will work... (?)

### Approach 4: Connect to the proven window lemma
We have a fully proven window lemma: rectangles of size ≥ d' × d' contain lattice points of the ED2 kernel lattice. Can we use this? The challenge is that the lattice gives a LINEAR condition while we need a QUADRATIC factorization (BC = A²). Is there a way to bridge this gap?

### Approach 5: Elementary sufficient conditions
Find a simple sufficient condition that's easy to prove universal:
- "A has a factor ≡ 2 (mod 3)" → offset=3 works
- "A is even" → maybe offset=7 works (since A = (p+7)/4 and p ≡ 1 mod 8 gives 8|(p+7) so A even)
- "A has a factor ≡ 3 (mod 7)" → offset=7 works
- Can we show: every A in the window satisfies at least ONE of these?
- More broadly: is there a finite list of sufficient conditions, each easy to state, such that every integer satisfies at least one?

### Approach 6: Something we haven't thought of
Is there a clever observation that makes this trivial? For instance:
- A number-theoretic identity that directly constructs the offset from p
- A result about consecutive integers sharing divisibility properties
- A reformulation that avoids the divisor condition entirely

## What I Need From You

1. **Your recommended approach** with a clear mathematical argument (not just a sketch — give enough detail that a formalization team could implement it).
2. **Why it's the simplest** compared to alternatives.
3. **The key lemma** that makes the whole argument work.
4. **Potential pitfalls** — what could go wrong in formalization?
5. **A rough estimate**: how many lines of Lean 4 would this require? (Not a time estimate — a complexity estimate.)

## Constraints

- We need a proof that works in Lean 4 + Mathlib. Ideally using only:
  - `Mathlib.Data.Nat.Prime.Basic`
  - `Mathlib.Data.Int.ModEq`
  - `Mathlib.Tactic`
  - `Mathlib.Data.ZMod.Basic` (if needed)
  - Other standard Mathlib imports
- `native_decide` is available for finite verification.
- We do NOT need constructive witnesses — existential proofs are fine.
- The simpler the better. We prefer a 50-line proof using native_decide over a 500-line proof using sieve theory.
- We have successfully used `linear_combination` for polynomial ℤ identities and `omega` for linear ℕ/ℤ arithmetic.

## Bonus Question

Dyachenko's paper (arXiv:2511.07465) proves this using lattice density arguments. How does his proof work, and can it be simplified for the special case p ≡ 1 (mod 24)? We've already built the lattice infrastructure in Lean — we just need the right way to apply it.
