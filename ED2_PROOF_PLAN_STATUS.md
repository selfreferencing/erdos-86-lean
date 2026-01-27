# ED2 Proof Plan Status

## Date: Session in progress

## Summary

We attempted to eliminate the `dyachenko_type3_existence` axiom using CRT certificates. This approach **failed** for Mordell-hard residue classes due to Mordell's quadratic-residue obstruction.

After consulting 5 AI systems (2 GPT Thinkings, 1 GPT Pro, 2 Gemini Deep Thinks), we have **unanimous consensus**:

**ED2/lattice point counting is the minimal machinery needed.**

---

## What We Proved (in ESC_TypeII_Prime_Covering.lean)

1. `type2_mod7_eq_6` - p ≡ 6 (mod 7) case with offset=7, k=1
2. `type2_mod7_eq_3` - p ≡ 3 (mod 7) with p ≡ 1 (mod 8), offset=7, k=2
3. `type3_2521` - Type III solution via native_decide
4. `type3_196561` - Type III solution via native_decide
5. `type3_402529` - Type III solution via native_decide
6. `type3_935761` - Type III solution via native_decide

## Remaining Sorries (3)

1. `dvd_poly_of_modEq` - polynomial congruence helper
2. `type2_mordell_large_offset` - Mordell-hard coverage (CRT approach FAILED)
3. `esc_1_mod_4_complete` - main theorem

---

## Why CRT Failed

GPT analysis confirmed: No uniform (offset, k) exists for Mordell-hard residue classes {1, 121, 169, 289, 361, 529} mod 840 under the constraint `4*offset*k | 840`.

The problem is structural: Mordell's obstruction prevents finite modular identity covers from working for quadratic residue classes.

---

## The ED2 Solution (Consensus from 5 AI systems)

### The Key Identity
```
4bc - b - c = pδ
```
where δ corresponds to `offset`.

### The Affine Lattice L_p
Triples (b, c, δ) satisfying the linear identity form an affine lattice of finite index in ℤ³.

### The Geometric Guarantee
Blichfeldt/Minkowski: if the parametric box volume exceeds the lattice covolume, a lattice point must exist.

### Mathlib Infrastructure (already exists)
- `Mathlib.MeasureTheory.Group.GeometryOfNumbers` - Blichfeldt/Minkowski
- `Mathlib.Data.ZMod.Basic` - CRT infrastructure

### Key Reference
Dyachenko 2025 preprint: arXiv 2511.07465
"Constructive Proofs of the Erdős–Straus Conjecture for Prime Numbers ≡ 1 (mod 4)"

---

## Progress Update (Session 2 - Claude Code)

### WindowLattice.lean: FULLY PROVEN (0 sorries)
- `ED2KernelLattice` - Kernel lattice AddSubgroup definition
- `mem_kernel_iff` - Membership criterion
- `v1_mem` - (c', -b') is in the lattice
- `v2_mem` - **(d', d') is in the lattice** - PROVEN
- `exists_unique_Ico_modEq` - **Division algorithm for intervals** - PROVEN
- `ed2_window_lemma` - **Prop 9.25: g x g rectangle contains lattice point** - PROVEN
- `kernel_lattice_index` - **Index = g** - PROVEN (Session 3: GPT draft + Claude fix)

### Bridge.lean: FULLY PROVEN (0 sorries)
- `type3Z_works` - Integer Type III predicate
- `typeIIeq_to_type3Z` - **Type II equation implies Type III** - PROVEN
- `type3_works` - Natural number Type III predicate
- `type3_nat_to_int` - **ℕ to ℤ lifting** - PROVEN
- `type3_int_to_nat` - **ℤ to ℕ conversion** - PROVEN
- `ED2Params` - Structure with ed2_id and hδA fields
- `type3_of_ed2` - **ED2 parameters yield Type III solution** - PROVEN

### Existence.lean: 2 sorries remaining (1 critical, narrowed to p ≡ 1 mod 24)
- `A_window_width` - Proven (ℚ version)
- `A_window_nonempty` - **PROVEN** (ℚ version)
- `A_window_nonempty_nat` - **PROVEN** (ℕ version)
- `offset_mod4` - Proven
- **`ed2_exists`** - **3/4 PROVEN** (Session 4: modular cascade)
  - Step 1: A-window + offset definition - PROVEN
  - Step 2: Core Type II equation existence:
    - p ≡ 2 (mod 3) [= p ≡ 5, 17 mod 24] - **PROVEN** (offset=3, c=(p+7)/12)
    - p ≡ 1 (mod 3), p ≡ 5 (mod 8) [= p ≡ 13 mod 24] - **PROVEN** (offset=3, c=(p+11)/12)
    - p ≡ 1 (mod 24) - **SORRY** (line 193, requires Dyachenko lattice density)
  - Step 3: d > 0 and d | product from Type II - PROVEN (via ℤ algebra)
- `dyachenko_type3_existence_theorem` - Delegates to ed2_exists (p=5 handled by native_decide)
- `type3_to_egyptian` - Sorry (not on critical path)

### Sorry Summary
**Critical path sorry: 1** (line 193 in ed2_exists: p ≡ 1 mod 24 only — 1/4 of original scope)
**Non-critical sorries: 1** (type3_to_egyptian)

### CRITICAL FINDING: The Sorry at Line 118 is UNPROVABLE as Written

**The current proof structure hard-codes `A = (p+3)/4`, giving `offset = 3`.**
This does NOT work for all primes. Counterexample: **p = 73**.

For p = 73, A = 19, offset = 3: the equation `(p+3)(b+c) = 12bc` has NO
positive integer solutions. (Proved computationally: 19*(b+c) = 3*b*c requires
divisor of 19^2 = 361 in residue class 2 mod 3, but all divisors of 361
are {1, 19, 361}, all congruent to 1 mod 3.)

**Primes failing with offset=3 (up to 500):** 73, 193, 241, 313, 409, 433
(6 out of 44 primes, all are primes where A = (p+3)/4 is prime and A = 1 mod 3)

**All failing primes are fixed by using a DIFFERENT offset:**
- p=73: A=20, offset=7, b=3, c=60
- p=193: A=50, offset=7, b=10, c=25
- p=241: A=62, offset=7, b=9, c=558
- p=313: A=80, offset=7, b=12, c=240
- p=409: A=104, offset=7, b=15, c=1560
- p=433: A=110, offset=7, b=16, c=880

**Up to 50000:** offset=3 covers 87% of primes. The remaining 13% need
offset=7 (10%), offset=11 (1.7%), offset=15/19/23/31 (rare).

### Mathematical Analysis: BC = A^2 Factorization

The Type II equation (p+offset)(b+c) = 4*offset*b*c is equivalent to:
```
B*C = A^2  where B = offset*b - A, C = offset*c - A, A = (p+offset)/4
```
A solution exists iff A^2 has a divisor d with d = -A (mod offset).
Since gcd(A, offset) = gcd(A, 4A-p) = gcd(A, p) = 1 (p prime, A < p),
the condition d_1 = -A (mod offset) automatically implies d_2 = A^2/d_1 = -A (mod offset).

**Key obstacle:** When A is prime and A = 1 (mod offset), ALL divisors of A^2
are = 1 (mod offset), so no divisor can be = -A = -1 (mod offset) unless
offset | 2, which is impossible since offset is odd.

### Required Fix: The Proof Must Allow Variable A

The proof must NOT fix A = (p+3)/4. Instead, it must existentially quantify over A:
```
exists A in window, exists b c > 0, offset*b*c = A*(b+c) where offset = 4A - p
```
The proof strategy should either:
1. **Multi-offset cascade:** Try offset=3, then 7, then 11, ..., prove one works
2. **Window lemma:** Use lattice geometry to prove existence for SOME A
3. **Divisor theory:** Prove A^2 has a divisor in the right residue class for some A

Note: The window lemma gives LATTICE points satisfying p | (u*offset + v*A),
a LINEAR condition. The ED2 identity is QUADRATIC (offset*bc = A*(b+c)). The
connection between these is NOT direct and requires additional mathematical
argument beyond what the current plan describes.

### GPT Outputs Will Likely Fail

Since the sorry is unprovable for p = 73, any GPT proof that doesn't restructure
to allow variable A is mathematically incorrect. The GPTs will either:
- Produce a proof with a subtle bug
- Identify the same issue and flag it
- Produce something that compiles but uses sorry or admits

---

## Files and Status

- `ErdosStraus/ED2/WindowLattice.lean` - **COMPILES, 0 sorries**
- `ErdosStraus/ED2/Bridge.lean` - **COMPILES, 0 sorries**
- `ErdosStraus/ED2/Existence.lean` - **COMPILES, 3 sorries** (1 critical at line 118, BUT UNPROVABLE AS WRITTEN)

---

## Key Insight

**The axiom is not "magic" - it encodes a Type II Erdos-Straus decomposition.**

Proving it for ALL primes requires ED2/lattice machinery, not CRT certificates.
The CRT approach works for 89/96 residue classes but fundamentally cannot cover Mordell-hard classes uniformly.

The window lemma and bridge lemma are now fully proven in Lean 4.
The remaining gap requires restructuring ed2_exists to allow variable A (not fixed
to (p+3)/4) and connecting the lattice geometry to the BC = A^2 factorization.

### Possible Path Forward

The BC = A^2 factorization reduces the problem to: for each prime p = 1 (mod 4),
find A in [(p+3)/4, (3p-3)/4] such that A^2 has a divisor d = -A (mod 4A-p).

The simplest sufficient condition: find A with (4A-p) | (A+1). This means
(4A-p) | (p+4), so we need a divisor delta of (p+4) with delta = 3 (mod 4)
and (p+4)/delta = 3 (mod 4). Both factors must be = 3 (mod 4), which requires
p+4 to have prime factors = 3 (mod 4).

This covers many primes but NOT all (fails when p+4 has only factors = 1 mod 4,
e.g., p = 97 where p+4 = 101 is prime = 1 mod 4).

For a complete proof, multiple factorization strategies must be combined, or
the window lemma must be applied with a more sophisticated parameterization.

---

## Option 5 Results (GPT Fleet, Session 5)

### Outcome: All three GPTs confirmed the sorry requires a deep lemma.

**GPT Pro**: "Can't do it, call a lemma." No mathematical content.
**GPT Thinking #1**: Same conclusion.
**GPT Thinking #2**: Did real computation. Key findings:

#### Parametric Construction (from GPT Thinking #2 traces)
If `m | (p + 4)` and `m ≡ 3 (mod 4)`, then:
- offset = (p+4)/m (need offset ≡ 3 mod 4 — holds when (p+4)/m ≡ 3 mod 4)
- A = (p + offset)/4
- b₀ = (m+1)/4, c₀ = A*b₀
- This gives a valid Type II solution

**Method 1**: Divisor of p+4 ≡ 3 (mod 4) → works for ~80% of p ≡ 1 (mod 24)
**Method 2**: Divisor of p+8 ≡ 7 (mod 8) → catches more
**Combined gap**: 65 primes still fail both methods up to 20,000

First few "bad" primes (fail methods 1+2): 193, 313, 673, 1009, 1033, 1153, 1321, 1489...

#### Generalized Framework
For integer t ≥ 1, check if p + 4t has a divisor m with m ≡ 3 (mod 4):
- t=1: check p+4
- t=2: check p+8
- t=3: check p+12
- etc.

The question reduces to: **among p+4, p+8, p+12, ..., p+4T (for T up to ~p/2),
does at least one have a factor ≡ 3 (mod 4)?**

This is equivalent to: does at least one of these numbers have a prime factor ≡ 3 (mod 4)?

A number has ALL prime factors ≡ 1 (mod 4) iff it's a sum of two squares (by Fermat).
So the question is: among p+4, p+8, ..., is there one that is NOT a sum of two squares?

The density of sums of two squares among integers up to N is ~C/√(log N) → 0.
So for large p, the answer is overwhelmingly YES.

### Implication for Strategy
The proof should combine:
1. **Finite check** (native_decide) for p ≤ B
2. **Density/pigeonhole** for p > B: among ~p/2 values in the window,
   not all can have exclusively ≡ 1 (mod 4) prime factors

---

## Option 3 Micro Results (3 GPT Fleet, Session 5)

### Consensus: 4-layer decomposition, Layer 4 is the only "Very Hard"

**Layer 1 (Algebraic infrastructure, ~15 lemmas):** Easy-Medium
- BC = A^2 factorization (ring_nf)
- Divisor + congruence → construct b,c (medium, Nat/Int bridging)
- Coprimality: gcd(A, delta) = gcd(A, p) = 1 since p prime, A < p (medium)
- Modular transfer: d = -A (mod delta) + d|A^2 + coprime → A^2/d = -A (mod delta) (hard-ish but local)

**Layer 2 (Offset characterization):** Medium
- offset=3 works iff A has a prime factor = 2 (mod 3)
- Decidable predicate on A

**Layer 3 (Finite computation):** Easy-Medium
- Define decidable `good_offset` checker in pure Nat
- Prove soundness: good_offset → TypeII solution exists
- native_decide for all primes p <= B with p = 1 (mod 24)

**Layer 4 (Infinite coverage):** **VERY HARD** (all 3 agree)
- "For all primes p > B and p = 1 (mod 24), some offset in finite set S works"
- This is the ONLY Very Hard lemma in the entire decomposition
- Options: sieve/density, Dyachenko lattice, or clever algebraic trick
- None of the 3 GPTs found a way to avoid this layer

### Engineering recommendation (from Thinking #2):
```
def good_offset (p delta : Nat) : Prop :=
  delta % 4 = 3 ∧ (p + delta) % 4 = 0 ∧
  let A := (p + delta) / 4
  ∃ d1 d2 : Nat, d1 > 0 ∧ d2 > 0 ∧ d1 * d2 = A^2 ∧
    (A + d1) % delta = 0 ∧ (A + d2) % delta = 0
```
Prove soundness once, then native_decide for finite range.

---

## Option 3 Macro Results (3 GPT + 1 Gemini Fleet, Session 5)

### Unanimous Recommendation: Use Existing WindowLattice.lean

All 4 macro responses agree:
1. Don't attack the divisor-residue problem (BC = A^2) directly
2. Use the ED2 lattice + window lemma (already proven)
3. Bridge from lattice point to Type II solution (already proven)
4. Hybrid: native_decide for small p, lattice for large p

Line estimates: 80-400 lines depending on glue needed.
All cite Dyachenko paper: Prop 9.25, Lemma D.16, Def D.32, Lemma D.33.

### CRITICAL GAP: The Linear-to-Quadratic Bridge

**None of the 4 macros explain the actual mathematical connection.**

What WindowLattice gives: point (u,v) in Z^2 with g | (u*b' + v*c') (LINEAR)
What we need: (offset, b, c) with (p+offset)(b+c) = 4*offset*b*c (QUADRATIC)

All 4 say "Dyachenko's Lemma D.16 handles this" but none reproduce the content.
They reference the "back-test" / "reconstruction" / "normalization" but don't explain:
- What g, b', c' should be (lattice parameters)
- How (u,v) maps to (offset, b, c)
- Why the quadratic condition follows from the linear one

### Next Step: Read Dyachenko Paper

Specific sections to read:
- Section 9 (ED2 lattice setup, Prop 9.25)
- Appendix D (back-test: Lemma D.16, normalization: Def D.32 + Lemma D.33)
- Theorem 9.21 / 10.21 (main existence result)

The paper is at arXiv:2511.07465.
Goal: extract the EXACT parameterization that connects our WindowLattice.lean
to the Type II equation, then formalize it.

### Alternative: Skip Dyachenko, Use Computational Approach

If the paper connection is too complex to formalize, fall back to:
1. Define decidable `good_offset` checker (from micro Layer 3)
2. native_decide for p <= B (some large bound)
3. For p > B, use a SIMPLER density argument
   (e.g., among p/2 consecutive integers, at least one has a factor = 2 mod 3,
   so offset=3 works for that A)

---

## Dyachenko Section 9 Analysis (Session 6)

### What Section 9 Contains

Section 9 ("Algorithm convergence and conditional completeness of coverage") has 13 subsections.
The section establishes the FRAMEWORK for proving ED2 existence but repeatedly delegates
the critical bridge to **Appendix D**. Here is the structure:

#### §9.1-9.2: Lattice Density Theorems (Thm 9.1, 9.2)
- Points in an affine lattice Λ ⊂ Z^k of index M in a parametric box B_k(T) number T^k/M + O(T^{k-1})
- For T = (log P)^A, this gives logarithmic growth
- **Remark 9.4 (CRITICAL)**: These theorems "by themselves do NOT guarantee the existence
  of solutions to the nonlinear identity (4b-1)(4c-1) = 4Pδ+1."
  To bridge geometry → existence requires EXTERNAL INPUT:
  either BV-type averaging or the (t,k) parametrization of §9.10.

#### §9.3-9.6: Affine Lattice Structure for ED2
- The ED2 conditions define an affine class u₀ + Λ_ED2 where Λ_ED2 ⊂ Z³
- Parametrization: α square-free, d' ∈ ℕ, g = α·d', δ = α·(d')²
- b = g·b', c = g·c', gcd(b', c') = 1
- Identity: (4gb' - 1)(4gc' - 1) = 4Pδ + 1
- Linear congruences: δ ≡ 0 (mod m₃), b ≡ 0 (mod g), c ≡ 0 (mod g)
- Lattice index [Z³ : Λ_ED2] = m₃·g² (independent of P)
- **Numerical example (P=73)**: α=1, d'=3, g=3, δ=9, b'=1, c'=20, b=3, c=60
  Gives 4/73 = 1/20 + 1/219 + 1/4380 ✓

#### §9.7-9.8: Box II and ED1 Method
- Type II boxes (quadratic surfaces) NOT used in main proofs — groundwork for future
- ED1 uses factorization identity (γA-c)(γB-c) = c², NOT an affine lattice
- ED1 handled separately via divisor counting (Lemma 9.17)

#### §9.9: ED2 Method Setup (Theorem 9.19)
- Core identity: rs = 4Pδ + 1 with r ≡ s ≡ 3 (mod 4)
- b = (r+1)/4, c = (s+1)/4, A = bc/δ, B = bP, C = cP
- Set C_ED2(P) = {admissible triples (δ,b,c)} satisfying all conditions

#### §9.10: THE KEY SECTION — "Unconditionality for the ED2 algorithm"
**Theorem 9.21**: For any prime P ≡ 1 (mod 4), there exists 4/P = 1/A + 1/(bP) + 1/(cP).

The proof assembles three pieces:
(I) Mathematical conditions (the ED2 identity and auxiliary constraints)
(II) Algorithmic conditions (Type I box, affine lattice membership)
(III) **Unconditional guarantee** via:

**Lemma 9.22** (= our WindowLattice.lean):
L = {(u,v) ∈ Z² : u·b' + v·c' ≡ 0 (mod g)} has index g, contains
v₁ = (c', -b') and v₂ = (d', d') where d' = g/α.

**Proposition 9.25** (= our ed2_window_lemma):
If H ≥ d' and W ≥ d', then L ∩ [x₀, x₀+H) × [y₀, y₀+W) ≠ ∅.

**The Bridge** (→ Appendix D):
"from u = m·d', u ≡ v (mod 2) and u² - v² = 4A/α we obtain
b' = (u+v)/2, c' = (u-v)/2 and the required b, c, A."
Uses: Lemma D.33 (sum and discriminant), Lemma D.16 (back-test).

#### §9.11: ED2 Does Not Require Factorization (Prop 9.28)
- Uses only: integer ops, gcd, Legendre/Jacobi symbols, linear formulas
- Relies on: D.33 (normalization), D.16 (back-test), D.2 (quadratic reparametrization)

#### §9.12: Enumeration Algorithm
- **Lemma 9.30 (IMPORTANT for alternative bridge)**:
  ∃ δ, a with a | (P+δ) and a ≡ -1 (mod δ) IFF ∃ t, k ∈ ℕ with D = tk-1 such that
  D | (P+t) and D | (kP+1), giving δ = (P+t)/D, a = (kP+1)/D.
- This is a PARAMETRIC approach: for fixed k, the conditions are LINEAR divisibility.

#### §9.12.1-9.13: ED2↔ED1 Correspondence (Convolution/Anticonvolution)
- Theorem 9.31: ED2 triple → ED1 quadruple via γ = (4c-1)/P, u = γA-c, v = γB-c
- Theorem 9.34: Correctness of convolution
- Theorem 9.41: Non-emptiness of ED2 from non-emptiness of ED1
- Canonical subclass for 1-1 correspondence

### What Section 9 Does NOT Contain

1. **The actual normalization formulas** (→ Appendix D, Lemma D.33)
2. **The back-test** (→ Appendix D, Lemma D.16)
3. **The quadratic reparametrization** (→ Appendix D, Theorem D.2)
4. **The complete proof that Prop 9.25 lattice point → ED2 solution**
   (the bridge goes through Appendix D)

### The Linear-to-Quadratic Bridge: What We Now Know

**The chain of reasoning in Theorem 9.21:**
1. Fix α (square-free), d' ∈ ℕ → g = α·d', δ = α·(d')²
2. Define kernel lattice L with parameters g, b', c'
3. Prop 9.25: L has a point in any d'×d' box
4. Appendix D normalization: lattice point (u,v) → (b', c') via
   - u = m·d' for some m
   - u ≡ v (mod 2)
   - u² - v² = 4A/α = 4b'c' (this is the QUADRATIC condition)
   - b' = (u+v)/2, c' = (u-v)/2
5. Then b = g·b', c = g·c' gives the ED2 solution

**The gap**: Step 4 requires showing that the lattice point from Prop 9.25
satisfies the QUADRATIC condition u² - v² = 4A/α, not just the LINEAR
congruence u·b' + v·c' ≡ 0 (mod g). This is what Appendix D handles.

**Remark 9.4 explicitly confirms**: the density theorems alone don't bridge this.
The paper uses either BV averaging or the (t,k) parametrization.

### Potential Alternative Bridge: The (t,k) Parametrization (Lemma 9.30)

This might bypass Appendix D entirely:
- For fixed k ∈ ℕ, we need D = tk-1 such that D | (kP+1)
- Any divisor D of (kP+1) with D ≡ -1 (mod k) gives t = (D+1)/k
- Then δ = (P+t)/D, a = (kP+1)/D
- For k=1: need (t-1) | (P+1), giving δ = (P+t)/(t-1)
- For k=2: need D | (2P+1) with D odd, giving δ = (P + (D+1)/2)/D
- The conditions are pure divisibility of KNOWN quantities (P+1, 2P+1, 3P+1, ...)

**Key question**: does the (t,k) parametrization ALWAYS produce a valid triple (δ,b,c)?
Or does it also require Appendix D to complete the construction?
Answer: Lemma 9.30 gives δ and a with a | (P+δ) and a ≡ -1 (mod δ).
From §9.9 (Theorem 9.19): given δ, factor 4Pδ+1 = rs with r ≡ s ≡ 3 (mod 4),
then b = (r+1)/4, c = (s+1)/4. So the (t,k) parametrization gives δ,
but you STILL need to factor 4Pδ+1 to get b and c. The factorization is
guaranteed to exist (it's a product of two factors ≡ 3 mod 4), but proving
the EXISTENCE of such a factorization requires additional work.

### Assessment: We Need Appendix D

Section 9 provides the framework but NOT the bridge. All three critical lemmas
(D.16, D.33, D.2) are in Appendix D. Without Appendix D, we cannot formalize
the connection between our proven WindowLattice.lean and the Type II equation.

**Action item**: Read and analyze Appendix D next.

---

## Dyachenko Appendix D Analysis (Session 6, continued)

### Overview

Appendix D ("Additional analysis for Theorem 9.21") has 17 subsections (D.1-D.17).
It contains the ALGEBRAIC CORE that Section 9 delegates to. The good news: these are
clean algebraic identities, formalizable in Lean. The surprising news: the paper
still does not exhibit an explicit covering for p ≡ 1 (mod 24).

### D.1: Algebraic Core — Theorem D.1 (THE KEY THEOREM)

**Theorem D.1**: Let A = α·b'·c' and m = 4A - P > 0. Then EQUIVALENT:
1. ∃ d' ∈ ℕ: (4αd'b' - 1)(4αd'c' - 1) = 4αP(d')² + 1
2. b'c' = A/α AND (b' + c') ≡ 0 (mod m), with d' = (b'+c')/m

**Proof is 4 lines of algebra**: expand LHS, equate to RHS, factor out 4α, cancel d'.

**Implication**: The QUADRATIC ED2 identity reduces to TWO conditions:
- A PRODUCT condition: b'c' = M = A/α
- A SUM-DIVISIBILITY condition: m | (b' + c')
- The parameter d' is then DETERMINED: d' = (b'+c')/m

This is the bridge we were looking for. The quadratic identity is
EQUIVALENT to a product constraint + a linear congruence on the sum.

### D.2: Quadratic Reparametrization — Theorem D.2

b', c' are roots of x² - Sx + M = 0 where S = md', M = A/α.
Discriminant Δ = S² - 4M must be a perfect square.

### D.6: Left Parametrization — Lemma D.6 (THE CONSTRUCTIVE LEMMA)

**Lemma D.6**: For any r, s ∈ ℕ, set M_{r,s} = 4αsr - 1.
If M_{r,s} | (4αs² + P), then with:
- d' = r, b' = s, c' = mr - s (where m = (4αs² + P)/M_{r,s})
- A = αs(mr - s)
The ED2 identity holds and A ∈ ℕ.

**Proof is direct substitution + verification of the identity.**

This is UNCONDITIONAL once you have a pair (r, s) satisfying the divisibility.
No lattice needed. No back-test needed. Pure divisibility.

### D.8: Back-Test — Lemma D.16

**Lemma D.16**: For fixed (α, P, A) with m = 4A - P > 0 and M = A/α,
an integer point (u, v) gives an ED2 solution IFF:
- m | u
- u ≡ v (mod 2)
- u² - v² = 4M

Where u = b'+c', v = b'-c' (the normalization from D.32-D.33).

This is the "reverse check": given coordinates (u,v), verify the ED2 identity
with three simple arithmetic conditions.

### D.12-D.13: Covering Scheme — Theorem D.14

**Theorem D.14 (Existence under covering)**:
If a finite family F = {(r_i, s_i)} has the property that for every residue
p mod Q = lcm(M_i), some (r_i, s_i) satisfies:
- P ≡ -4αs_i² (mod M_i)
- A_{r_i,s_i}(P) ∈ [L(P), U(P)]
Then for ANY odd prime P, there exists a valid A in the window.

**The proof is clean**: reduce P mod Q, find the covering index, verify
the affine bounds (using λ_{r,s} ∈ (1/4, 1/3]).

### D.12: Corollary D.26 (Single-Class Criterion, s=1)

**For α=1, s=1**: If (P+4) has a divisor d ≡ 3 (mod 4), then r = (d+1)/4
gives a valid ED2 solution.

This is EXACTLY what GPT Thinking #2 found in Option 5!
Fails when ALL prime factors of P+4 are ≡ 1 (mod 4) (i.e., P+4 is a sum of two squares).

### D.13: Normalization — Definition D.32, Lemma D.33

u = b' + c', v = b' - c'. Then S = u, Δ = v², M = (u²-v²)/4.
This is the coordinate change connecting Theorem D.1 to Lemma D.16.
Trivial to formalize.

### What Appendix D Does NOT Contain

1. **An explicit covering set for p ≡ 1 (mod 24)**
   Theorem D.14 says "IF a covering exists THEN solutions exist for all P."
   But it does not EXHIBIT such a covering.

2. **A proof that the covering exists**
   The paper's actual unconditional guarantee seems to come from Section 9.10
   (lattice + Prop 9.25), not from an explicit finite covering.

3. **The gap remains**: How does the LINEAR lattice condition from Prop 9.25
   yield a point satisfying the QUADRATIC condition u² - v² = 4M?
   Appendix D provides the algebraic equivalences but not the geometric-to-
   algebraic bridge.

### Connecting Appendix D to Our Lean Code

**Parameter mapping:**
- Our `offset` = Dyachenko's m = 4A - P
- Our `b`, `c` in Type II equation = Dyachenko's b = g·b', c = g·c'
- g = α·d', δ = α·(d')²
- offset % 4 = 3 follows automatically: m = 4A - P ≡ -P ≡ -1 ≡ 3 (mod 4)

**Verification for P=73:**
α=1, d'=3, g=3, b'=1, c'=20, A=20, m=7 (=offset)
b=3, c=60: (73+7)(3+60) = 80·63 = 5040 = 4·7·3·60 = 5040 ✓

**Verification for P=97:**
α=2, d'=2, g=4, b'=1, c'=13, M=13, A=26, m=7 (=offset)
b=4, c=52: (97+7)(4+52) = 104·56 = 5824 = 4·7·4·52 = 5824 ✓
b'+c'=14, m=7, d'=14/7=2 ✓. b'c'=13=A/α=26/2 ✓.

### The Simplest Formalization Path (Updated Assessment)

**The algebraic core is now clear and formalizable:**

1. **Lemma D.6 in Lean** (~40-60 lines):
   For (r, s, α) with (4αsr-1) | (4αs²+P), construct explicit (offset, b, c)
   satisfying the Type II equation. Proof by `linear_combination`.

2. **Soundness** (~20 lines):
   The constructed (offset, b, c) satisfy offset % 4 = 3, b > 0, c > 0.
   Proof by `omega` and modular arithmetic.

**The existence question has three sub-approaches:**

**(A) Finite modular covering** (Theorem D.14):
Find a finite set of (r_i, s_i, α_i) whose congruences cover all P ≡ 1 (mod 24).
Verify computationally that A lands in the window for each case.
This converts the entire problem to a FINITE CHECK, which native_decide can handle.

**(B) Computational brute force**:
For all P ≡ 1 (mod 24) up to bound B: native_decide with the Lemma D.6 construction.
For P > B: need a covering or density argument.

**(C) The lattice path** (Section 9 + Appendix D together):
Use WindowLattice.lean (Prop 9.25) to guarantee a lattice point,
then Lemma D.16 to verify it gives an ED2 solution.
PROBLEM: the lattice condition is LINEAR but the back-test has a QUADRATIC condition.
The bridge between these is still not fully clear from the paper.

**Recommendation: Path (A) is the most promising.**
If we can find a small covering, the ENTIRE proof reduces to:
- Lemma D.6 algebraic construction (formalizable)
- Theorem D.14 covering verification (native_decide)
- No lattice needed, no density needed, no analytic NT

**The key question: can we find such a covering?**
This is a computational search problem. For each (r, s, α), the covered
residue class is P ≡ -4αs² (mod 4αsr-1). We need enough of these
to cover all P ≡ 1 (mod 24).

Small examples:
- (r=1, s=1, α=1): M=3, covers P ≡ 2 (mod 3) → handles P ≡ 5,17 (mod 24)
- (r=1, s=2, α=1): M=7, covers P ≡ 5 (mod 7)
- (r=2, s=1, α=1): M=7, covers P ≡ 3 (mod 7)
- (r=1, s=1, α=2): M=7, covers P ≡ 1 (mod 7)... wait, let me check.
  M = 4·2·1·1 - 1 = 7. Condition: 7 | (4·2·1 + P) = 8+P. So P ≡ -8 ≡ 6 (mod 7).
- (r=3, s=1, α=1): M=11, covers P ≡ 7 (mod 11)
- (r=1, s=3, α=1): M=11, covers P ≡ 8 (mod 11)
- etc.

We need enough (r, s, α) triples so that for every P ≡ 1 (mod 24),
at least one congruence is satisfied AND A is in the window.

**This is a finite search over a finite problem. It should be doable computationally.**
