# Parallel AI Prompts for Closing `ed2_qr_classes` Sorry
## Erdos-Straus Conjecture Formalization - Stage 8

Generated 2026-01-26. Each prompt is self-contained.
Give each instance the full Dyachenko paper PDF (arXiv:2511.07465).
Use 10-15 instances in parallel. Mix of full-approach and component prompts.

---

## SHARED CONTEXT (copy into every prompt)

```
BACKGROUND:
We are formalizing the Erdos-Straus Conjecture (4/n = 1/x + 1/y + 1/z for all n >= 2)
in Lean 4 with Mathlib. The ENTIRE proof is complete except ONE sorry. The sorry is:

theorem ed2_qr_classes (p : ℕ) (hp : Nat.Prime p)
    (hp24 : p % 24 = 1)
    (hp7_ne0 : p % 7 ≠ 0) (hp7_ne3 : p % 7 ≠ 3)
    (hp7_ne5 : p % 7 ≠ 5) (hp7_ne6 : p % 7 ≠ 6)
    (hp5_ne0 : p % 5 ≠ 0) (hp5_ne2 : p % 5 ≠ 2) (hp5_ne3 : p % 5 ≠ 3) :
    ∃ offset b c : ℕ, offset % 4 = 3 ∧ b > 0 ∧ c > 0 ∧
    (↑p + ↑offset : ℤ) * (↑b + ↑c) = 4 * ↑offset * ↑b * ↑c

MEANING: For primes p ≡ 1 (mod 24) with p mod 7 ∈ {1,2,4} and p mod 5 ∈ {1,4},
there exist offset ≡ 3 (mod 4) and b, c > 0 satisfying the Type II equation
(p + offset)(b + c) = 4 * offset * b * c.

These are the 6 "QR obstruction classes" mod 840.

WHY IT'S HARD: The Dyachenko paper's Lemma D.6 construction always produces
M = 4*alpha*s*r - 1 ≡ 3 (mod 4). For such M, the residue condition
P ≡ -4*alpha*s^2 (mod M) is always a QNR condition. The 6 hard classes
are QR classes. No D6 extension with any parameters can reach them.
The ONLY known proof path is the paper's 2D lattice argument (§9, Prop 9.25).

LEAN 4 NOTES:
- Use: import Mathlib.Data.Nat.Prime.Basic, import Mathlib.Data.Int.ModEq, import Mathlib.Tactic
- Key tactics: omega, linarith, nlinarith, ring, linear_combination, push_cast, field_simp
- Nat.div_mul_cancel: (n / d) * d = n from d ∣ n
- NEVER hallucinate Mathlib lemma names. If unsure, prove inline.
- Minkowski's lattice point theorem is NOT in Mathlib.
- Mathlib.NumberTheory.GeometryOfNumbers does NOT exist.

THE PAPER: I'm attaching the Dyachenko 2025 paper (arXiv:2511.07465). The key sections are:
- §9: Main existence theorem (Theorem 9.21, Lemmas 9.22-9.24, Proposition 9.25)
- Appendix D: Bridge algebra (D.1, D.6, D.16, D.33)
```

---

## PROMPT 1: FULL APPROACH A — Elementary Lattice Proof
**Assign to: strongest reasoning model (o3, Thinking Claude, Gemini Deep Think)**

```
[paste SHARED CONTEXT above]

YOUR TASK: Write a COMPLETE Lean 4 proof of ed2_qr_classes that follows the paper's
lattice argument. You have the full paper attached.

The proof structure should be:

1. For a prime p satisfying the hypotheses, choose alpha = 1, g = 1 (simplest case).
   Actually, read the paper carefully -- the lattice parameters depend on the
   specific (b', c', g) decomposition. The key is Theorem 9.21 condition (III).

2. The paper proves (Prop 9.25): for ANY rectangle with sides >= d' = g/alpha,
   the lattice L = {(u,v) : u*b' + v*c' ≡ 0 (mod g)} intersects it.

3. The bridge (D.1 + D.33): a lattice point (b', c') with b'*c' = M and
   b'+c' ≡ 0 (mod m) gives the Type II identity automatically.

CRITICAL QUESTION you must answer: In Proposition 9.25, the paper claims that
choosing u* ≡ u0 (mod d') in [x0, x0+H) and v* ≡ v0 (mod d') in [y0, y0+W),
then the point p0 + m*(d',d') lands in the rectangle. But adding m*(d',d')
shifts BOTH coordinates by the same amount. How does the second coordinate
land in [y0, y0+W)?

Read the paper's proof carefully and explain the argument. Then formalize it.

Your output should be a COMPLETE .lean file that compiles. No sorry allowed.
If you get stuck, describe exactly where and what lemma you need.
```

---

## PROMPT 2: FULL APPROACH B — Avoid Lattice Theory Entirely
**Assign to: creative reasoning model**

```
[paste SHARED CONTEXT above]

YOUR TASK: Find a proof of ed2_qr_classes that does NOT use lattice theory.
The paper's approach goes through 2D lattices, but there might be simpler paths.

IDEAS TO EXPLORE:

(A) The Type II equation (p+δ)(b+c) = 4δbc can be rewritten as:
    1/b + 1/c = (p+δ)/(4δbc) * (b+c)
    Or equivalently: A*(b+c) = δ*b*c where A = (p+δ)/4 and δ = 4A-p.
    So A/c + A/b = δ. Need divisors u|A, v|A with u+v = δ.

(B) For δ ≡ 7 (mod 8) (needed since p ≡ 1 mod 8 and A must be even):
    A = (p+δ)/4 is even. We need two divisors of A summing to δ (odd).
    One divisor must be even, one odd.

(C) The A-window has width (p-3)/2. We have ~p/16 choices of δ ≡ 7 (mod 8)
    in range. For EACH δ, A_δ = (p+δ)/4. Can you prove that for p large enough,
    at least ONE of these A_δ has a divisor pair summing to δ?

(D) By Linnik's theorem or Dirichlet's theorem on primes in arithmetic progressions,
    A_δ will have small prime factors for SOME δ. Can this guarantee a divisor pair?

(E) Erdos-Kac theorem: most integers have ~log log n prime factors. The number of
    divisors τ(A) is typically ~(log A)^(log 2). For p/4 < A < 3p/4, we need
    τ(A) to be large enough that a pair sums to δ ≈ 4A - p.

You don't have to succeed. If you find a path that works, write the Lean 4 proof.
If you can reduce the problem to a simpler statement, state that clearly.
If you prove it can't work without lattice theory, explain why.
```

---

## PROMPT 3: FULL APPROACH C — Mathlib-native Lattice Approach
**Assign to: Lean 4 / Mathlib expert model**

```
[paste SHARED CONTEXT above]

YOUR TASK: Formalize the lattice argument using Mathlib's existing algebraic structures.

KEY MATHLIB STRUCTURES TO USE:
- ZMod n for modular arithmetic
- AddSubgroup for subgroups of Z^2
- Int.emod for integer modular arithmetic
- Finset.Icc or Set.Icc for intervals

The lattice L = {(u,v) ∈ Z² : u*b' + v*c' ≡ 0 (mod g)} is an AddSubgroup of Z × Z.

STEP 1: Define L and prove it's a subgroup.
STEP 2: Prove (c', -b') ∈ L and (d', d') ∈ L where d' = g / gcd(g, b'+c').
STEP 3: Prove the "rectangle hitting" property: if R = [x0, x0+H) × [y0, y0+W)
         with H ≥ d' and W ≥ d', then L ∩ R ≠ ∅.
STEP 4: Bridge to the Type II equation via Theorem D.1.

For Step 3, the key is that the DIAGONAL COSET {p0 + k*(d',d') : k ∈ Z}
is a 1D sublattice of L with spacing d' in each coordinate.

IMPORTANT: Check whether Mathlib has:
- Quotient groups of Z^n
- Index of a sublattice
- Anything about lattice points in regions

Search Mathlib for relevant lemmas before writing code. List what you find.
Write the proof even if some intermediate lemmas need sorry -- flag them clearly.
```

---

## PROMPT 4: FULL APPROACH D — Computational Certificate + Asymptotic
**Assign to: any model with good Lean 4 knowledge**

```
[paste SHARED CONTEXT above]

YOUR TASK: Try a hybrid approach:
Part 1: For p ≤ B (some explicit bound), prove ed2_qr_classes by native_decide
         or by providing explicit witnesses for each prime.
Part 2: For p > B, prove it analytically.

FOR PART 1:
The goal is existential (∃ offset b c, ...). For a SPECIFIC prime p, this is decidable
IF we bound the search space. The challenge: offset, b, c could be large.

Approach: Write a DECIDABLE search that, for a given p, checks all
offset ≤ D, b ≤ E, c ≤ E for some bounds D, E depending on p.

From computational experiments: max offset needed up to 10^7 is about 200.
Max b, c are roughly p/3. So for small p (say p ≤ 1000), a bounded search works.

Can you write:
```lean
def ed2_search (p : ℕ) (max_off max_bc : ℕ) : Bool :=
  -- search for offset ≡ 3 (mod 4), b, c > 0 satisfying Type II equation
  decide -- or explicit loop
```
and then use `native_decide` for small p?

FOR PART 2:
Read the paper's §9 and Appendix D carefully. The paper proves existence for ALL p.
Can you extract a BOUND B such that for p > B, the lattice argument is unconditional?

From the analysis: d' ≤ √δ ≤ (log p)^(A0/2), and box sides are (log p)^A0.
For the box sides to exceed d', we need (log p)^A0 ≥ (log p)^(A0/2),
which holds for all p ≥ e. So technically B = 3 works!

But the paper's "Type I box" parametrization is not what we're using in Lean.
Our Lean proof uses specific offset formulas, not the full Type I box.
You need to bridge this gap.

Produce whatever Lean code you can, with clear documentation of what's proven and what's sorry.
```

---

## PROMPT 5: COMPONENT — Theorem D.1 (Algebraic Equivalence)
**Assign to: any model. Difficulty: Medium. Independence: Full.**

```
[paste SHARED CONTEXT above]

YOUR TASK: Formalize Theorem D.1 from Appendix D of the attached paper.

STATEMENT: Let A = alpha * b' * c' with b', c', alpha ∈ ℕ, and m := 4*A - P > 0.
The identity
  (4*alpha*d'*b' - 1) * (4*alpha*d'*c' - 1) = 4*alpha*P*d'^2 + 1
holds if and only if b'*c' = A/alpha and b'+c' = m*d' (with d' = (b'+c')/m ∈ ℕ).

This is pure algebra. The proof expands the LHS, equates coefficients, and simplifies.

Write this as a Lean 4 theorem. Both directions.

FORWARD DIRECTION (the important one for us):
Given b'*c' = M and b'+c' = m*d' where M = A/alpha and m = 4*A - P,
prove the identity holds.

```lean
theorem D1_forward (alpha P A b' c' d' : ℕ)
    (hA : A = alpha * b' * c')
    (hm_pos : 4 * A > P)
    (hsum : b' + c' = (4 * A - P) * d') :
    (4 * alpha * d' * b' - 1) * (4 * alpha * d' * c' - 1) =
    4 * alpha * P * d'^2 + 1 := by
  sorry
```

CAUTION: This involves ℕ subtraction (4*A - P). You may need to work in ℤ.
The pattern from the existing code: use `push_cast`, `zify`, then `ring` or `nlinarith`.

Provide a COMPLETE proof. No sorry.
```

---

## PROMPT 6: COMPONENT — Bridge Lemma (Type II Equation from Parameters)
**Assign to: any model. Difficulty: Medium. Independence: Full.**

```
[paste SHARED CONTEXT above]

YOUR TASK: Prove the bridge from ED2 parameters to the Type II equation.

Given: prime p, and natural numbers alpha, b', c', d' satisfying:
- A := alpha * b' * c'
- m := 4 * A - p > 0  (so offset := m, and offset ≡ 3 mod 4 since p ≡ 1 mod 4)
- b' + c' = m * d'
- b := alpha * d' * b'  (so b > 0)
- c := alpha * d' * c'  (so c > 0)

Prove: (p + offset)(b + c) = 4 * offset * b * c
where offset = 4*A - p = m.

Actually wait -- let me re-derive the relationship.

From the paper: the Type II equation in our Lean file is
  (↑p + ↑offset : ℤ) * (↑b + ↑c) = 4 * ↑offset * ↑b * ↑c

where offset ≡ 3 (mod 4), b > 0, c > 0.

The ED2 identity (4*alpha*d'*b' - 1)(4*alpha*d'*c' - 1) = 4*alpha*P*d'^2 + 1
corresponds to the Type II equation via:
  offset = delta = 4*A - P
  b = alpha*d'*b' (NO -- that's not right either)

Actually, look at the existing Lean code pattern. For the D6 subcases:
  offset = (P + 4*alpha*s^2) / M  where M = 4*alpha*s*r - 1
  b and c are specific expressions in terms of s, r, m, alpha.

The connection is: given the ED2 identity
  (4*alpha*d'*b' - 1)(4*alpha*d'*c' - 1) = 4*alpha*P*d'^2 + 1,
set:
  B = 4*alpha*d'*b' - 1
  C = 4*alpha*d'*c' - 1
  Then B*C = 4*alpha*P*d'^2 + 1

  The offset delta = 4*A - P where A = alpha*b'*c'.
  delta = 4*alpha*b'*c' - P.

  Now: B + 1 = 4*alpha*d'*b', C + 1 = 4*alpha*d'*c'.
  (B+1)(C+1) = 16*alpha^2*d'^2*b'*c' = 16*alpha^2*d'^2*(A/alpha) = 16*alpha*d'^2*A

  B*C + B + C + 1 = 16*alpha*d'^2*A
  (4*alpha*P*d'^2 + 1) + B + C + 1 = 16*alpha*d'^2*A
  B + C = 16*alpha*d'^2*A - 4*alpha*P*d'^2 - 2 = 4*alpha*d'^2*(4A - P) - 2 = 4*alpha*d'^2*delta - 2

  And B*C = 4*alpha*P*d'^2 + 1 = 4*alpha*d'^2*P + 1

Hmm, this doesn't simplify to the Type II equation directly. Let me look at
how the existing Lean code connects the D6 identity to the Type II equation.

In subcase 3a: offset = (p+4)/7, b = 2, c = 2*(2p+1)/7.
The Type II equation: (p + offset)(b + c) = 4*offset*b*c.
This is verified by nlinarith from the divisibility facts.

So the existing code does NOT go through the D1 identity at all! It just
directly constructs offset, b, c and verifies the Type II equation by nlinarith.

For the lattice approach, we need to:
1. Find b', c' from the lattice.
2. Construct offset, b, c from b', c'.
3. Verify the Type II equation.

The construction is (from the paper's notation):
  g = gcd(b, c)  [in the original (b,c), not (b',c')]
  b = g*b', c = g*c'
  delta (= offset) = 4*A - P where A = (some expression)

Actually, I think the cleanest bridge is:
Given b', c' ∈ ℕ with b'*c' = M and b'+c' = m*d' where m = 4*A - P and M = A/alpha,
set:
  g = alpha * d'
  b = g * b' = alpha * d' * b'
  c = g * c' = alpha * d' * c'
  offset = 4*A - P = m

Then: (P + offset)(b + c) = (P + m) * alpha*d'*(b'+c')
     = (P + m) * alpha*d' * m*d'
     = (P + m) * alpha * m * d'^2

     4 * offset * b * c = 4 * m * alpha*d'*b' * alpha*d'*c'
     = 4 * m * alpha^2 * d'^2 * b'*c'
     = 4 * m * alpha^2 * d'^2 * M
     = 4 * m * alpha^2 * d'^2 * (A/alpha)
     = 4 * m * alpha * d'^2 * A

We need: (P + m) * alpha * m * d'^2 = 4 * m * alpha * d'^2 * A
Simplify (divide by alpha * m * d'^2): P + m = 4*A
Which is: P + (4*A - P) = 4*A. TRUE! ✓

So the bridge is trivial! Given ANY b', c' with the right properties,
offset = 4*alpha*b'*c' - P, b = alpha*d'*b', c = alpha*d'*c',
and the Type II equation holds because P + offset = 4*A = 4*alpha*b'*c'.

WRITE THIS AS A LEAN 4 THEOREM:

theorem bridge_to_typeII (p alpha b' c' d' : ℕ)
    (hp_pos : 0 < p) (halpha_pos : 0 < alpha)
    (hb'_pos : 0 < b') (hc'_pos : 0 < c') (hd'_pos : 0 < d')
    (hA_gt : 4 * (alpha * b' * c') > p)
    (hsum : b' + c' = (4 * (alpha * b' * c') - p) * d') :
    let offset := 4 * (alpha * b' * c') - p
    let b := alpha * d' * b'
    let c := alpha * d' * c'
    offset % 4 = 3 ∧ b > 0 ∧ c > 0 ∧
    (↑p + ↑offset : ℤ) * (↑b + ↑c) = 4 * ↑offset * ↑b * ↑c := by
  sorry

PROVIDE A COMPLETE PROOF. The Type II equation part should follow from
the identity P + offset = 4*alpha*b'*c' and simple algebra.
The offset ≡ 3 (mod 4) part follows from P ≡ 1 (mod 4).

Wait -- we also need offset ≡ 3 (mod 4). Since offset = 4*alpha*b'*c' - P
and P ≡ 1 (mod 4): offset ≡ 0 - 1 ≡ 3 (mod 4). So we need p % 4 = 1 as a hypothesis.

Revise the theorem to include hp4 : p % 4 = 1.
```

---

## PROMPT 7: COMPONENT — Interval Representative (Lemma 9.23)
**Assign to: any model. Difficulty: Easy. Independence: Full.**

```
[paste SHARED CONTEXT above]

YOUR TASK: Prove in Lean 4 that for any positive integer m, any integer r, and
any interval [x0, x0 + H) with H ≥ m (as natural numbers), there exists an integer
u in the interval with u ≡ r (mod m).

This is Lemma 9.23 from the attached paper. It's the division algorithm.

Version 1 (integers):
theorem interval_has_mod_rep (m : ℕ) (hm : 0 < m) (r x0 : ℤ) (H : ℕ) (hH : m ≤ H) :
    ∃ u : ℤ, x0 ≤ u ∧ u < x0 + ↑H ∧ m ∣ (u - r) := by
  sorry

Version 2 (natural numbers, simpler):
theorem interval_has_mod_rep_nat (m : ℕ) (hm : 0 < m) (r x0 H : ℕ) (hH : m ≤ H) :
    ∃ u : ℕ, x0 ≤ u ∧ u < x0 + H ∧ u % m = r % m := by
  sorry

Proof idea: Let u = x0 + ((r - x0) % m + m) % m (adjusting for signs).
Or: among the m consecutive integers x0, x0+1, ..., x0+m-1, exactly one
is congruent to r mod m. Since H ≥ m, [x0, x0+H) contains these m integers.

Provide COMPLETE proofs for both versions. No sorry.
```

---

## PROMPT 8: COMPONENT — Rectangle Hits Lattice (Proposition 9.25)
**Assign to: strongest model. Difficulty: Hard. Independence: Needs Prompt 7.**

```
[paste SHARED CONTEXT above]

YOUR TASK: Formalize Proposition 9.25 from the attached paper.

STATEMENT: Define L(g, b', c') = {(u,v) ∈ Z² : g | (u*b' + v*c')}.
Let α = gcd(g, b'+c'), d' = g/α. Assume gcd(b',g) = gcd(c',g) = 1.
If H ≥ d' and W ≥ d', then for any x0, y0 there exists (u,v) ∈ L with
x0 ≤ u < x0+H and y0 ≤ v < y0+W.

The paper's proof:
1. Take p0 = (c', -b') ∈ L.
2. Find u* ∈ [x0, x0+H) with u* ≡ c' (mod d') [by Lemma 9.23].
3. Find v* ∈ [y0, y0+W) with v* ≡ -b' (mod d') [by Lemma 9.23].
4. Set m = (u* - c')/d'. Then p0 + m*(d',d') = (c' + m*d', -b' + m*d') = (u*, -b'+m*d').
5. Now -b' + m*d' ≡ -b' (mod d'), and v* ≡ -b' (mod d'). So -b'+m*d' ≡ v* (mod d').
6. Claim: -b'+m*d' ∈ [y0, y0+W) and therefore equals v*.

CRITICAL ISSUE: Step 6 is NOT obvious. Adding m*d' to -b' gives -b' + (u*-c') which
is determined by u*. This might NOT be in [y0, y0+W).

I believe the paper's proof requires using BOTH generators of L, not just the diagonal.
The lattice L has generators (c', -b') and (d', d'). A general lattice point is
a*(c',-b') + k*(d',d') = (a*c'+k*d', -a*b'+k*d') for integers a, k.

With TWO degrees of freedom (a, k), we can independently control:
- First coord: a*c' + k*d' ≡ x (mod anything)
- Second coord: -a*b' + k*d' ≡ y (mod anything)

The proof might work like this:
- We need u ∈ [x0, x0+H) and v ∈ [y0, y0+W).
- u = a*c' + k*d', v = -a*b' + k*d'.
- u - v = a*(c'+b'), u + v = 2*k*d' + a*(c'-b').
- u ≡ a*c' (mod d') and v ≡ -a*b' (mod d').
- Since gcd(c', g) = 1 and d' | g, we have gcd(c', d') = 1.
  So a*c' runs through all residues mod d' as a varies.
  Choose a so that a*c' ≡ x0 (mod d'). This determines a mod d'.
- Then v = -a*b' + k*d'. Since a is determined mod d', v ≡ -a*b' (mod d').
  Choose k so that -a*b' + k*d' ∈ [y0, y0+W).
- For the first coordinate: a*c' + k*d' = a*c' + k*d'.
  With a fixed mod d' and k chosen for v, the first coord is
  a*c' + k*d' ≡ a*c' ≡ x0 (mod d'). So the first coord is also
  congruent to x0 mod d'. Since H ≥ d', [x0, x0+H) contains a representative.
  But we need the ACTUAL value a*c'+k*d' to be in the interval!

Hmm, this still has the coupling problem. Let me think differently.

ALTERNATIVE APPROACH: Use the fact that L has index g in Z^2 (this is Lemma 9.22).
The cosets of L in Z^2 are indexed by residues mod g.
In the rectangle R of area H*W ≥ d'^2 = (g/α)^2, there are H*W integer points.
By pigeonhole on g cosets, if H*W > g then R contains a point of L.
But d'^2 = g^2/α^2 and g = α*d', so d'^2 = g*d'/α. This doesn't directly give H*W > g.

Actually the paper says the lattice has index g and contains (d',d').
The diagonal sublattice {k*(d',d')} has spacing d' in EACH coordinate.
A fundamental domain for this 1D sublattice within R has area H*W/d'
(roughly). We need this to intersect L.

I think the cleanest approach for Lean is:

SIMPLIFIED PROPOSITION: The diagonal coset {p0 + k*(d',d') : k ∈ Z}
is periodic with period d' in BOTH coordinates. Any interval of length ≥ d'
in either coordinate contains a point of this coset. Therefore the rectangle
[x0, x0+H) × [y0, y0+W) contains a point IF we can find k such that
BOTH coordinates are in range simultaneously.

With the diagonal shift, both coordinates move by d' together. So we need
k such that x0 ≤ c'+k*d' < x0+H AND y0 ≤ -b'+k*d' < y0+W simultaneously.

First constraint: (x0-c')/d' ≤ k < (x0+H-c')/d'. Width: H/d' ≥ 1.
Second constraint: (y0+b')/d' ≤ k < (y0+W+b')/d'. Width: W/d' ≥ 1.

Both intervals have width ≥ 1 (since H,W ≥ d'). Do they overlap?
Not necessarily! They might be offset.

THIS is the real issue. With only the diagonal vector, we can't guarantee
overlap of the two k-intervals. We need to also use the OTHER generator (c',-b')
to shift the starting point.

CORRECT PROOF (I think):
1. Use generator (c',-b') to adjust the "phase": replace p0 by p0 + a*(c',-b')
   for some integer a. This gives starting point (c'+a*c', -b'-a*b') = ((1+a)*c', -(1+a)*b').
   Hmm, that just scales p0.

Actually let me use a general point of L. An arbitrary point of L is
a*(c',-b') + k*(d',d'). The set of all first coordinates as a, k vary:
{a*c' + k*d' : a, k ∈ Z}. Since gcd(c', d') | gcd(c', g) = 1, we have
gcd(c', d') = 1. So by Bezout, {a*c' + k*d'} = Z (all integers).
Similarly for second coords: {-a*b' + k*d'} = Z (since gcd(b', d') = 1).

But the PAIRS (a*c'+k*d', -a*b'+k*d') are constrained: both use the SAME (a,k).
The question is whether the set of pairs covers all residue classes mod d'.

The pair (a*c' + k*d', -a*b' + k*d') mod d' = (a*c' mod d', -a*b' mod d').
As a varies over Z/d'Z, first coord covers all residues (since gcd(c',d')=1),
and second coord = -a*b' also covers all residues (since gcd(b',d')=1).
But they're COUPLED: second = -(b'/c') * first (mod d') where b'/c' is the
modular inverse.

So the pairs mod d' form a LINE in (Z/d'Z)^2, not all of (Z/d'Z)^2.
This line has d' elements. The rectangle has ≥ d'^2 integer pairs mod d'.
So by pigeonhole, the rectangle contains a pair on the line.

Wait, that's not right either. The rectangle has H*W points total, which is
≥ d'^2. Mod d', there are d'^2 residue classes. The line has d' classes.
We need the rectangle to hit ONE of those d' classes. Since the rectangle has
≥ d'^2 points and there are d'^2 classes, on average each class gets 1 point.
But we need one specific set of d' classes to be hit. Since the rectangle
has ≥ d'^2 points and we need to hit one of d' classes, by pigeonhole
the rectangle hits ALL d' classes (in fact each at least d' times?). No,
that's only if the points are uniformly distributed mod d'^2.

I think the correct argument is SIMPLER:

For fixed a (mod d'): the first coordinate a*c' + k*d' hits any target
mod d' by choosing a appropriately (since gcd(c', d')=1). Then k ranges
over Z, and we need -a*b' + k*d' to be in [y0, y0+W). Since W ≥ d',
there exists such k. And for that k, a*c' + k*d' has a specific value.
We need a*c' + k*d' ∈ [x0, x0+H).

Let's be precise:
- Choose a ∈ Z so that a*c' ≡ x0 (mod d'). [Possible since gcd(c',d')=1.]
- For this a, define f(k) = a*c' + k*d' (first coord) and g(k) = -a*b'+k*d' (second).
- We need k such that x0 ≤ f(k) < x0+H AND y0 ≤ g(k) < y0+W.
- f(k) ∈ [x0, x0+H) iff k ∈ [(x0-a*c')/d', (x0+H-a*c')/d'). Width H/d' ≥ 1.
- g(k) ∈ [y0, y0+W) iff k ∈ [(y0+a*b')/d', (y0+W+a*b')/d'). Width W/d' ≥ 1.
- Both intervals have width ≥ 1. Do they intersect?
  Two intervals of width ≥ 1 on the real line intersect iff their centers
  are less than (sum of widths)/2 apart. But widths can be exactly 1, and
  the intervals could be non-overlapping (e.g., [0,1) and [1,2)).

So with JUST choosing a to fix the residue, we still can't guarantee overlap.

THE FIX: Don't fix a to one specific value. Instead:
- There are d' valid values of a (mod d') giving a*c' ≡ x0, x0+1, ..., x0+d'-1 (mod d').
  Wait, we want a*c' to be in a specific residue class. There's exactly ONE such a mod d'.
  But we can choose a = a0 + j*d' for any j ∈ Z. Each such choice gives a different
  starting point for the k-intervals.

Hmm, I'm going in circles. Let me just ask the instance to figure it out with the paper.

FORMALIZE THIS. Read the paper's proof of Proposition 9.25 very carefully.
The proof claims to only use the diagonal vector, but I believe it implicitly
uses both generators. Figure out the correct argument and formalize it in Lean 4.

You have two generators: (c', -b') and (d', d').
These are both in L, and they generate L (or a finite-index sublattice of L).
The key properties: gcd(b', g) = gcd(c', g) = 1, d' = g/gcd(g, b'+c').

Provide a COMPLETE proof or clearly identify what intermediate lemma you need.
```

---

## PROMPT 9: RESEARCH — Is There a Simpler Proof for These Specific 6 Classes?
**Assign to: mathematical reasoning model**

```
[paste SHARED CONTEXT above]

YOUR TASK: Mathematical research, NOT Lean code.

The 6 hard residue classes mod 840 are: p ≡ {1, 121, 169, 289, 361, 529} (mod 840).
These correspond to p ≡ 1 (mod 24), p mod 7 ∈ {1,2,4} (QR mod 7),
p mod 5 ∈ {1,4} (QR mod 5).

QUESTION 1: Is there a parametric identity (not of D6 form) that works for
these specific classes? For example:
- An identity involving quadratic residues
- An identity using the structure of p ≡ 1 (mod 24) specifically
- A Pell-equation approach
- A continued-fraction approach

QUESTION 2: The paper proves existence via a 2D lattice argument. But the
ACTUAL Lean goal only needs offset, b, c satisfying an equation. Is there
a NUMBER-THEORETIC shortcut that avoids lattice theory?

For instance: can we prove that for p ≡ 1 (mod 24) and p ≡ 1 (mod 7),
there always exists A ∈ [(p+3)/4, (3p-3)/4] such that A has a divisor pair
(u, v) with u + v = 4A - p?

This is equivalent to: 4A - p divides some factorization of A into
u * (A/u) with u + A/u = 4A - p. Which means u^2 - (4A-p)*u + A = 0
has integer solutions. Discriminant: (4A-p)^2 - 4A must be a perfect square.

For A close to p/4: δ = 4A-p is small, so (4A-p)^2 - 4A ≈ δ^2 - 4A ≈ δ^2 - p.
For δ ≈ √p, this is ≈ 0. So we need A near p/4 + √p/4.

Can you make this precise? Is there always a perfect-square discriminant
for SOME A in the window?

QUESTION 3: Read the paper's Theorem 9.21 and its proof. Does it actually
use the FULL lattice machinery, or is there a simpler argument hidden in it
that we could extract for formalization?

Provide detailed mathematical analysis. If you find a simpler proof path,
describe it precisely enough that it could be formalized in Lean.
```

---

## PROMPT 10: RESEARCH — Verify Proposition 9.25 Proof Correctness
**Assign to: careful mathematical reader**

```
[paste SHARED CONTEXT above]

YOUR TASK: Carefully verify the proof of Proposition 9.25 in §9 of arXiv:2511.07465.

The proposition says: if the rectangle R has sides H ≥ d' and W ≥ d', then
the lattice L = {(u,v) : u*b' + v*c' ≡ 0 (mod g)} intersects R.

The paper's proof:
1. Choose p0 = (c', -b') ∈ L.
2. Find u* ∈ [x0, x0+H) with u* ≡ c' (mod d'). [Lemma 9.23]
3. Find v* ∈ [y0, y0+W) with v* ≡ -b' (mod d'). [Lemma 9.23]
4. Set m := (u* - c')/d'.
5. Point p := p0 + m*(d', d') = (u*, -b' + m*d').
6. First coord u* ∈ [x0, x0+H). ✓
7. Second coord -b' + m*d' ≡ -b' (mod d') ≡ v* (mod d').
8. "By uniqueness of the class representative, v0 + m*d' = v* ∈ [y0, y0+W)."

QUESTION: Is step 8 valid? The uniqueness of Lemma 9.23 says there's exactly
ONE integer in [y0, y0+W) congruent to -b' mod d'. That integer is v*.
But the proof ALSO needs -b' + m*d' to be in [y0, y0+W).

-b' + m*d' = -b' + (u* - c')/d' * d' = -b' + u* - c' = u* - (b' + c').

This is a FIXED value determined by u*. It equals v* only if
u* - (b'+c') ∈ [y0, y0+W) AND u* - (b'+c') ≡ -b' (mod d').

The second condition: u* - (b'+c') ≡ c' - (b'+c') = -b' (mod d'). ✓
The first condition: u* ∈ [x0, x0+H), so u* - (b'+c') ∈ [x0-(b'+c'), x0+H-(b'+c')).
This equals [y0, y0+W) only if y0 = x0 - (b'+c') and W = H.

But y0 and W are ARBITRARY (subject to W ≥ d')! So this doesn't hold in general!

IS THE PROOF WRONG? Or am I missing something? Check the paper very carefully.
Look at Lemma 9.24 (diagonal coset) -- does it provide additional structure?

If the proof IS wrong for the general rectangle, does it still work for the
SPECIFIC rectangles used in the ED2 application (where x0, y0, H, W are
determined by p)?

Provide a detailed analysis. If the proof has a gap, identify EXACTLY what
additional hypothesis is needed to make it work.
```

---

## USAGE GUIDE

1. **Highest priority**: Prompts 1, 5, 6, 7 (self-contained components)
2. **Most likely to break through**: Prompts 9, 10 (research, may find simpler path)
3. **Ambitious but high-reward**: Prompts 2, 3, 8 (if they work, problem solved)
4. **Backup strategy**: Prompt 4 (computational approach)
5. **Long shot**: Prompt 2 approach B (elementary proof without lattices)

Run Prompts 5, 6, 7, 9, 10 first (independent, faster). Then use their
outputs to inform Prompts 1, 2, 3, 8.

For each instance, prepend the SHARED CONTEXT block and attach the paper PDF.
