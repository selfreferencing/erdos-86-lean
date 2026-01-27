# Dyachenko 2025 Paper Notes
## arXiv:2511.07465 - ED2 Method for Erdos-Straus Conjecture

### Purpose
This file records key definitions, lemmas, and propositions from the Dyachenko paper
needed to close the `ed2_qr_classes` sorry in Existence.lean.

### What we need from the paper
1. **Lemma 9.22**: Lattice structure, diagonal period d', index g -- HAVE
2. **Lemma 9.23**: Interval representative (division algorithm) -- HAVE
3. **Proposition 9.25**: Rectangle hits lattice when sides >= d' -- HAVE
4. **Appendix D bridge lemmas**: D.1-D.3, D.33 (lattice point -> Type II solution) -- NEED
5. **The value/bound on d'**: Is it uniformly bounded or does it depend on p? -- SEE ANALYSIS BELOW

---

## Pasted Content from Paper (2026-01-26)

### Lemma 9.22 (Kernel structure and diagonal period)

L is a full-rank lattice of index g, containing:

- v1 = (c', -b')
- v2 = (d', d')

The vector v2 is a diagonal period of length d' = g/alpha.

### Lemma 9.23 (Unique representative of a class)

For any m in N and r in Z, in any half-interval [x0, x0+H) with H >= m
there is exactly one integer u with u = r (mod m).

### Lemma 9.24 (Diagonal coset)

If w = (d', d') in L and p0 in L, then

  p0 + Z*w = {(u, v) in L : u = u0, v = v0 (mod d')}.

### Proposition 9.25 (Hitting the box with a point of L)

Let R = [x0, x0+H) x [y0, y0+W) be an axis-parallel rectangle
(see the definition of the Type I parametric box, 9.6).

If H >= d' and W >= d', where d' = g/alpha from Lemma 9.22, then L intersect R != empty.

**Proof.**
Choose any point p0 = (u0, v0) in L (for example, v1 = (c', -b') from Lemma 9.22).
By Lemma 9.23 there exist unique:

- u* in [x0, x0+H) with u* = u0 (mod d')
- v* in [y0, y0+W) with v* = v0 (mod d')

Set m := (u* - u0)/d' in Z and consider w = (d', d') from Lemma 9.22. Then the point

  p := p0 + m*w = (u0 + m*d', v0 + m*d')

belongs to L. By the choice of m we have the first coordinate u0 + m*d' = u* in [x0, x0+H).

By Lemma 9.24 the second coordinate of p lies in the same class modulo d' as v0,
hence by the uniqueness of the class representative (Lemma 9.23) we get
v0 + m*d' = v* in [y0, y0+W).

Therefore p in L intersect R. QED

### Corollary 9.26 (Role of the parameter alpha)

Increasing alpha decreases the diagonal step d' = g/alpha and thus relaxes the
condition H, W >= d' in Proposition 9.25. Equivalently, the density of the diagonal
layers of L in projection increases by a factor of alpha.

With the standard choice of Type I box sizes (see 9.4.1) the condition H, W >= d'
is satisfied, and there exists an admissible point L intersect R != empty.

### Connection with Section 7.3

Lemma 9.22 and Proposition 9.25 provide a point (b, c) satisfying the linear
constraints of the affine class.

For this point to produce a solution to the ED2 problem, we use the normalization
(u, v) and the inverse test (Lemmas D.33, D.16): for m = 4A - P we take
u = m*d' and find v = u (mod 2) with u^2 - v^2 = 4A/alpha.

Combining Lemma 9.22 and Proposition 9.25, we obtain item (III) of Theorem 9.21:
reducing the lattice step via the parameter alpha gives an unconditional guarantee
of the existence of an admissible triple (delta, b, c) in C_ED2(P) in the given
parametric box.

### Remark 9.27

The conditions obtained in Theorem 9.21 have a natural algebraic interpretation
in terms of the ED2 model. In particular, the parameters m, M, A introduced in
the geometric formulation correspond to the coefficients and constraints in the
system (ED2), where checking the existence of a solution reduces to analyzing
congruences and inequalities. A detailed derivation, as well as extended criteria
allowing refinement of the applicability bounds of the theorem, are given in
Appendix D. There it is also shown how the geometric construction of the window
and strip is consistent with the algebraic description, and additional lemmas are
provided for deeper consideration.

---

## Theorem 9.21 (Main unconditional existence)

For any prime P = 1 (mod 4) there exists a representation
  4/P = 1/A + 1/(bP) + 1/(cP),
where (delta, b, c) in N^3 are obtained from the constructive ED2 method,
based on the parametrization of the set C_ED2(P) satisfying conditions (I)-(III).

### (I) Mathematical conditions:

  b, c, delta in N
  gcd(b, c) = d
  (4b - 1)(4c - 1) = 4*P*delta + 1
  delta | b*c
  A = b*c / delta <= b*P
  B = b*P
  C = c*P
  g_b = gcd(b, g)
  g_c = gcd(c, g)
  b' = b / g_b
  c' = c / g_c
  gcd(b', g) = gcd(c', g) = 1
  alpha = gcd(g, b' + c')
  d' = g / alpha

Here g and d' are consistent with the parametrization of Theorem 7.3:
  delta = alpha * d'^2, where alpha is square-free.

### (II) Algorithmic conditions (Type I parametric box):

  - 1 <= delta, b, c <= (log P)^A0, with fixed A0 > 0.
  - b <= c.
  - (delta, b, c) = u0(P) (mod Lambda_1), where Lambda_1 subset Z^3
    is a lattice of index M1.
  - gcd(b', c') = 1.
  - For the Type I box in ED2 there are no additional restrictions on
    parity or coprimality with P.

### (III) Unconditional guarantee of finding a solution.

Consider the two-dimensional lattice
  L = {(u,v) in Z^2 : u*b' + v*c' = 0 (mod g)},
where g in N, b', c' satisfy gcd(b', g) = gcd(c', g) = 1,
and set alpha := gcd(g, b' + c'), d' := g/alpha.

---

## Section 9.4 - Parametric boxes

### Definition 9.6 (Type I box)

For fixed A > 0 and prime P:
  B_P^(I) = {u in Z^3 : 1 <= u_i <= (log P)^A,
              u = u0(P) (mod Lambda_1)},
where Lambda_1 subset Z^3 is a sublattice of index M1 defining the modular constraints.

### Definition 9.7 (Type II box)

Let k >= 2, A > 0, T > 1, and Lambda_2 subset Z^k be a sublattice of fixed index.
A Type II box is defined as
  B_P^(II)(T) = {u in Z^k : u = u0(P) (mod Lambda_2),
                  rho_W(u) <= (log P)^A,
                  |F(u)| <= Delta(T)},
where W is a weight matrix for the norm rho_W(u) = <Wu, u>,
F: Z^k -> Z is a fixed (usually quadratic) form,
Delta(T) is the window thickness.

### Remark 9.8
A Type II box is used to localize parameters near nonlinear dependencies
(quadratic, bilinear, etc.), complementing the Type I box, which covers linear classes.

### Example 9.9 (Thickening of a quadratic surface)
For k = 3, u = (delta, b, c) and
  F(delta, b, c) = (4b - 1)(4c - 1) - 4*P*delta - 1,
we obtain
  B_II^ED2(T) = {(d, b, c) = u0(P) (mod Lambda_2),
                  rho_W(d, b, c) <= (log P)^A,
                  |F(d, b, c)| <= Delta(T)}.

### Remark 9.13 (Status)
**IMPORTANT**: Type II boxes and radial windows are not used in the proofs of
Sections 9.1-9.10 and serve as groundwork for numerical experiments and future estimates.

---

## ANALYSIS OF d' BOUND

From Theorem 9.21 condition (I):
  delta = alpha * d'^2, where alpha is square-free
  g = alpha * d'
  d' = g / alpha

The Type I box constrains: 1 <= delta <= (log P)^A0
Since delta = alpha * d'^2, we get: d'^2 <= delta <= (log P)^A0
Therefore: d' <= (log P)^(A0/2)

This means d' GROWS with P (logarithmically), but slowly.

The box sizes H, W are also ~ (log P)^A0 (from the Type I box definition).
Since d' <= (log P)^(A0/2) and the box has side (log P)^A0,
we need (log P)^A0 >= (log P)^(A0/2), which holds for P >= e (trivially).

So the condition H, W >= d' in Proposition 9.25 IS automatically satisfied
for the Type I box. This confirms Corollary 9.26.

KEY IMPLICATION: There is NO finite bound B needed for computational certificates.
The lattice argument works for ALL primes, unconditionally.

However: formalizing this in Lean requires:
1. The lattice construction (L, its index, diagonal period)
2. Proposition 9.25 (rectangle hitting)
3. The bridge from lattice point to ED2 solution (Appendix D)
4. Showing the Type I box satisfies H, W >= d'

---

## APPENDIX D - Complete Content (Pasted 2026-01-26)

### D.1 Algebraic core of ED2

**Theorem D.1 (Equivalence of "product" and "sum/product").**
Let A = alpha * b' * c' for some b', c' in N and m := 4A - P > 0. Then equivalent:

1. There exists d' in N such that
   (4*alpha*d'*b' - 1)(4*alpha*d'*c' - 1) = 4*alpha*P*d'^2 + 1

2. b'*c' = M = A/alpha and b'+c' ≡ 0 (mod m)

3. And automatically d' = (b'+c')/m in N.

**Proof:** Expand LHS, equate to RHS, subtract 1, divide by 4*alpha:
  4*alpha*d'^2*(b'c') - d'(b'+c') = P*d'^2
  Since 4*alpha*(b'c') = 4A: d'(b'+c') = (4A-P)*d'^2 = m*d'^2
  So b'+c' = m*d'. QED

### D.2 Quadratic reparameterization

**Theorem D.2.** Let S := (4A-P)*d' = m*d' and M := A/alpha. Conditions of D.1
are equivalent to b', c' being integer roots of x^2 - S*x + M = 0,
i.e., b'+c' = S and b'*c' = M. Discriminant Delta := S^2 - 4M is a perfect square.

### D.3 Bounds via discriminant

**Lemma D.3.** The identity holds iff:
- alpha in N and alpha | A (i.e., M in N)
- d' in N
- Delta = S^2 - 4M is a perfect square
Then b', c' = (S ± sqrt(Delta))/2 in N.
Necessary bound: (4A-P)*d' >= 2*sqrt(A/alpha), i.e., d' >= 2*sqrt(A/alpha)/(4A-P).

### D.4 On parity (Remark D.4)

Since P is odd, m = 4A-P is odd, so S has same parity as d'.
Both (S ± sqrt(Delta))/2 are integers; no additional parity restrictions on d' needed.

### D.5 Unconditional generation of candidates (Theorem D.5)

For A in [(P-1)/4 + 1, (3P+1)/4 - 1], decompose A = alpha*b'*c'.
Define L_{alpha,d'}(b',c') := (4*alpha*d'*b' - 1)(4*alpha*d'*c' - 1)
and R_{alpha,d'} := 4*alpha*P*d'^2 + 1.
If L = R for some (alpha, d', b', c'), the identity holds.

### D.6 Left parameterization (Lemma D.6 - KEY, already in Lean)

Let r, s >= 1 and M := 4*alpha*s*r - 1.
If M | (4*alpha*s^2 + P), then with:
  d' = r, b' = s, c' = m*r - s, where m = (4*alpha*s^2 + P)/M,
  A = alpha*s*(m*r - s)
the identity (4*alpha*d'*b' - 1)(4*alpha*d'*c' - 1) = 4*alpha*P*d'^2 + 1 holds.

### D.7 Affine form and slope (Lemma D.7)

A(P) = lambda_{r,s} * P + mu_{r,s}, where:
  lambda_{r,s} = alpha*s*r / (4*alpha*s*r - 1)
  1/4 < lambda_{r,s} <= 1/3 for all alpha, r, s >= 1.

### D.8 Width of target interval (Lemma D.8)

Length of [L(P), U(P)] = P/2 - 3/2.
L(P) = P/4 + 3/4, U(P) = 3P/4 - 3/4.

### D.9 Diagonal period as multiple of sum (Lemma D.9)

Same as D.1 restated: b'+c' is a multiple of m. The minimal
"diagonal period" equals m/gcd(m, 2).

### D.10 Geometry in (u,v) coordinates

Switch to u = b'+c', v = c'-b'. Then M = b'c' = (u^2-v^2)/4.
Parity cosets: L_00 = {u ≡ v ≡ 0 (mod 2)}, L_11 = {u ≡ v ≡ 1 (mod 2)}.

### D.11 Bezout lemma with parity (Lemma D.11/D.6-variant)

Bezout representation u(4b-1) + vP = 1 with u ≡ 3 (mod 4)
and v ≡ 0 (mod 4*alpha*d'^2) exists when gcd conditions hold.

### D.12 Conditional residue covering scheme

**Definition D.12 (Fixed covering set).** F = {(r_i, s_i)}_{i=1}^K,
M_i := 4*alpha*s_i*r_i - 1, Q := lcm(M_1, ..., M_K).
F satisfies covering condition if for each p in {0,...,Q-1} there exists i with
p ≡ -4*alpha*s_i^2 (mod M_i) and A_{r_i,s_i}(p) in [L(p), U(p)].

**Theorem D.14 (Existence under covering).** If covering condition holds,
then for any odd prime P, there exists i such that M_i | (4*alpha*s_i^2 + P)
and A_{r_i,s_i}(P) in [L(P), U(P)].

**Proof:** Take p ≡ P (mod Q). Covering gives i. Since M_i | Q and P ≡ p (mod Q),
we get M_i | (4*alpha*s_i^2 + P). The A-window inclusion follows from
lambda_{r_i,s_i} in (1/4, 1/3] and the monotonicity argument. QED

**Corollary D.15 (Constructiveness).** The found i gives explicit integers
m, d', b', c', A satisfying the identity.

### D.16 Necessary and sufficient conditions for (u,v) point (KEY BRIDGE)

**Lemma D.16.** Fix alpha, P, A with m := 4A-P > 0, M := A/alpha.
For integer point (u,v), the following are EQUIVALENT:

1. There exist d', b', c' in N such that u = m*d', v = b'-c',
   b' = (u+v)/2, c' = (u-v)/2, and the identity holds.

2. m | u, u ≡ v (mod 2), u^2 - v^2 = 4M.

3. There exists d' in N with u = m*d' and Delta := u^2 - 4M = v^2
   is a perfect square.

### D.21-D.31 Extended constructions

**Definition D.21 (Candidate set F(P)).** For fixed alpha and odd prime P:
F(P) := {(r,s) in Z_>=1^2 | A_{r,s}(P) in [L(P), U(P)] and
P ≡ -4*alpha*s^2 (mod 4*alpha*s*r - 1)}.

**Lemma D.24 (Divisor-oriented constructor).** If d | (4*alpha*s^2 + P)
and d ≡ -1 (mod 4*alpha*s), set r = (d+1)/(4*alpha*s), then the identity holds.

**Corollary D.26 (Single-class criterion for s=1).** If d | (4*alpha + P)
and d ≡ -1 (mod 4*alpha), then r = (d+1)/(4*alpha) gives a solution.

### D.32-D.34 Normalization and perfect square (CRITICAL)

**Definition D.32 (Normalization).** u := b'+c', v := b'-c'.
Then u ≡ v (mod 2) and M = b'c' = (u^2-v^2)/4, A = alpha*M.

**Lemma D.33 (Sum and discriminant - KEY).** Let S = b'+c', M = b'c',
Delta = S^2 - 4M. Under normalization:
  S = u, Delta = v^2.
**In particular, Delta is ALWAYS a perfect square.**

This is the critical insight: the discriminant condition (D.2) is automatically
satisfied for any lattice point satisfying the linear congruence.

**Lemma D.34 (Parity cosets).** Admissible (u,v) lie in
Lambda_00 = (2Z) x (2Z) or Lambda_11 = (2Z+1) x (2Z+1).

### D.35-D.41 Covering geometry

**Proposition D.35 (Anchors).** For K = A/alpha, anchor points (u,v) with
u^2-v^2 = 4K exist in Lambda_00 (K odd) or Lambda_11 (K even).

**Proposition D.40 (Lattice covering modulo).** If for every class x in Z/QZ
there exist i and r in R_i with x ≡ r (mod M_i), then for sufficiently large P,
[L(P), U(P)] ∩ Z ⊆ F(P).

**Theorem D.41 (Existence under covering).** If conditions of D.40 hold,
then for all sufficiently large P, there exists A in [L(P), U(P)] ∩ Z
satisfying the congruences.

---

## STRUCTURAL ANALYSIS: Why D6 Cannot Cover the 6 Hard Classes

The D6 construction always produces M = 4*alpha*s*r - 1 ≡ 3 (mod 4).
For such M (when prime), -1 is a QNR, so -QR = QNR.
The D6 residue condition P ≡ -4*alpha*s^2 (mod M) requires P to be
in a QNR class (since 4*alpha*s^2 is a QR, and -QR = QNR for M ≡ 3 mod 4).

Therefore D6 STRUCTURALLY cannot reach QR classes:
- mod 7: QR = {1,2,4}, QNR = {3,5,6}. D6 covers {3,5,6} only.
- mod 5: QR = {1,4}, QNR = {2,3}. D6 covers {2,3} only.
- mod 11: QR = {1,3,4,5,9}, QNR = {2,6,7,8,10}. D6 covers QNR only.

The 6 hard classes (p mod 7 in {1,2,4} AND p mod 5 in {1,4}) are the
intersection of QR classes, unreachable by ANY D6 extension.

This is NOT a limitation of our specific (r,s) choices - it is structural.
No D6-based covering can ever reach these classes, regardless of how
many (r,s) pairs we add.

---

## FORMALIZATION PATH ANALYSIS

### What the paper actually proves (Theorem 9.21 + Appendix D)

The paper proves existence for ALL primes P ≡ 1 (mod 4), unconditionally.
The proof uses:
1. A-window existence (DONE in Lean - A_window_nonempty)
2. Lattice L construction (Lemma 9.22)
3. Lattice hitting proposition (Prop 9.25) - box sides >= d' guarantees intersection
4. Bridge: lattice point -> ED2 solution (D.1 + D.16 + D.33)
5. Box size vs d' comparison: d' <= (log P)^(A0/2), box sides ~ (log P)^A0

### Key insight from D.33

The discriminant Delta = v^2 is ALWAYS a perfect square under normalization.
This means: once Proposition 9.25 gives us a lattice point (b',c') in the box,
the algebraic conditions for an ED2 solution are AUTOMATICALLY satisfied.
No discriminant checking needed. The bridge is purely algebraic.

### Three possible formalization strategies

**Strategy 1: Full lattice formalization (~800-1200 LOC)**
- Formalize Lemma 9.22 (lattice structure)
- Formalize Lemma 9.23 (interval representative - division algorithm)
- Formalize Proposition 9.25 (rectangle hits lattice)
- Formalize D.1 (algebraic equivalence)
- Formalize D.33 (discriminant automatic)
- Prove box sides >= d' from Type I box definition
- Pro: Complete, rigorous, follows the paper exactly
- Con: Very substantial Lean effort, needs lattice theory

**Strategy 2: Computational + analytic hybrid**
- For p <= B: verify by decision procedure (need decidable bounded search)
- For p > B: use paper's analytic argument
- Pro: Smaller Lean effort for the analytic part
- Con: Still need B to be provably sufficient, native_decide may be slow

**Strategy 3: Extended covering with non-D6 methods**
- Find additional parametric families beyond D6 that cover QR classes
- The divisor-pair method covers individual primes but not as congruence classes
- The (u,v) geometry (D.10, D.16) gives different access patterns
- Pro: Stays within the parametric identity framework
- Con: May not be achievable - the QR obstruction may be fundamental

### Recommended path: Strategy 1 (full lattice)

The paper gives a complete, self-contained proof. The core components are:
1. Lemma 9.23 is trivial (division algorithm / modular arithmetic)
2. Proposition 9.25 is elementary (two applications of 9.23 + lattice coset)
3. D.1 is pure algebra (already essentially done in the D6 subcases)
4. D.33 is trivial (definitional - v^2 is always a perfect square)
5. The d' bound is a simple inequality from delta = alpha*d'^2

The HARD part is formalizing the lattice L itself and showing it has the
claimed structure (index g, diagonal period d' = g/alpha). This requires
Lemma 9.22, which involves submodule theory in Z^2.
