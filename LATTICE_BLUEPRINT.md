# Mathematical Blueprint: Closing the Sorry in ed2_qr_classes

## 0. Executive Summary

**Goal**: Prove in Lean 4 that for every prime p with p%24=1, p%7 in {1,2,4},
p%5 in {1,4}, p%11 not in {7,8,10}, p%19 not in {14,15,18},
p%23 not in {7,10,11,15,17,19,20,21,22}, there exist natural numbers
offset, b, c satisfying:

```
offset % 4 = 3  /\  b > 0  /\  c > 0  /\
(p + offset : Z) * (b + c) = 4 * offset * b * c
```

**Coverage analysis** (computed 2026-01-26):
- D6 with M <= 5000 covers 10293/10752 sorry-region residue classes mod 4037880
- 459 classes remain uncovered at the CLASS level
- Every individual prime tested (up to 50M) IS solvable by D6 with larger M
- Finite D6 coverage CANNOT close the gap (QNR obstruction: D6 residues are
  always QNR mod M, plateaus at 459 uncovered classes)

**Recommended strategy**: Two-phase proof.
- Phase 1 (computational): Verify all primes up to bound B by decision procedure
- Phase 2 (analytic): Prove existence for p > B via bridge lemma + density argument

---

## 1. The Bridge Lemma (ED2 Parameters -> Type II)

This is the algebraic core. Pure computation, no number theory.

### Statement

```
theorem bridge_lemma (p alpha b' c' d' : N)
    (hp4 : p % 4 = 1) (hp_pos : p >= 5)
    (hb'_pos : b' > 0) (hc'_pos : c' > 0) (hd'_pos : d' > 0) (halpha_pos : alpha > 0)
    (hsum : b' + c' = d' * (4 * alpha * b' * c' - p))
    (hgt : 4 * alpha * b' * c' > p) :
    let offset := 4 * alpha * b' * c' - p
    let b := alpha * d' * b'
    let c := alpha * d' * c'
    offset % 4 = 3 /\ b > 0 /\ c > 0 /\
    (p + offset : Z) * (b + c) = 4 * offset * b * c
```

### Proof sketch

1. **offset % 4 = 3**: offset = 4*alpha*b'*c' - p. Since p % 4 = 1,
   offset % 4 = (0 - 1) % 4 = 3. In Lean: `omega` after establishing offset mod 4.

2. **b > 0, c > 0**: Immediate from positivity of alpha, d', b', c'.

3. **Type II identity**: Setting A = alpha*b'*c', we have offset = 4A - p.
   LHS = (p + 4A - p)(alpha*d'*b' + alpha*d'*c')
       = 4A * alpha*d'*(b' + c')

   RHS = 4*(4A - p)*alpha*d'*b'*alpha*d'*c'
       = 4*(4A-p)*alpha^2*d'^2*b'*c'

   Using hsum: b'+c' = d'*(4A-p), so LHS = 4A*alpha*d'*d'*(4A-p)
                                           = 4*alpha*b'*c'*alpha*d'^2*(4A-p)
                                           = 4*alpha^2*d'^2*b'*c'*(4A-p) = RHS. QED.

   In Lean: `push_cast` then `nlinarith` with cast versions of hsum.

### Lean implementation notes
- Work in Z for the identity (cast N -> Z).
- The subtraction 4*alpha*b'*c' - p needs care in N (hgt ensures no underflow).
- ~25 lines of Lean. Follows exactly the pattern of existing D6 subcases but abstracted.

---

## 2. The Existence Theorem (Core Number Theory)

This is the hard part. We need:

### Statement

```
theorem ed2_params_exist (p : N) (hp : Nat.Prime p) (hp4 : p % 4 = 1) (hp_ge : p >= 5) :
    exists alpha b' c' d' : N,
      alpha > 0 /\ b' > 0 /\ c' > 0 /\ d' > 0 /\
      Nat.Coprime b' c' /\
      b' + c' = d' * (4 * alpha * b' * c' - p) /\
      4 * alpha * b' * c' > p
```

### Approach A: Hybrid Computational + Analytic

**Phase 1 (p <= B):** Direct computation.
For each prime p <= B in the sorry region, produce an explicit witness
(alpha, b', c', d'). This can be done by:
- A `Decidable` instance with `native_decide`, or
- A hardcoded witness table verified by `decide`/`omega`

The witness table approach is more practical. For each p, store (alpha, b', c', d')
and verify the three conditions by `omega`.

**Phase 2 (p > B):** Analytic existence.
For p > B, prove that the D6 construction with some M value works. This uses
the density of suitable M values.

**Key insight**: For the D6 construction with parameters (alpha, r, s):
- M = 4*alpha*s*r - 1
- Residue covered: p % M = (-4*alpha*s^2) % M
- b' = s, c' = r (or reversed), d' = (p + 4*alpha*s^2)/M
- The sum condition is automatically satisfied

So existence of D6 parameters is equivalent to: there exist alpha, r, s >= 1
with M = 4*alpha*s*r - 1 and M | (p + 4*alpha*s^2).

Setting alpha = 1, s = 1: M = 4r - 1 and we need (4r-1) | (p + 4).
So we need a divisor of (p + 4) that is 3 mod 4.

### Critical Sub-Lemma: Divisor Congruence

```
lemma has_divisor_3_mod_4 (n : N) (hn : n > 1) (hn_odd : n % 2 = 1) (hn_mod : n % 4 = 1) :
    exists d : N, d > 1 /\ d | n /\ d % 4 = 3
```

**Why this suffices for alpha=1, s=1**: If p % 4 = 1, then p + 4 is odd (p is odd, +4
stays odd parity? No: p odd + 4 = odd. p+4 is odd). And p+4 % 4 = (1+0)%4 = 1.
Wait: p%4=1, so p+4 % 4 = 1+0 = 1. So p+4 = 1 mod 4.

**Problem**: Not every n = 1 mod 4 has a divisor = 3 mod 4!
Counter: n = 5 (prime, 5 % 4 = 1). Divisors: {1, 5}. Neither is 3 mod 4.
Counter: n = 25. Divisors: {1, 5, 25}. None is 3 mod 4.

This lemma is FALSE. Numbers that are products of primes = 1 mod 4 have
NO divisor = 3 mod 4. Example: 5, 13, 17, 25, 29, 37, 41, ...

So the simple D6 with alpha=1, s=1 does NOT work for all p.
This is exactly the QR obstruction.

### Why D6 alone cannot close the sorry

For D6 with parameters (alpha, r, s) and M = 4*alpha*s*r - 1:
The residue -4*alpha*s^2 is ALWAYS a quadratic non-residue mod M.
(Proof: (-4*alpha*s^2 / M) = (-1/M) * (alpha/M) * (4s^2/M) = -1 * 1 * 1 = -1,
using: M = 3 mod 4 => (-1/M) = -1, and alpha is always QR mod M = 4*alpha*s*r - 1
by quadratic reciprocity.)

Consequence: D6 can only cover primes p that are QNR mod M.
The sorry region has p that is QR mod 5 and QR mod 7.
For M coprime to 35, being QNR mod M is independent of QR status mod 5 and 7.
So D6 CAN cover sorry-region primes (using M coprime to 35 where p happens to be QNR).

But: at the RESIDUE CLASS level mod Q = lcm(24,5,7,11,19,23) = 4037880,
D6 with finitely many M values leaves 459 classes permanently uncovered.
This is because for these classes, p's residue mod EVERY M <= 5000 falls in the QR set.

Individual primes in these classes DO get covered by D6 with specific large M values
(because a specific prime p is QNR mod infinitely many primes M).
But no finite set of M values covers the entire class.

### Approach B: Divisor-Pair (DP) Construction

Alternative to D6. Given p, find offset = u + v with:
- offset % 4 = 3
- u | A and v | A where A = (p + offset) / 4
- Then b = A/u, c = A/v satisfies the Type II equation

DP works whenever A = (p + offset)/4 has a factorization A = b*c with b+c = offset.
This requires finding offset such that A is "sufficiently composite."

**DP is also insufficient for a CLASS-level proof** for the same reason: no finite
set of DP congruences covers all sorry-region classes.

### Approach C: The Actual Dyachenko Argument (What We Need)

The Dyachenko paper (Theorem 9.21) proves existence using a DENSITY argument:

**Setup**: Fix p prime, p = 1 mod 4. Consider all pairs (b', c') with:
- 1 <= b', c' <= N (for N = (log p)^A0, some fixed A0)
- gcd(b', c') = 1
- The "sum condition" determines d' = (b'+c')/(4*alpha*b'*c' - p) (need divisibility)

**Key counting argument**:
1. The number of pairs (b', c') in [1,N]^2 with gcd(b',c')=1 is ~ (6/pi^2) * N^2.
2. For each (b', c'), the sum condition b'+c' = 0 mod (4*alpha*b'*c' - p)
   holds for a positive density of (b', c') pairs.
3. The coprimality conditions gcd(b', alpha*d') = gcd(c', alpha*d') = 1 are
   satisfied with positive density.
4. For large enough N (i.e., large enough p), the product of densities exceeds 1/N^2,
   guaranteeing at least one valid pair exists.

**Why this is hard to formalize**:
- Requires counting lattice points in regions (Gauss circle-type bounds)
- Requires Euler product formula for coprimality density
- Requires explicit constants to determine the threshold B

---

## 3. Recommended Implementation Plan

### Option 1: Computational Proof (Simplest, Works for Specific Bound)

Replace the sorry with a decision procedure for ALL primes up to 10^7 (or higher).

```lean
-- For each sorry-region prime p <= B, provide explicit (offset, b, c)
-- verified by omega/norm_num
theorem ed2_qr_classes_computational (p : N) (hp : Nat.Prime p)
    (hp24 : p % 24 = 1) ... (hp_le : p <= 10000000) :
    exists offset b c : N, offset % 4 = 3 /\ b > 0 /\ c > 0 /\
    (p + offset : Z) * (b + c) = 4 * offset * b * c
```

**Implementation**:
- Precompute witnesses for all ~14000 hard primes up to 10M
- Store as a lookup table in Lean
- Verify each witness by `omega` or `norm_num`
- Size: ~14000 * 5 lines = 70000 lines (large but feasible with code generation)

**Limitation**: Only proves the conjecture up to 10M, not for all primes.

### Option 2: Hybrid (Computational + Analytic Tail) [RECOMMENDED]

```lean
theorem ed2_qr_classes (p : N) (hp : Nat.Prime p) ... :
    exists offset b c : N, ... := by
  by_cases hp_le : p <= B
  -- Case 1: small primes, computational
  · exact ed2_qr_classes_small p hp ... hp_le
  -- Case 2: large primes, analytic
  · exact ed2_qr_classes_large p hp ... (not hp_le)
```

For Case 2, use the bridge lemma + existence of D6 parameters for large p.

**Key Lemma for Large Primes**:

```
theorem d6_exists_for_large_prime (p : N) (hp : Nat.Prime p) (hp_large : p > B) :
    exists M alpha r s : N, M = 4*alpha*s*r - 1 /\ M | (p + 4*alpha*s^2) /\ ...
```

Proof idea: For p > B, p + 4 has a prime factor q >= 3 with q = 3 mod 4.
WAIT: this is the false lemma from above. p + 4 need not have such a factor.

Alternative: Use MULTIPLE values of (alpha, s):
- alpha=1, s=1: need (p+4) to have a factor = 3 mod 4
- alpha=1, s=2: need (p+16) to have a factor = 3 mod 4
- alpha=1, s=3: need (p+36) to have a factor = 3 mod 4
- alpha=2, s=1: need (p+8) to have a factor = 7 mod 8
- etc.

For p > B (large), at least one of p+4, p+16, p+36, p+64, ... must have a
prime factor = 3 mod 4. This follows from:

**Lemma (Key number theory)**: For any integer n, at least one of
n, n+12, n+24, n+36, ... (finitely many terms) has a prime factor = 3 mod 4.

Actually, this is related to values of quadratic forms. The integers
without any prime factor = 3 mod 4 are exactly those of the form
a^2 + b^2 (sums of two squares, by Fermat/Euler). The density of such
integers up to N is ~ C / sqrt(log N) (Landau-Ramanujan theorem).

So for large N, the probability that a random integer near N is a sum of
two squares is ~ C/sqrt(log N) -> 0. In particular, among any O(sqrt(log p))
consecutive values of 4s^2, at least one gives p + 4s^2 with a factor = 3 mod 4.

**Formalization difficulty**: The Landau-Ramanujan theorem is deep. It requires
the analytic properties of L-functions. This is far beyond current Mathlib.

---

## 4. Pragmatic Path Forward

Given the formalization difficulties of the analytic approach, here are the
practical options ranked by feasibility:

### Path A: Computational Certificate (Most Feasible)

1. Precompute witnesses for ALL sorry-region primes up to B = 10^7
2. Store as a Lean structure: array of (p, offset, b, c) tuples
3. Each verified by `omega` at compile time
4. Leave a sorry ONLY for the statement "for p > 10^7" with clear documentation
5. The sorry statement is much more specific: existence for very large primes only

**Lean code structure**:
```lean
-- Generated witness table (or use native_decide over Finset)
theorem ed2_qr_small (p : N) (hp : Nat.Prime p) ... (hp_le : p <= 10000000) :
    exists offset b c, ... := by
  -- omega over witness table, or interval_cases + omega
  sorry -- TO BE REPLACED by generated code

theorem ed2_qr_large (p : N) (hp : Nat.Prime p) ... (hp_gt : p > 10000000) :
    exists offset b c, ... := by
  sorry -- Analytic: every large prime has D6 parameters

theorem ed2_qr_classes (p : N) (hp : Nat.Prime p) ... :=
  if h : p <= 10000000
  then ed2_qr_small p hp ... h
  else ed2_qr_large p hp ... (by omega)
```

### Path B: Extended D6 Cover + Documented Sorry (Next Most Feasible)

1. Add D6 subcases for M values up to 200 (covers 95.7% of classes at class level)
2. The sorry becomes: "459 specific residue classes mod 4037880"
3. Document that these require the Dyachenko lattice density argument
4. This is a SHARPER sorry than the current one

### Path C: Full Lattice Formalization (Hardest)

1. Formalize the bridge lemma (easy, ~25 lines)
2. Formalize interval representative lemma (easy, ~15 lines)
3. Formalize two-generator CRT lemma (medium, ~50 lines)
4. Formalize Landau-Ramanujan type bound (VERY HARD, not in Mathlib)
5. Connect everything to close the sorry

Step 4 is the blocker. Without a formalized density bound for sums-of-two-squares,
the full closure is not feasible with current Mathlib.

---

## 5. Detailed Lemma Specifications for Aristotle

### Lemma 1: Bridge (ED2 -> Type II)

**File**: New file or append to Existence.lean
**Dependencies**: Int arithmetic, push_cast, nlinarith
**Difficulty**: Easy (algebraic identity)

```lean
-- Given ED2 parameters, produce Type II solution
theorem bridge_ed2_to_type2
    (p α b' c' d' : N)
    (hp_mod4 : p % 4 = 1)
    (hα : α > 0) (hb' : b' > 0) (hc' : c' > 0) (hd' : d' > 0)
    (hgt : 4 * α * b' * c' > p)
    (hsum : b' + c' = d' * (4 * α * b' * c' - p)) :
    let offset := 4 * α * b' * c' - p
    let b := α * d' * b'
    let c := α * d' * c'
    offset % 4 = 3 ∧ b > 0 ∧ c > 0 ∧
    (↑p + ↑offset : ℤ) * (↑b + ↑c) = 4 * ↑offset * ↑b * ↑c := by
  constructor
  · -- offset % 4 = 3
    -- offset = 4αb'c' - p, and p % 4 = 1
    omega
  constructor
  · -- b > 0
    exact Nat.mul_pos (Nat.mul_pos hα hd') hb'
  constructor
  · -- c > 0
    exact Nat.mul_pos (Nat.mul_pos hα hd') hc'
  · -- Type II identity
    -- Key: p + offset = 4αb'c', b + c = αd'(b' + c')
    -- LHS = 4αb'c' * αd'(b'+c') = 4α²d'b'c'(b'+c')
    -- RHS = 4(4αb'c' - p) * α²d'²b'c'
    --     = 4α²d'²b'c'(4αb'c' - p)
    -- Using hsum: b'+c' = d'(4αb'c'-p), so d'(b'+c') = d'²(4αb'c'-p)
    -- Then LHS = 4α²b'c' * d'²(4αb'c'-p) = RHS. QED
    push_cast
    nlinarith [hsum]  -- may need explicit cast lemmas
```

**Note**: The `omega` for offset%4=3 may need help. Since p%4=1 and
4αb'c' % 4 = 0, offset = 4αb'c' - p has offset%4 = (0-1)%4 = 3.
But in Nat, subtraction is tricky. May need:
`have : offset = 4*α*b'*c' - p := rfl; omega` with hgt ensuring no underflow.

### Lemma 2: Computational Witness Verification

**For each prime p in the sorry region up to B**:
Given concrete (offset, b, c), verify all four conditions by `omega` / `norm_num`.

**Pattern** (follows existing D6 subcases exactly):
```lean
-- Example for p = 4037881 (smallest prime in uncovered classes)
-- Witness: offset=2051, b=494, c=155382
refine ⟨2051, 494, 155382, ?_, by norm_num, ?_, ?_⟩
· omega  -- 2051 % 4 = 3
· norm_num  -- 155382 > 0
· push_cast; ring  -- or nlinarith
```

### Lemma 3: D6 Parameter Existence (alpha=1, s=1 special case)

```lean
-- If (p + 4) has a divisor d with d > 1 and d % 4 = 3,
-- then D6 with M = d works (alpha=1, r=(d+1)/4, s=1)
theorem d6_from_divisor_3mod4 (p d : N) (hp : Nat.Prime p) (hp4 : p % 4 = 1)
    (hd_pos : d > 1) (hd_dvd : d ∣ (p + 4)) (hd_mod : d % 4 = 3) :
    ∃ offset b c : N, offset % 4 = 3 ∧ b > 0 ∧ c > 0 ∧
    (↑p + ↑offset : ℤ) * (↑b + ↑c) = 4 * ↑offset * ↑b * ↑c
```

This handles the easy cases but NOT all primes (fails when p+4 is a product
of primes all = 1 mod 4).

---

## 6. Quantitative Analysis

### Sorry-region statistics (computed)

| Metric | Value |
|--------|-------|
| Q = lcm(24,5,7,11,19,23) | 4,037,880 |
| Sorry-region classes mod Q | 10,752 |
| D6-covered (M <= 5000) | 10,293 (95.7%) |
| Uncovered classes | 459 (4.3%) |
| Hard primes up to 10M | 14,351 |
| D6 failures (M <= 200) | 9 primes |
| D6 failures (M <= 2000) | 1 prime (p=2031121) |
| D6 failures (M <= 2500) | 0 primes up to 10M |

### Smallest primes in uncovered classes

All have p > Q = 4,037,880:
- p = 4,037,881 (offset=2051, b=494, c=155382)
- p = 4,038,169 (offset=2087, b=484, c=11110704)
- p = 4,038,721 (offset=2111, b=480, c=157845)

All solvable by DP with large offset.

### The QNR obstruction (proof)

For D6 with M = 4αsr - 1:
The Legendre symbol (-4αs^2 / M) = (-1/M)(α/M)(4s^2/M).
- M = 3 mod 4, so (-1/M) = -1
- (4s^2/M) = 1 (perfect square times unit)
- (α/M) = 1 (by quadratic reciprocity: M = -1 mod α, so (M/α) = (-1/α),
  and the reciprocity law gives (α/M)(M/α) = (-1)^((α-1)(M-1)/4).
  Since M = 3 mod 4, (M-1)/2 is odd. For odd α:
  (-1)^((α-1)(M-1)/4) = (-1)^((α-1)/2) = (-1/α) = (M/α).
  So (α/M) = 1.)
Therefore (-4αs^2/M) = -1: always QNR.

This means: among all primes M = 3 mod 4, D6 picks out a QNR class.
For a specific sorry-region class r mod Q, r may be QR mod every
"reachable" M, making it permanently uncovered by D6.

---

## 7. Open Questions

1. **Explicit bound B**: What is the smallest B such that ALL sorry-region
   primes p > B are covered by D6 with M <= M_max(B)? The Dyachenko paper
   doesn't give explicit constants. Determining B requires making the
   Landau-Ramanujan density argument quantitative.

2. **Feasibility of computational approach**: Can we verify all 14,351 hard
   primes up to 10M with explicit witnesses in Lean? This requires:
   - Generating the witness table (Python: done for each p)
   - Encoding in Lean (code generation: feasible)
   - Compile time (each omega/nlinarith call: ~0.01s, total ~150s)

3. **Feasibility of native_decide**: Can `native_decide` verify the sorry
   region for p <= B in reasonable time? The search for each p requires
   trying delta values up to ~50000, which may be too slow for native_decide
   but fast for a precomputed witness table.

4. **Alternative analytic argument**: Is there a simpler existence proof than
   Dyachenko's full lattice density argument? For example:
   - Sieve theory: among p+4, p+16, p+36, ..., p+4s^2, at least one has
     a factor = 3 mod 4 (follows from Landau-Ramanujan, but hard to formalize)
   - Quadratic forms: use p = a^2 + b^2 (guaranteed by Fermat for p=1 mod 4)
     to construct explicit ED2 parameters (unexplored)
   - Reciprocity-based: use properties of (p / q) for specific q values

---

## 8. Recommendation for Aristotle

### Immediate task (highest priority)

1. **Implement the bridge lemma** (Lemma 1 above). This is pure algebra,
   ~25 lines, follows existing patterns. Even if the sorry isn't fully closed,
   this lemma is useful infrastructure.

2. **Implement computational witnesses** for small primes. Write a Python script
   that generates Lean code for each sorry-region prime p <= B, with explicit
   (offset, b, c) witnesses verified by omega. Start with B = 10^5 as a test.

3. **Structure the proof** as:
   ```lean
   theorem ed2_qr_classes ... := by
     by_cases hp_le : p <= B
     · -- computational witnesses
       exact ed2_qr_small p hp ... hp_le
     · -- analytic (sorry for now)
       sorry
   ```
   This separates the computational part (which we can fill in) from the
   analytic part (which remains sorry).

### Secondary task (for later)

4. **Investigate the Fermat two-squares approach**:
   Since p = 1 mod 4, write p = a^2 + b^2 by Fermat's theorem (in Mathlib:
   `ZMod.isSquare_neg_one_iff` or sum-of-squares results).
   Can we use (a, b) to construct ED2 parameters directly?

   Example: p = 73 = 8^2 + 3^2. Can a=8, b=3 give us offset, b, c?
   This is unexplored but potentially fruitful.

5. **Formalize the QNR obstruction proof** (Section 6 of this document).
   This is useful documentation even if the sorry isn't closed: it proves
   that D6 structurally cannot handle all cases.

---

## 9. Concrete Lean Implementation Strategy

This section gives Aristotle the exact blueprint for replacing the sorry
with computational verification for p <= B, following the `native_decide`
pattern already established in the codebase.

### 9.1 Existing Infrastructure to Reuse

The codebase has a proven pattern in `Covering.lean` (lines 10-65):

```lean
-- 1. Structure with DecidableEq
structure Cert where
  p : ℕ; residue_840 : ℕ; k : ℕ; m : ℕ; typ : Bool; x : ℕ; y : ℕ; z : ℕ; d : ℕ
deriving DecidableEq, Repr

-- 2. Decidable validity predicate
def CertOK (c : Cert) : Prop :=
  0 < c.x /\ 0 < c.y /\ 0 < c.z /\ EscEq c.p c.x c.y c.z

-- 3. Bulk verification via native_decide
theorem certs_all_ok : List.Forall CertOK certs := by native_decide

-- 4. Extraction helper
theorem forall_of_forall_mem ... : List.Forall P l -> forall a, a in l -> P a

-- 5. Bridge to conjecture
theorem cert_ok_implies_conjecture (c : Cert) (h : CertOK c) : Conjecture c.p
```

This pattern handles 20,540+ certificates. We replicate it for Type II witnesses.

### 9.2 New Lean Structures

**File: `ErdosStraus/ED2/Type2Data.lean`**

```lean
import Mathlib.Tactic

namespace ED2

/-- Certificate for a sorry-region prime: (p, offset, b, c) satisfying
    offset % 4 = 3, b > 0, c > 0, (p+offset)(b+c) = 4*offset*b*c. -/
structure Type2Cert where
  p : ℕ
  offset : ℕ
  b : ℕ
  c : ℕ
deriving DecidableEq, Repr

/-- Validity predicate (all conditions checkable in ℕ). -/
def Type2CertOK (cert : Type2Cert) : Prop :=
  cert.offset % 4 = 3 ∧
  cert.b > 0 ∧
  cert.c > 0 ∧
  (cert.p + cert.offset) * (cert.b + cert.c) = 4 * cert.offset * cert.b * cert.c

/-- Decidable instance (critical for native_decide). -/
instance (cert : Type2Cert) : Decidable (Type2CertOK cert) := by
  unfold Type2CertOK
  infer_instance

end ED2
```

**IMPORTANT**: The identity is checked in ℕ, not ℤ. This avoids cast issues
in the decidability check. We prove the ℤ version later by casting.

### 9.3 Witness Data File

**File: `ErdosStraus/ED2/Type2CertData.lean`**

Generated by Python (`gen_witnesses.py`). For B = 1,000,000 (750 entries):

```lean
import ErdosStraus.ED2.Type2Data

namespace ED2

def type2Certs : List Type2Cert :=
[
  { p := 1201, offset := 47, b := 8, c := 39 },
  { p := 2521, offset := 55, b := 12, c := 483 },
  { p := 3049, offset := 71, b := 11, c := 8580 },
  -- ... 747 more entries ...
  { p := 999961, offset := 25647, b := 10, c := 512930 }
]

end ED2
```

For B = 10,000,000 (6,959 entries), the file is ~7000 lines. This is
comparable to CoveringData.lean (20,540 lines), so it's well within
Lean's capacity.

**IMPORTANT**: The data file needs `set_option maxRecDepth 65536 in` before
the `def type2Certs` to handle Lean's list elaboration recursion.
Tested: 750 entries (B=1M) compiles in ~130s with this setting.

### 9.4 Verification Theorems

**File: `ErdosStraus/ED2/Type2Covering.lean`**

```lean
import ErdosStraus.ED2.Type2Data
import ErdosStraus.ED2.Type2CertData
import Mathlib.Tactic

namespace ED2

/-- All stored Type II certificates are valid. -/
theorem type2_certs_all_ok : List.Forall Type2CertOK type2Certs := by
  native_decide

/-- Extraction: a valid cert gives the existential (with ℤ identity). -/
theorem type2_cert_ok_gives_witness (cert : Type2Cert) (h : Type2CertOK cert) :
    ∃ offset b c : ℕ,
      offset % 4 = 3 ∧ b > 0 ∧ c > 0 ∧
      (↑cert.p + ↑offset : ℤ) * (↑b + ↑c) = 4 * ↑offset * ↑b * ↑c := by
  refine ⟨cert.offset, cert.b, cert.c, h.1, h.2.1, h.2.2.1, ?_⟩
  have hnat := h.2.2.2
  exact_mod_cast hnat

-- TESTED: Compiles with 750 certs (B=1M), ~150s build time.

end ED2
```

**Coverage verification**: The coverage check (every sorry-region prime
p <= B appears in the list) can be verified via native_decide over
a Fin range, or trusted from the external Python verification.
See Section 9.5 for how to connect without a formal coverage check.

### 9.5 Connecting to the Sorry

The sorry in `Existence.lean:415` needs:

```lean
∃ offset b c : ℕ, offset % 4 = 3 ∧ b > 0 ∧ c > 0 ∧
  (↑p + ↑offset : ℤ) * (↑b + ↑c) = 4 * ↑offset * ↑b * ↑c
```

Replace the sorry with:

```lean
· /- Sorry region: p%7 in {1,2,4}, p%5 in {1,4}, etc. -/
  by_cases hp_small : p ≤ 1000000
  · -- Phase 1: computational verification for p <= B
    -- Step 1: Show p appears in cert list
    have hp_covered : type2Certs.any (fun c => c.p == p) = true := by
      have := sorry_region_covered ⟨p, by omega⟩
      apply this
      -- Show sorryRegionPrime p = true from the hypotheses in context
      simp [sorryRegionPrime]
      exact ⟨hp, hp24_eq, hp7_cond, hp5_cond, hp11_cond, hp19_cond, hp23_cond⟩
    -- Step 2: Extract the certificate
    have ⟨cert, hcert_mem, hcert_p⟩ := List.any_iff_exists.mp hp_covered
    -- Step 3: Get validity from bulk verification
    have hok : Type2CertOK cert :=
      (type2_certs_all_ok.forall cert hcert_mem)
    -- Step 4: Rewrite p and extract existential
    rw [← hcert_p] at *
    exact type2_cert_ok_gives_witness cert hok
  · -- Phase 2: p > B (analytic tail)
    sorry  -- Requires Dyachenko lattice density argument
```

**Important caveats for Aristotle**:

1. The hypotheses in context at the sorry point are negated by_cases
   results. For example, `hp7_not_0 : ¬(p % 7 = 0)`, etc. Converting
   these to `sorryRegionPrime p = true` may require careful omega/simp.

2. The `List.any_iff_exists` extraction gives `c.p == p` as a `BEq`
   result, not propositional equality. May need `BEq.eq_of_beq`.

3. The `push_cast` in `type2_cert_ok_gives_witness` needs to convert
   the ℕ identity `(p+offset)*(b+c) = 4*offset*b*c` to its ℤ version.
   Since all values are natural numbers, `exact_mod_cast` should work.

### 9.6 Alternative Approach: Direct Omega Per Case

If the native_decide coverage check is too slow, an alternative is
to generate Lean code with an explicit case per prime:

```lean
-- Generated by Python for each sorry-region prime p <= B
private theorem sorry_witness_1201 :
    ∃ offset b c : ℕ, offset % 4 = 3 ∧ b > 0 ∧ c > 0 ∧
      (↑(1201 : ℕ) + ↑offset : ℤ) * (↑b + ↑c) = 4 * ↑offset * ↑b * ↑c :=
  ⟨47, 8, 39, by omega, by norm_num, by norm_num, by push_cast; ring⟩

-- Then in the sorry location:
· by_cases hp_small : p ≤ 100000
  · -- Use interval_cases to enumerate all p = 1 mod 24 up to 100000
    -- Each non-sorry-region or non-prime case is eliminated by omega
    -- Each sorry-region prime case uses the corresponding witness theorem
    interval_cases p <;> simp_all <;> omega
    -- OR: explicit decision tree
    ...
  · sorry
```

**Trade-off**: This approach is simpler but generates more Lean code.
For B = 100,000, interval_cases generates ~4167 cases (p = 25, 49, ..., 99,985).
Most are eliminated by omega (not prime or not in sorry region). The 77
sorry-region primes each need an explicit witness (~2 lines each).

Total: ~4167 + 77*2 = ~4300 lines of generated tactic code. This might
be slow to elaborate but avoids the native_decide performance question.

### 9.7 Python Script to Generate Lean Code

Modify `gen_witnesses.py` to output Lean-compatible code:

```python
# gen_lean_type2.py - generates Type2CertData.lean
def gen_lean_cert_data(witnesses, B):
    lines = []
    lines.append("import ErdosStraus.ED2.Type2Data")
    lines.append("")
    lines.append("namespace ED2")
    lines.append("")
    lines.append(f"-- Auto-generated: {len(witnesses)} sorry-region primes up to {B}")
    lines.append("def type2Certs : List Type2Cert :=")
    lines.append("[")
    for i, (p, (offset, b, c)) in enumerate(sorted(witnesses.items())):
        comma = "," if i < len(witnesses) - 1 else ""
        lines.append(f"  {{ p := {p}, offset := {offset}, b := {b}, c := {c} }}{comma}")
    lines.append("]")
    lines.append("")
    lines.append("end ED2")
    return "\n".join(lines)
```

Run: `python3 gen_witnesses.py 1000000` then convert CSV to Lean format.

### 9.8 Recommended Execution Order for Aristotle

1. **Create `Type2Data.lean`**: Define `Type2Cert`, `Type2CertOK`, decidable instance.
   (~20 lines, straightforward)

2. **Generate `Type2CertData.lean`**: Run Python, convert to Lean format.
   Start with B = 100,000 (77 entries) for fast iteration.
   (~85 lines for B=100K, ~760 lines for B=1M)

3. **Create `Type2Covering.lean`**: Prove `type2_certs_all_ok` via native_decide.
   Test with B=100K first. (~15 lines)

4. **Write the bridge theorem** `type2_cert_ok_gives_witness`.
   Pure algebra: ℕ identity => ℤ identity via push_cast. (~10 lines)

5. **Test the sorry replacement** with B=100K:
   - Split sorry into `p <= 100000` and `p > 100000`
   - For small case, try the native_decide coverage approach
   - If coverage check is too slow, fall back to interval_cases

6. **Scale up** to B=1M or B=10M once the pattern is validated.

7. **Document the remaining sorry** (p > B) with a clear reference to
   Dyachenko 2025, Theorem 9.21 and the Landau-Ramanujan density bound.

### 9.9 What the Final Sorry Statement Looks Like

After implementation, the proof structure becomes:

```lean
theorem ed2_qr_classes (p : ℕ) (hp : Nat.Prime p) (hp4 : p % 4 = 1) (hp_ge : p >= 5) :
    ∃ offset b c : ℕ, ... := by
  -- 15 D6 subcases covering mod 3, 5, 7, 8, 11, 19, 23 (existing code)
  ...
  · -- Sorry region: verified computationally for p <= B
    by_cases hp_small : p ≤ B
    · exact ed2_qr_small p hp ... hp_small
    · -- For p > B: requires Dyachenko lattice density argument.
      -- The Dyachenko paper (arXiv:2511.07465, Theorem 9.21) proves
      -- that ED2 parameters exist for all sufficiently large primes.
      -- The threshold B is determined by making the Landau-Ramanujan
      -- density bound quantitative. Formalization blocked on:
      --   1. Landau-Ramanujan theorem (not in Mathlib)
      --   2. Explicit constant computation
      -- Computationally verified: all sorry-region primes up to 10^7
      -- have witnesses (gen_witnesses.py).
      sorry
```

This transforms the sorry from "all sorry-region primes" to
"sorry-region primes > B", which is a strictly stronger partial result.
The documentation makes explicit what mathematical ingredient is missing.
