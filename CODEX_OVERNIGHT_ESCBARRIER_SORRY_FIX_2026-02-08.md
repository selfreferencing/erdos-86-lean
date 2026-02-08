# Codex Overnight Task: Close All Sorry Stubs in ESCBarrier/

## Date: 2026-02-08 (overnight run)
## Target: Eliminate every `sorry` in `lean/ESCBarrier/` so all four main theorems compile cleanly
## Environment: Lean 4 with Mathlib (commit f897ebcf72cd16f89ab4577d0c826cd14afaafc7, approx v4.24.0)
## Build command: `lake build` from the `lean/` directory

---

## Overview

The ESCBarrier project formalizes the internal parity barrier for the
Erdos-Strauss Conjecture (ESC). It has four main theorems in `Main.lean`:

1. `four_divides_iff_vanishing`: Type I/II solutions vanish at odd squares iff 4|m
2. `certificate_barrier`: Certificate classes force quadratic nonresidues
3. `esc_under_grh`: GRH implies ESC for all primes
4. `meta_theorem_barrier`: Bounded certificates reduce to bounded nonresidues

All four delegate to lemmas in other files. Those lemmas contain approximately
15 sorry stubs. Your job is to close them all, or as many as possible.

**CRITICAL BUILD RULE**: After fixing each file, run `lake build` to verify
it compiles. Do NOT move to the next file until the current one compiles.
If a sorry proves genuinely impossible to close, leave it with a detailed
comment explaining why, and move on.

---

## STRUCTURAL BUG ALERT

### `reciprocity_contradiction` in OddSquareVanishing.lean is WRONG

The lemma is stated as:

```lean
lemma reciprocity_contradiction (cert : TypeICert) (k : ℕ) (hk : Odd k)
    (h_e : (cert.e : ℕ) % 4 = 3) : False
```

This tries to derive False from `e ≡ 3 (mod 4)` alone. But this is NOT a
contradiction: take `a = 1, b = 2, d = 1, e = 3` and any odd k. All
hypotheses are satisfied but there is no contradiction.

**The fix**: The contradiction requires the Type I equation as a hypothesis.
The correct statement should be:

```lean
lemma reciprocity_contradiction (cert : TypeICert) (m : ℕ) (k : ℕ) (hk : Odd k)
    (h_holds : typeI_holds m (k^2) cert)
    (h_four : 4 ∣ m)
    (h_e : (cert.e : ℕ) % 4 = 3) : False
```

Or alternatively, restructure `typeI_vanishes_at_odd_squares_m4` to prove the
contradiction directly without this intermediate lemma.

**The mathematical argument** (from Elsholtz-Tao Proposition 1.6):
From `m * a * b * d = k^2 * e + 1` with `4 | m`, `k` odd, and `e = a + b`:
- We derived `e ≡ 3 (mod 4)` (this part is correct and proved)
- Since `e ≡ 3 (mod 4)`, there exists an odd prime `p | e` with `p ≡ 3 (mod 4)`
- From the equation: `m*a*b*d ≡ k^2*e + 1 (mod p)`. Since `p | e`, this gives
  `m*a*b*d ≡ 1 (mod p)`, so `gcd(m*a*b*d, p) = 1`
- But also from the equation considered mod `a*b`: `0 ≡ k^2*e + 1 (mod a*b)`,
  i.e., `k^2*(a+b) ≡ -1 (mod a*b)`. Since `gcd(a, a+b) | gcd(a,b)` ... this gets
  into the details of the Elsholtz-Tao argument which uses Jacobi symbols.

**Recommended approach**: Instead of trying to reconstruct the exact Elsholtz-Tao
argument, use a DIRECT proof that combines the mod 4 analysis with the equation:

From `4*q*a*b*d = k^2*(a+b) + 1` (where m = 4q):
- This means `k^2*(a+b) ≡ -1 (mod 4)`
- Since k is odd, `k^2 ≡ 1 (mod 4)`
- So `(a+b) ≡ -1 ≡ 3 (mod 4)` (this we already have)
- Now consider the equation mod 2: `0 ≡ k^2*(a+b) + 1 ≡ (a+b) + 1 (mod 2)`
- So `a + b` is odd, meaning exactly one of a, b is even
- WLOG a is odd and b is even (or vice versa)
- From the equation mod a: `0 ≡ k^2*b + 1 (mod a)`, so `k^2*b ≡ -1 (mod a)`
- From the equation mod b: `0 ≡ k^2*a + 1 (mod b)`, so `k^2*a ≡ -1 (mod b)`
- Now consider the Jacobi symbol `(k^2*b / a) = (b / a)` and `(-1 / a)`...

This is where the QR machinery enters. The precise contradiction depends on
the interaction between `(-1/a)`, `(b/a)`, `(-1/b)`, `(a/b)` and the
constraint `a + b ≡ 3 (mod 4)`.

**If this restructuring proves too complex**: An alternative is to AXIOMATIZE
this result (it IS proved in the Elsholtz-Tao paper) and focus on the other
sorry stubs. Use:

```lean
axiom elsholtz_tao_1_6 : ∀ (m : ℕ) (hm : 4 ∣ m) (k : ℕ) (hk : Odd k)
    (cert : TypeICert), ¬typeI_holds m (k^2) cert
```

This would let you close all downstream sorry stubs that depend on this result.
Only use this fallback after spending real effort on the proof.

---

## File-by-File Sorry Catalog and Proof Strategies

### Priority Order (by dependency):

1. **OddSquareVanishing.lean** (3 sorry) - everything depends on this
2. **CertificateQNR.lean** (3 sorry) - depends on OddSquareVanishing
3. **Periodicity.lean** (3 sorry) - needed by CoverageLemma
4. **CoverageLemma.lean** (2 sorry) - needed by Main
5. **GRHConditional.lean** (4 sorry) - depends on CertificateQNR
6. **AnalyticTheorems.lean** (5+ sorry) - alternate coverage path
7. **Mod8Coverage.lean** (6+ sorry) - another alternate coverage path

Files 6-7 are NOT imported by Main.lean. They are alternate approaches to
the coverage argument. Prioritize files 1-5.

---

### File 1: OddSquareVanishing.lean

**Already proved** (no changes needed):
- `odd_square_mod_eight`: k odd => k^2 ≡ 1 (mod 8)
- `typeI_forces_e_mod_four`: Type I + k odd => e ≡ 3 (mod 4)

**Sorry 1.1: `reciprocity_contradiction`** (STRUCTURAL FIX REQUIRED)

See the STRUCTURAL BUG ALERT above. Either:
(a) Add typeI_holds hypothesis and prove the QR contradiction, OR
(b) Merge into typeI_vanishes_at_odd_squares_m4 directly, OR
(c) Axiomatize if proof is too complex

If you choose (a), update `typeI_vanishes_at_odd_squares_m4` to pass the
typeI_holds hypothesis through.

**Sorry 1.2: `typeII_vanishes_at_odd_squares_m4`**

```lean
theorem typeII_vanishes_at_odd_squares_m4 (k : ℕ) (hk : Odd k) :
    ∀ cert : TypeIICert, ¬typeII_holds 4 (k^2) cert
```

The Type II equation is `m * a * b * d = n + e`, i.e., `4*a*b*d = k^2 + (a+b)`.
The argument is analogous to Type I:
- `4*a*b*d = k^2 + a + b`
- Mod 4: `0 ≡ k^2 + a + b (mod 4)`, and k^2 ≡ 1 (mod 4), so `a + b ≡ 3 (mod 4)`
- Same QR contradiction follows

Structure the proof parallel to the Type I case.

**Sorry 1.3: `typeII_vanishes_when_four_divides`**

```lean
theorem typeII_vanishes_when_four_divides (m : ℕ) (hm : 4 ∣ m) (k : ℕ) (hk : Odd k) :
    ∀ cert : TypeIICert, ¬typeII_holds m (k^2) cert
```

Same generalization as `typeI_vanishes_when_four_divides` (which is already proved
modulo the reciprocity_contradiction). Write m = 4q, then the Type II equation
`4q*a*b*d = k^2 + e` gives the same mod 4 analysis: `k^2 + e ≡ 0 (mod 4)`,
so `e ≡ 3 (mod 4)`, and the same QR argument applies.

---

### File 2: CertificateQNR.lean

**Sorry 2.1: `cert_class_no_odd_squares`**

```lean
lemma cert_class_no_odd_squares (C : CertificateClass) :
    ∀ k : ℕ, Odd k → (k^2 : ZMod C.q) ≠ C.r
```

Strategy: If k^2 ≡ r (mod q), then hasEgyptianRep 4 (k^2) by C.h_cert.
But hasEgyptianRep 4 (k^2) means 4/(k^2) = 1/x + 1/y + 1/z.

The connection to OddSquareVanishing: we need that for odd k, there is NO
solution to 4/(k^2). But `hasEgyptianRep` is defined using rational arithmetic
(4/n = 1/x + 1/y + 1/z in Q), while OddSquareVanishing uses TypeICert.

This gap needs bridging. You need to show:
- If hasEgyptianRep 4 (k^2), then either a TypeICert or TypeIICert exists
- But OddSquareVanishing says no TypeI or TypeII cert exists for odd k
- Therefore hasEgyptianRep 4 (k^2) is false for odd k

The first step requires decomposing 4/(k^2) = 1/x + 1/y + 1/z into
the parametric form. This is standard: the Egyptian fraction 4/n = 1/x + 1/y + 1/z
can always be written in Type I or Type II form (Elsholtz-Tao framework).

If this decomposition is hard to prove: you can axiomatize the link between
hasEgyptianRep and TypeI/TypeII existence. Use:

```lean
axiom egyptian_rep_iff_type_I_or_II (m n : ℕ) :
    hasEgyptianRep m n ↔
    (∃ cert : TypeICert, typeI_holds m n cert) ∨
    (∃ cert : TypeIICert, typeII_holds m n cert)
```

With this axiom, cert_class_no_odd_squares follows from
typeI_vanishes_at_odd_squares_m4 and typeII_vanishes_at_odd_squares_m4.

**Preferred approach**: Actually, looking at the usage in `certificate_implies_qnr`,
we just need `cert_class_no_odd_squares`. If we have `four_divides_iff_vanishing`
with m = 4, the "if" direction gives vanishing. But the cert class guarantees
solutions exist (C.h_cert). So the contradiction is: C.h_cert says hasEgyptianRep
holds, but vanishing says it doesn't. The bridge is the axiom above.

**Sorry 2.2: `qr_everywhere_implies_odd_squares`**

```lean
lemma qr_everywhere_implies_odd_squares (q : ℕ+) (r : ZMod q)
    (h_qr : ∀ p : ℕ, p.Prime → Odd p → p ∣ q →
      @IsSquare (ZMod p) _ (r.val : ZMod p)) :
    ∃ k : ℕ, Odd k ∧ (k^2 : ZMod q) = r
```

Strategy: This is a CRT + quadratic residue argument.
- For each odd prime power p^a dividing q, since r is a QR mod p, by Hensel's
  lemma r is a QR mod p^a. Get x_p with x_p^2 ≡ r (mod p^a).
- For the 2-adic part: handle separately (2-adic lifting).
- CRT combines all x_p values into x with x^2 ≡ r (mod q).
- To ensure k is odd: if x is even, use q - x (which has the same square mod q).
  Since q has an odd prime factor (otherwise q is a power of 2 and the
  "odd p" hypothesis is vacuous), we can adjust.

Mathlib has:
- `ZMod.isSquare_of_isSquare_mod_prime` or similar
- `ChineseRemainder` for the CRT step
- Hensel's lemma may be in `Mathlib.NumberTheory.Padics`

This is a HARD lemma. If it can't be proved from Mathlib directly, axiomatize it.

**Sorry 2.3: `prime_in_cert_is_qnr`**

```lean
theorem prime_in_cert_is_qnr (p : ℕ) (hp : p.Prime) (C : CertificateClass)
    (h_in : (p : ZMod C.q) = C.r) :
    ∃ q' : ℕ, q'.Prime ∧ Odd q' ∧ (q' : ℕ) ∣ C.q ∧
      ¬@IsSquare (ZMod q') _ (p : ZMod q')
```

The sorry is at the end, after getting q' from certificate_implies_qnr.
Need to show: since p ≡ r (mod q) and q' | q, we have p ≡ r (mod q'),
and since r is QNR mod q', so is p.

This requires ZMod coercion compatibility:
- `(p : ZMod C.q) = C.r` and `q' | C.q` implies `(p : ZMod q') = (C.r.val : ZMod q')`
- Then `¬IsSquare (C.r.val : ZMod q')` gives `¬IsSquare (p : ZMod q')`

Mathlib API:
- `ZMod.castHom` for the map ZMod q -> ZMod q' when q' | q
- `ZMod.ringHom_map_cast` or similar

This should be provable but requires navigating Mathlib's ZMod API carefully.

---

### File 3: Periodicity.lean

**Sorry 3.1: `qr_condition_factors_by_crt`**

```lean
lemma qr_condition_factors_by_crt (a b e m : ℕ) :
    constructionWorks a b e m ↔
    (∀ p : ℕ, p.Prime → p ∣ m * a * b →
      ∃ k : ℕ, (k^2 * e + 1) % p = 0) ∧
    (∃ k : ℕ, Odd k)
```

The statement itself seems wrong (the conclusion `∃ k, Odd k` is trivially true
and the factoring doesn't account for prime powers or the odd constraint on k).
The real CRT factoring would be more involved.

**Recommendation**: This entire file (Periodicity.lean) represents the "periodicity
approach" to coverage. It has 3 sorry stubs and the statements may need revision.
Consider whether the "mod 8 partition approach" (AnalyticTheorems.lean) is a better
path. If so, modify CoverageLemma.lean to NOT import Periodicity.lean and instead
use the mod 8 approach directly.

**Sorry 3.2: `periodicity_principle`** and **Sorry 3.3: `verification_extends`**

Both depend on a correct CRT factoring. If the mod 8 approach is used instead,
these become unnecessary.

---

### File 4: CoverageLemma.lean

**Sorry 4.1: `portfolio_covers_small`**

```lean
theorem portfolio_covers_small (m : ℕ) (hm_pos : 0 < m) (hm_le : m ≤ 100)
    (hm : ¬ 4 ∣ m) :
    ∃ t ∈ portfolio, let (a, b, e) := t; constructionWorks a b e m
```

Strategy: This is a FINITE verification. For each of the 75 values of m from
1 to 100 with 4∤m, provide an explicit witness (a, b, e, k).

**Approach A (native_decide)**: Make constructionWorks decidable and use
`native_decide`. This requires a `Decidable` instance for `constructionWorks`:

```lean
instance : DecidableEq (ℕ × ℕ × ℕ) := inferInstance

instance constructionWorks_decidable (a b e m : ℕ) : Decidable (constructionWorks a b e m) := by
  unfold constructionWorks
  -- Need to decide ∃ k, Odd k ∧ (k^2 * e + 1) % (m * a * b) = 0
  -- Bounded: k < m * a * b suffices (since k^2*e+1 mod mab is periodic)
  sorry -- construct the Decidable instance
```

This is tricky because the existential is unbounded. A simpler approach:

**Approach B (explicit witnesses)**: For each m, provide the witness directly.
Omega-style case analysis:

```lean
theorem portfolio_covers_small (m : ℕ) (hm_pos : 0 < m) (hm_le : m ≤ 100)
    (hm : ¬ 4 ∣ m) :
    ∃ t ∈ portfolio, let (a, b, e) := t; constructionWorks a b e m := by
  interval_cases m <;> simp_all [portfolio, constructionWorks] <;>
    first
    | exact ⟨(1,1,2), by simp [portfolio], 1, by decide, by decide⟩
    | exact ⟨(1,1,2), by simp [portfolio], 3, by decide, by decide⟩
    | ...  -- 75 cases
```

This might be too slow for `interval_cases` with 100 cases. Alternative:

**Approach C (omega + decide per case)**: Use a helper that takes m as input
and returns the witness, then verify with `decide`:

```lean
-- Build a lookup table
def coverageWitness : ℕ → ℕ × ℕ × ℕ × ℕ  -- returns (a, b, e, k)
  | 1 => (1, 1, 2, 1)
  | 2 => (1, 2, 3, 1)
  | 3 => (1, 1, 2, 1)
  | 5 => (1, 1, 2, 3)
  -- ... etc for all 75 values
  | _ => (0, 0, 0, 0)  -- shouldn't be reached
```

Then prove `portfolio_covers_small` by extracting from the lookup table.

**Recommendation**: Try Approach A first (native_decide). If it fails due to
unbounded existential, fall back to Approach C with explicit witnesses.
You can compute witnesses using the `findSmallestWitness` function in
ComputationalVerification.lean or QuickPatternScan.lean.

**Sorry 4.2: `coverage_lemma`**

```lean
theorem coverage_lemma (m : ℕ) (hm_pos : 0 < m) (hm : ¬ 4 ∣ m) :
    ∃ k : ℕ, Odd k ∧ ∃ cert : TypeICert, typeI_holds m (k^2) cert
```

This needs TWO things:
1. A constructionWorks witness for m (from portfolio coverage)
2. Converting constructionWorks to TypeICert + typeI_holds

For (1): Either use the periodicity route or the mod 8 analytic route.
For (2): From constructionWorks a b e m, we have k with Odd k and
(k^2 * e + 1) % (m * a * b) = 0. Set d = (k^2 * e + 1) / (m * a * b).
Then m * a * b * d = k^2 * e + 1, and with e = a + b, this gives a
TypeICert. Need to verify d > 0 (it is, since k^2 * e + 1 > 0 and m*a*b > 0
and divisibility holds).

The key helper is already partly proved: `typeI_reduces_to_qr` in
CoverageLemma.lean shows the equivalence.

**If periodicity is skipped**: Restructure coverage_lemma to use mod 8
partition. This would require:
- Importing AnalyticTheorems.lean (or copying the relevant theorems)
- Using `portfolio_covers_all_mod8_classes` from AnalyticTheorems.lean
- Converting from constructionWorks to TypeICert

---

### File 5: GRHConditional.lean

**Sorry 5.1: `certificate_exists_under_grh`**

```lean
theorem certificate_exists_under_grh (h_grh : GRH) (p : ℕ) (hp : p.Prime) (hp2 : p > 2) :
    ∃ q : ℕ, q.Prime ∧ q ≤ (Nat.log p)^2 ∧ ¬@IsSquare (ZMod q) _ (p : ZMod q)
```

Strategy: The `ankeny_bound` axiom gives `leastNonresidue p ≤ (Nat.log p)^2`.
The `nonresidue_exists` axiom gives that a nonresidue exists (some n > 1, n < p,
not a square mod p). The `leastNonresidue` is defined via Classical.choose.

We need: the least nonresidue q = leastNonresidue p satisfies:
- q is prime (or has a prime factor that works)
- q ≤ (Nat.log p)^2
- p is QNR mod q

The issue: leastNonresidue might not be prime. It's the least n > 1 that is
a QNR mod p. But we need q prime with p QNR mod q (the roles are swapped!).

Actually, there's a conceptual issue here. The Ankeny bound bounds the least
QNR mod p (i.e., the least n with (n/p) = -1). But the theorem wants a prime
q with (p/q) = -1 (p is QNR mod q). These are different things!

By quadratic reciprocity: for odd primes p, q with p ≡ q ≡ 3 (mod 4),
(p/q) = -(q/p). Otherwise (p/q) = (q/p). So the Legendre symbols (p/q) and
(q/p) are related but not identical.

**Resolution**: The least QNR mod p, call it q_0, satisfies (q_0/p) = -1.
If q_0 is prime, then by QR: (p/q_0) = (q_0/p) * (-1)^{(p-1)(q_0-1)/4}.
So (p/q_0) = -1 iff exactly one of (q_0/p) = -1 (which we have) and
(-1)^{...} = -1 holds. This doesn't always give (p/q_0) = -1.

This means the simple approach doesn't work directly. The certificate_exists
theorem may need a different proof strategy that doesn't go through the
least QNR directly.

**Alternative**: The Ankeny bound under GRH actually gives a prime q ≤ (log p)^2
such that (p/q) = -1. This is because:
- Under GRH, for any non-principal character chi mod m, there exists n ≤ (log m)^2
  with chi(n) ≠ 0, 1.
- Taking m = p and chi = (./p) the Legendre symbol: there exists prime q ≤ (log p)^2
  with (q/p) = -1.
- By QR, from (q/p) = -1, we can derive info about (p/q).

This is getting into deep analytic number theory. If the direct proof is too
hard, axiomatize:

```lean
axiom grh_gives_small_qnr_prime (h : GRH) (p : ℕ) (hp : p.Prime) (hp2 : p > 2) :
    ∃ q : ℕ, q.Prime ∧ q ≤ (Nat.log p)^2 ∧ ¬@IsSquare (ZMod q) _ (p : ZMod q)
```

**Sorry 5.2: `grh_implies_esc_large`**

```lean
theorem grh_implies_esc_large (h_grh : GRH) :
    ∃ N : ℕ, ∀ p : ℕ, p.Prime → p > N → hasEgyptianRep 4 p
```

Strategy: Under GRH, for large p, there's a small prime q with p QNR mod q.
This q provides a certificate class. By `coverage_lemma` (for the "only if"
direction) or by direct construction, this gives an Egyptian fraction.

This depends on `certificate_exists_under_grh` and the connection between
certificates and Egyptian fractions.

The argument: if p is QNR mod some small q, then p lies in a certificate
class mod q. The certificate class construction (from the portfolio) gives
hasEgyptianRep 4 p.

But this requires connecting `coverage_lemma` (which is about Type I solutions
at odd squares) to `hasEgyptianRep`. And `coverage_lemma` itself has sorry.

**Recommended**: If `coverage_lemma` and `certificate_exists_under_grh` are
both proved (or axiomatized), this theorem becomes an assembly step. Prove
the assembly assuming the pieces.

**Sorry 5.3: `grh_implies_esc`**

```lean
theorem grh_implies_esc (h_grh : GRH) :
    ∀ p : ℕ, p.Prime → hasEgyptianRep 4 p
```

Strategy: Combine `grh_implies_esc_large` (for p > N) with finite verification
for p ≤ N. The finite verification can use `decide` or explicit witnesses.

For small primes, 4/p = 1/x + 1/y + 1/z is known for all p ≤ 10^14 or more.
For our purposes, p ≤ some computable N (from grh_implies_esc_large) suffices.

If N is not explicitly computed, this can be axiomatized or left as:
```lean
-- Finite verification for small primes
axiom esc_small_primes (p : ℕ) (hp : p.Prime) (hp_le : p ≤ 10000) :
    hasEgyptianRep 4 p
```

**Sorry 5.4: `bounded_cert_implies_bounded_nonresidue`**

```lean
theorem bounded_cert_implies_bounded_nonresidue
    (B : ℕ → ℕ)
    (h_cert : ∀ p : ℕ, p.Prime → ∃ C : CertificateClass, C.q ≤ B p ∧ (p : ZMod C.q) = C.r) :
    ∀ p : ℕ, p.Prime → leastNonresidue p ≤ B p
```

Strategy: From h_cert, for each prime p, there's a certificate C with modulus
≤ B(p) and p ≡ C.r (mod C.q). By `prime_in_cert_is_qnr`, there exists a prime
q' | C.q with p QNR mod q'. Since q' | C.q ≤ B(p), we have q' ≤ B(p).

Now we need: q' is a QNR mod p (by QR: if p is QNR mod q', then...). Wait,
this has the same issue as certificate_exists_under_grh: the roles of p and q'
are swapped.

Actually, `prime_in_cert_is_qnr` gives: p is QNR mod q' (¬IsSquare (p : ZMod q')).
But `leastNonresidue p` is the least n with n QNR mod p (¬IsSquare (n : ZMod p)).
These are different!

This is a genuine mathematical issue. The certificate approach shows p is QNR
mod some q', but the meta-theorem wants to conclude the least QNR mod p is
bounded. These are related by quadratic reciprocity but not identical.

**Option 1**: Strengthen `certificate_implies_qnr` to give a QNR mod p
(not p mod q'). This would require a different argument.

**Option 2**: Change the meta-theorem statement to bound the least q with
p QNR mod q (rather than the least QNR mod p). This is what the certificate
naturally gives.

**Option 3**: Use QR to convert. For odd primes p, q' with p QNR mod q':
by QR, (p/q') * (q'/p) = (-1)^{(p-1)(q'-1)/4}. So:
- If (p-1)(q'-1)/4 is even: (q'/p) = (p/q') = -1, so q' IS a QNR mod p
- If (p-1)(q'-1)/4 is odd: (q'/p) = -(p/q') = 1, so q' is a QR mod p

So the conversion works HALF the time. For the other half, we'd need a
different argument. This suggests the certificate-to-nonresidue link is
more subtle than stated.

**Recommendation**: Try Option 3. When QR gives the wrong sign, consider
q' * p' for another small prime p' as a potential nonresidue. Or axiomatize
if this gets too complex.

---

### Files 6-7: AnalyticTheorems.lean and Mod8Coverage.lean (NOT on critical path)

These files are NOT imported by Main.lean. They represent alternate approaches
to portfolio coverage. If you finish files 1-5 early, work on these.

The key sorry in AnalyticTheorems.lean is `construction_112_covers_mod8_classes`,
which requires proving that construction (1,1,2) works for all m ≡ 1,3 (mod 8).
This needs:
- Mathlib's `ZMod.exists_sq_eq_two_iff` or `legendreSym.at_two`
- Hensel's lemma for lifting from primes to prime powers
- CRT for combining solutions
- Parity adjustment (ensuring odd k)

---

## Mathlib API Reference

Key Mathlib imports and their useful lemmas:

### Quadratic Reciprocity
```lean
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
import Mathlib.NumberTheory.LegendreSymbol.Basic

-- Key lemmas:
-- legendreSym.quadratic_reciprocity : QR law
-- legendreSym.at_two : (2/p) characterization
-- legendreSym.at_neg_one : (-1/p) = (-1)^((p-1)/2)
-- ZMod.isSquare_neg_one_iff : characterization of when -1 is a square
```

### ZMod
```lean
import Mathlib.Data.ZMod.Basic

-- Key lemmas:
-- ZMod.val_natCast : coercion properties
-- ZMod.natCast_zmod_eq_zero_iff_dvd : n ≡ 0 (mod m) iff m | n
-- ZMod.ringHom_map_cast : compatibility of ring homs with coercions
-- ZMod.castHom : ring hom from ZMod q to ZMod q' when q' | q
```

### CRT
```lean
import Mathlib.Data.ZMod.Quotient
-- Or
import Mathlib.RingTheory.Ideal.Operations

-- ZMod.chineseRemainder : CRT isomorphism
```

### IsSquare
```lean
-- IsSquare x means ∃ y, x = y * y  (or y^2)
-- Use IsSquare.mul, IsSquare.pow, etc.
```

---

## Build and Verification

After each file modification:

```bash
lake build ESCBarrier.OddSquareVanishing  # build specific module
lake build ESCBarrier.CertificateQNR
lake build ESCBarrier.Periodicity
lake build ESCBarrier.CoverageLemma
lake build ESCBarrier.GRHConditional
lake build ESCBarrier.Main               # final check
lake build                                # full build
```

Use `lake build 2>&1 | head -50` to see errors without overwhelming output.

---

## Summary of Recommended Priority

1. **Fix reciprocity_contradiction** (structural fix, highest priority)
2. **Close typeII sorry stubs** (parallel to Type I, should be straightforward)
3. **Close cert_class_no_odd_squares** (bridge between vanishing and certificates)
4. **Close prime_in_cert_is_qnr** (ZMod coercion, medium difficulty)
5. **Close qr_everywhere_implies_odd_squares** (CRT + QR, hard)
6. **Close portfolio_covers_small** (computational, explicit witnesses)
7. **Close coverage_lemma** (assembly)
8. **Close GRH conditional stubs** (may require axiomatization)
9. **Close bounded_cert_implies_bounded_nonresidue** (QR conversion, subtle)

## Axiom Budget

If a proof genuinely cannot be closed, use an axiom with the prefix
`axiom sorry_` and a detailed docstring explaining:
- What the axiom states
- Why it's mathematically true (paper reference)
- Why the Lean proof failed
- What Mathlib API gap blocked it

Maximum axiom budget: 5 new axioms (beyond the 3 already in GRHConditional.lean).
Fewer is better. Zero new axioms is the goal.

## Stopping Criterion

- **Best**: All sorry stubs closed. `lake build` succeeds with zero warnings.
- **Good**: Critical-path sorry stubs closed (files 1-5). Supplementary files
  (6-7) may still have sorry. Main.lean compiles cleanly.
- **Fallback**: Structural bug fixed, Type I/II vanishing proved, some stubs
  axiomatized with clear documentation.
- **Worst**: Structural bug identified but not fixed. Some progress on easy stubs.

## Final Notes

- The `_aristotle` files (e.g., `OddSquareVanishing_aristotle.lean`) are older
  versions. Ignore them.
- `ComputationalVerification.lean`, `QuickPatternScan.lean`, and
  `AnalyticFromComputational.lean` are exploration files. They are NOT on the
  critical path. Ignore them unless you need computational witnesses.
- The `constructionWorks` definition appears in MULTIPLE files with the SAME
  definition. This will cause conflicts if multiple files are imported. The
  canonical definition should be in `Basic.lean` or `Periodicity.lean`.
  Consider deduplicating if build errors arise.
- `Mod8Coverage.lean` also redefines `portfolio`. Same deduplication issue.
