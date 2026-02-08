/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 56db09d5-570d-46da-abb1-ba529e0c7507

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

Aristotle encountered an error while processing imports for this file.
You are importing a file that is unknown to Aristotle, Aristotle supports importing user projects, but files must be uploaded as project context, please see the aristotlelib docs or help menu, and ensure your version of `aristotlelib` is up to date.
Details:
unknown module prefix 'ESCBarrier'

No directory 'ESCBarrier' or file 'ESCBarrier.olean' in the search path entries:
/code/harmonic-lean/.lake/packages/batteries/.lake/build/lib/lean
/code/harmonic-lean/.lake/packages/Qq/.lake/build/lib/lean
/code/harmonic-lean/.lake/packages/aesop/.lake/build/lib/lean
/code/harmonic-lean/.lake/packages/proofwidgets/.lake/build/lib/lean
/code/harmonic-lean/.lake/packages/importGraph/.lake/build/lib/lean
/code/harmonic-lean/.lake/packages/LeanSearchClient/.lake/build/lib/lean
/code/harmonic-lean/.lake/packages/plausible/.lake/build/lib/lean
/code/harmonic-lean/.lake/packages/MD4Lean/.lake/build/lib/lean
/code/harmonic-lean/.lake/packages/BibtexQuery/.lake/build/lib/lean
/code/harmonic-lean/.lake/packages/UnicodeBasic/.lake/build/lib/lean
/code/harmonic-lean/.lake/packages/Cli/.lake/build/lib/lean
/code/harmonic-lean/.lake/packages/mathlib/.lake/build/lib/lean
/code/harmonic-lean/.lake/packages/doc-gen4/.lake/build/lib/lean
/code/harmonic-lean/.lake/build/lib/lean
/root/.elan/toolchains/leanprover--lean4---v4.24.0/lib/lean
/root/.elan/toolchains/leanprover--lean4---v4.24.0/lib/lean
-/

/-
# Certificate → Quadratic Nonresidue Reduction

**Written proof reference**: META_THEOREM_PROOF.md, Part II
**Key Lemma**: If a certificate class r (mod q) contains solutions,
then r is a QNR mod some odd prime power q' | q.

## Proof Structure (must match written proof exactly)
1. Certificate defines residue class n ≡ r (mod q)
2. By OddSquareVanishing, class contains no odd squares
3. If r were QR mod all odd q' | q, CRT would give odd squares in class
4. Contradiction. Hence r is QNR mod some odd q' | q.
-/

import ESCBarrier.OddSquareVanishing
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity

/-! ## Certificate Class Definition

**Written proof reference**: META_THEOREM_PROOF.md, "Step 1: Certificate defines a residue class"
-/

/-- A certificate class is a residue class that guarantees solutions -/
structure CertificateClass where
  q : ℕ+                    -- modulus
  r : ZMod q                -- residue
  h_cert : ∀ n : ℕ, (n : ZMod q) = r → hasEgyptianRep 4 n

/-! ## The Key Lemma

**Written proof reference**: META_THEOREM_PROOF.md, "Proposition 2"
-/

/-- Step 2: Certificate class contains no odd squares
**Written proof**: "By Elsholtz-Tao Proposition 1.6, no certificate class contains any odd square"
-/
lemma cert_class_no_odd_squares (C : CertificateClass) :
    ∀ k : ℕ, Odd k → (k^2 : ZMod C.q) ≠ C.r := by
  sorry

/-- Step 3: If r is QR mod all odd prime power divisors, CRT gives odd squares
**Written proof**: "If r were a QR mod q' for every odd q' | q, then by CRT..."
-/
lemma qr_everywhere_implies_odd_squares (q : ℕ+) (r : ZMod q)
    (h_qr : ∀ p : ℕ, p.Prime → Odd p → p ∣ q → @IsSquare (ZMod p) _ (r.val : ZMod p)) :
    ∃ k : ℕ, Odd k ∧ (k^2 : ZMod q) = r := by
  sorry

/-- The Key Lemma: Certificate → QNR
**Written proof**: META_THEOREM_PROOF.md, Proposition 2
-/
theorem certificate_implies_qnr (C : CertificateClass) :
    ∃ p : ℕ, p.Prime ∧ Odd p ∧ (p : ℕ) ∣ C.q ∧
      ¬@IsSquare (ZMod p) _ (C.r.val : ZMod p) := by
  -- Step 2: Class contains no odd squares
  have h_no_sq := cert_class_no_odd_squares C
  -- Step 3: Contrapositive of qr_everywhere_implies_odd_squares
  by_contra h_all_qr
  push_neg at h_all_qr
  -- If QR everywhere, we get an odd square in the class
  have ⟨k, hk_odd, hk_sq⟩ := qr_everywhere_implies_odd_squares C.q C.r (by
    intro p hp_prime hp_odd hp_div
    exact h_all_qr p hp_prime hp_odd hp_div)
  -- But this contradicts Step 2
  exact h_no_sq k hk_odd hk_sq

/-! ## Corollary: Bounded Certificates Require Bounded Nonresidues

**Written proof reference**: META_THEOREM_PROOF.md, "Corollary (Finite Covering Barrier)"
-/

/-- If p has a certificate with modulus q, then p is QNR mod some odd divisor of q -/
theorem prime_in_cert_is_qnr (p : ℕ) (hp : p.Prime) (C : CertificateClass)
    (h_in : (p : ZMod C.q) = C.r) :
    ∃ q' : ℕ, q'.Prime ∧ Odd q' ∧ (q' : ℕ) ∣ C.q ∧
      ¬@IsSquare (ZMod q') _ (p : ZMod q') := by
  -- Apply certificate_implies_qnr
  obtain ⟨q', hq'_prime, hq'_odd, hq'_div, hq'_nqr⟩ := certificate_implies_qnr C
  use q', hq'_prime, hq'_odd, hq'_div
  -- p ≡ r (mod q) and r is QNR mod q', so p is QNR mod q'
  sorry
