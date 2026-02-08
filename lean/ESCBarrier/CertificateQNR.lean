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
  intro k hk hcontra
  -- If k² ∈ class, then 4/k² has solution
  have h_sol := C.h_cert (k^2) hcontra
  -- But typeI_vanishes_at_odd_squares_m4 says no solution exists
  -- This is the connection to OddSquareVanishing.lean
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
  -- Apply certificate_implies_qnr to get q' where r is QNR mod q'
  obtain ⟨q', hq'_prime, hq'_odd, hq'_div, hq'_nqr⟩ := certificate_implies_qnr C
  use q', hq'_prime, hq'_odd, hq'_div
  -- Goal: show p is QNR mod q'
  -- Key insight: p ≡ r (mod q) and q' | q implies p ≡ r (mod q')
  -- Since r is QNR mod q', so is p
  intro ⟨x, hx⟩
  -- If p were a QR mod q', then p ≡ x² (mod q') for some x
  -- We know C.r.val ≡ C.r (mod q')
  -- From h_in: p ≡ C.r (mod q), so p ≡ C.r.val (mod q')
  -- This would make C.r.val a square mod q', contradicting hq'_nqr
  apply hq'_nqr
  -- Need to show C.r.val is a square mod q'
  -- Since p ≡ C.r (mod q) and q' | q, we have p ≡ C.r.val (mod q')
  -- And p ≡ x² (mod q'), so C.r.val ≡ x² (mod q')
  sorry
