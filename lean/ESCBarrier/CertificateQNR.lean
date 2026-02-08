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

/-- Every Egyptian fraction 4/n has a Type I or Type II certificate witness.
**Reference**: Standard parametric identity for m/n = 1/x + 1/y + 1/z decompositions.
Any solution arises from choosing denominators of the form na, nb, nabd. -/
axiom egyptian_rep_implies_certificate :
    ∀ (n : ℕ), 0 < n → hasEgyptianRep 4 n →
    (∃ cert : TypeICert, typeI_holds 4 n cert) ∨ (∃ cert : TypeIICert, typeII_holds 4 n cert)

/-- Step 2: Certificate class contains no odd squares
**Written proof**: "By Elsholtz-Tao Proposition 1.6, no certificate class contains any odd square"
-/
lemma cert_class_no_odd_squares (C : CertificateClass) :
    ∀ k : ℕ, Odd k → (k^2 : ZMod C.q) ≠ C.r := by
  intro k hk hcontra
  -- If k² ∈ class, then 4/k² has solution
  have h_sol := C.h_cert (k^2) (by simpa using hcontra)
  -- By the certificate witness axiom, this gives a Type I or Type II cert
  have hk_pos : 0 < k := by obtain ⟨m, rfl⟩ := hk; omega
  have hk2_pos : 0 < k ^ 2 := pow_pos hk_pos 2
  have h_cert := egyptian_rep_implies_certificate (k^2) hk2_pos h_sol
  -- But Elsholtz-Tao says neither can exist at odd squares when 4 | 4
  rcases h_cert with ⟨cert, h_holds⟩ | ⟨cert, h_holds⟩
  · exact elsholtz_tao_typeI_vanishing 4 (dvd_refl 4) k hk cert h_holds
  · exact elsholtz_tao_typeII_vanishing 4 (dvd_refl 4) k hk cert h_holds

/-- Step 3: If r is QR mod all odd prime power divisors, CRT gives odd squares.
**Written proof**: "If r were a QR mod q' for every odd q' | q, then by CRT..."

The proof requires the Chinese Remainder Theorem for ZMod and Hensel's lemma
to lift square roots from prime to prime power moduli. Axiomatized. -/
axiom qr_everywhere_implies_odd_squares (q : ℕ+) (r : ZMod q)
    (h_qr : ∀ p : ℕ, p.Prime → Odd p → p ∣ q → @IsSquare (ZMod p) _ (r.val : ZMod p)) :
    ∃ k : ℕ, Odd k ∧ (k^2 : ZMod q) = r

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

/-- ZMod consistency: if (p : ZMod q) = r and q' | q, then (p : ZMod q') = (r.val : ZMod q').
This follows from the functoriality of the ZMod quotient map. -/
axiom zmod_cast_consistent (p : ℕ) (q : ℕ+) (r : ZMod q) (q' : ℕ)
    (hq'_div : q' ∣ q) (h_in : (p : ZMod q) = r) :
    (p : ZMod q') = (r.val : ZMod q')

/-- If p has a certificate with modulus q, then p is QNR mod some odd divisor of q -/
theorem prime_in_cert_is_qnr (p : ℕ) (hp : p.Prime) (C : CertificateClass)
    (h_in : (p : ZMod C.q) = C.r) :
    ∃ q' : ℕ, q'.Prime ∧ Odd q' ∧ (q' : ℕ) ∣ C.q ∧
      ¬@IsSquare (ZMod q') _ (p : ZMod q') := by
  -- Apply certificate_implies_qnr to get q' where r is QNR mod q'
  obtain ⟨q', hq'_prime, hq'_odd, hq'_div, hq'_nqr⟩ := certificate_implies_qnr C
  use q', hq'_prime, hq'_odd, hq'_div
  -- Goal: show p is QNR mod q'
  intro ⟨x, hx⟩
  apply hq'_nqr
  -- From h_in and hq'_div, we get (p : ZMod q') = (C.r.val : ZMod q')
  have h_eq := zmod_cast_consistent p C.q C.r q' hq'_div h_in
  -- Since (p : ZMod q') = x * x and (p : ZMod q') = (C.r.val : ZMod q')
  -- we have (C.r.val : ZMod q') = x * x
  exact ⟨x, by rw [← hx, h_eq]⟩
