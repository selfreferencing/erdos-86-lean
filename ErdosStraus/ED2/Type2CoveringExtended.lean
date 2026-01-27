/-
  Extended Type II Certificate Verification
  ==========================================

  Proves all 142 extended certificates are valid via native_decide,
  and provides bridge theorems for the sorry replacement in Existence.lean.

  This is a SEPARATE compilation unit from Existence.lean, so it does
  not contribute to that file's memory footprint.
-/

import ErdosStraus.ED2.Type2Data
import ErdosStraus.ED2.Type2CertDataExtended
import ErdosStraus.Covering
import Mathlib.Tactic

namespace ED2

/-- All 142 extended certificates satisfy the validity predicate. -/
theorem type2_certs_extended_all_ok :
    List.Forall Type2CertOK type2CertsExtended := by
  native_decide

/-- A valid cert in the extended list gives an existential witness. -/
theorem type2_extended_gives_witness (cert : Type2Cert)
    (h_mem : cert ∈ type2CertsExtended) :
    ∃ offset b c : ℕ,
      offset % 4 = 3 ∧ b > 0 ∧ c > 0 ∧
      (↑cert.p + ↑offset : ℤ) * (↑b + ↑c) = 4 * ↑offset * ↑b * ↑c := by
  have h_ok : Type2CertOK cert :=
    forall_of_forall_mem type2_certs_extended_all_ok cert h_mem
  exact type2_cert_ok_gives_witness cert h_ok

/-- The list of primes covered by extended certificates. -/
def extendedCertPrimes : List ℕ := type2CertsExtended.map Type2Cert.p

/-- If prime p appears in the extended cert list, solution exists. -/
theorem ed2_extended_prime_covered (p : ℕ)
    (h_mem : p ∈ extendedCertPrimes) :
    ∃ offset b c : ℕ,
      offset % 4 = 3 ∧ b > 0 ∧ c > 0 ∧
      (↑p + ↑offset : ℤ) * (↑b + ↑c) = 4 * ↑offset * ↑b * ↑c := by
  simp only [extendedCertPrimes, List.mem_map] at h_mem
  obtain ⟨cert, h_cert_mem, h_eq⟩ := h_mem
  subst h_eq
  exact type2_extended_gives_witness cert h_cert_mem

end ED2
