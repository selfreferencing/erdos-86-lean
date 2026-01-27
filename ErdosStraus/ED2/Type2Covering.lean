/-
  Type II Certificate Verification
  =================================

  Proves all stored Type II certificates are valid via native_decide,
  and provides bridge theorems to connect to the sorry in Existence.lean.
-/

import ErdosStraus.ED2.Type2Data
import ErdosStraus.ED2.Type2CertData
import Mathlib.Tactic

namespace ED2

/-- All stored Type II certificates satisfy the validity predicate. -/
theorem type2_certs_all_ok : List.Forall Type2CertOK type2Certs := by
  native_decide

/-- A valid Type II cert gives an existential witness (with ℤ identity). -/
theorem type2_cert_ok_gives_witness (cert : Type2Cert) (h : Type2CertOK cert) :
    ∃ offset b c : ℕ,
      offset % 4 = 3 ∧ b > 0 ∧ c > 0 ∧
      (↑cert.p + ↑offset : ℤ) * (↑b + ↑c) = 4 * ↑offset * ↑b * ↑c := by
  refine ⟨cert.offset, cert.b, cert.c, h.1, h.2.1, h.2.2.1, ?_⟩
  -- Bridge: ℕ identity => ℤ identity
  have hnat := h.2.2.2
  exact_mod_cast hnat

-- To use: for each sorry-region prime p ≤ 1000000, look up its cert,
-- verify via type2_certs_all_ok, and extract via type2_cert_ok_gives_witness.
-- The extraction of a cert for a specific p from the Forall uses
-- ErdosStraus.forall_of_forall_mem from Covering.lean.

end ED2
