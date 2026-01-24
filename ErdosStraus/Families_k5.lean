import ErdosStraus.Covering
import ErdosStraus.CoveringData
import Mathlib.Tactic

namespace ErdosStraus

/-- Sublist of dataset certificates that use k = 5. -/
def certs_k5 : List Cert := certs.filter (fun c => c.k = 5)

theorem certs_k5_all_ok : List.Forall CertOK certs_k5 := by
  native_decide

theorem certs_k5_all_m_matches : List.Forall CertMMatches certs_k5 := by
  native_decide

theorem certs_k5_all_k_in_set : List.Forall CertKInSet certs_k5 := by
  native_decide

end ErdosStraus
