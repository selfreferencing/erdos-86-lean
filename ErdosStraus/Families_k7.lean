import ErdosStraus.Covering
import ErdosStraus.CoveringData
import Mathlib.Tactic

namespace ErdosStraus

/-- Sublist of dataset certificates that use k = 7. -/
def certs_k7 : List Cert := certs.filter (fun c => c.k = 7)

theorem certs_k7_all_ok : List.Forall CertOK certs_k7 := by
  native_decide

theorem certs_k7_all_m_matches : List.Forall CertMMatches certs_k7 := by
  native_decide

theorem certs_k7_all_k_in_set : List.Forall CertKInSet certs_k7 := by
  native_decide

end ErdosStraus
