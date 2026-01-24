import ErdosStraus.Covering
import ErdosStraus.CoveringData
import Mathlib.Tactic

namespace ErdosStraus

/-- Sublist of dataset certificates that use k = 9. -/
def certs_k9 : List Cert := certs.filter (fun c => c.k = 9)

theorem certs_k9_all_ok : List.Forall CertOK certs_k9 := by
  native_decide

theorem certs_k9_all_m_matches : List.Forall CertMMatches certs_k9 := by
  native_decide

theorem certs_k9_all_k_in_set : List.Forall CertKInSet certs_k9 := by
  native_decide

end ErdosStraus
