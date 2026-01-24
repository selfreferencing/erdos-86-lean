import ErdosStraus.Covering
import ErdosStraus.CoveringData
import Mathlib.Tactic

namespace ErdosStraus

/-- Sublist of dataset certificates that use k = 17. -/
def certs_k17 : List Cert := certs.filter (fun c => c.k = 17)

theorem certs_k17_all_ok : List.Forall CertOK certs_k17 := by
  native_decide

theorem certs_k17_all_m_matches : List.Forall CertMMatches certs_k17 := by
  native_decide

theorem certs_k17_all_k_in_set : List.Forall CertKInSet certs_k17 := by
  native_decide

end ErdosStraus
