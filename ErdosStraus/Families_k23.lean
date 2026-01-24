import ErdosStraus.Covering
import ErdosStraus.CoveringData
import Mathlib.Tactic

namespace ErdosStraus

/-- Sublist of dataset certificates that use k = 23. -/
def certs_k23 : List Cert := certs.filter (fun c => c.k = 23)

theorem certs_k23_all_ok : List.Forall CertOK certs_k23 := by
  native_decide

theorem certs_k23_all_m_matches : List.Forall CertMMatches certs_k23 := by
  native_decide

theorem certs_k23_all_k_in_set : List.Forall CertKInSet certs_k23 := by
  native_decide

end ErdosStraus
