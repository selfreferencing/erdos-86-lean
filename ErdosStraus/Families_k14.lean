import ErdosStraus.Covering
import ErdosStraus.CoveringData
import Mathlib.Tactic

namespace ErdosStraus

/-- Sublist of dataset certificates that use k = 14. -/
def certs_k14 : List Cert := certs.filter (fun c => c.k = 14)

theorem certs_k14_all_ok : List.Forall CertOK certs_k14 := by
  native_decide

theorem certs_k14_all_m_matches : List.Forall CertMMatches certs_k14 := by
  native_decide

theorem certs_k14_all_k_in_set : List.Forall CertKInSet certs_k14 := by
  native_decide

end ErdosStraus
