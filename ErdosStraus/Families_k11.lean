import ErdosStraus.Covering
import ErdosStraus.CoveringData
import Mathlib.Tactic

namespace ErdosStraus

/-- Sublist of dataset certificates that use k = 11. -/
def certs_k11 : List Cert := certs.filter (fun c => c.k = 11)

theorem certs_k11_all_ok : List.Forall CertOK certs_k11 := by
  native_decide

theorem certs_k11_all_m_matches : List.Forall CertMMatches certs_k11 := by
  native_decide

theorem certs_k11_all_k_in_set : List.Forall CertKInSet certs_k11 := by
  native_decide

end ErdosStraus
