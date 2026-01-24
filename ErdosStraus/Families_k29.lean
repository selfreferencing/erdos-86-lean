import ErdosStraus.Covering
import ErdosStraus.CoveringData
import Mathlib.Tactic

namespace ErdosStraus

/-- Sublist of dataset certificates that use k = 29. -/
def certs_k29 : List Cert := certs.filter (fun c => c.k = 29)

theorem certs_k29_all_ok : List.Forall CertOK certs_k29 := by
  native_decide

theorem certs_k29_all_m_matches : List.Forall CertMMatches certs_k29 := by
  native_decide

theorem certs_k29_all_k_in_set : List.Forall CertKInSet certs_k29 := by
  native_decide

end ErdosStraus
