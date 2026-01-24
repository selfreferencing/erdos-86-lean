import ErdosStraus.Covering
import ErdosStraus.CoveringData
import Mathlib.Tactic

namespace ErdosStraus

/-- Sublist of dataset certificates that use k = 26. -/
def certs_k26 : List Cert := certs.filter (fun c => c.k = 26)

theorem certs_k26_all_ok : List.Forall CertOK certs_k26 := by
  native_decide

theorem certs_k26_all_m_matches : List.Forall CertMMatches certs_k26 := by
  native_decide

theorem certs_k26_all_k_in_set : List.Forall CertKInSet certs_k26 := by
  native_decide

end ErdosStraus
