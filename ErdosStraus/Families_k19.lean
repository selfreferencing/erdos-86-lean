import ErdosStraus.Covering
import ErdosStraus.CoveringData
import Mathlib.Tactic

namespace ErdosStraus

/-- Sublist of dataset certificates that use k = 19. -/
def certs_k19 : List Cert := certs.filter (fun c => c.k = 19)

theorem certs_k19_all_ok : List.Forall CertOK certs_k19 := by
  native_decide

theorem certs_k19_all_m_matches : List.Forall CertMMatches certs_k19 := by
  native_decide

theorem certs_k19_all_k_in_set : List.Forall CertKInSet certs_k19 := by
  native_decide

end ErdosStraus
