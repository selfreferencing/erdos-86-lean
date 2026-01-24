import ErdosStraus.FamiliesK10Common
import ErdosStraus.QRCommon

namespace ErdosStraus

/-- Sufficient condition for `k = 11` (d=1 family). -/
def k11Sufficient (p : ℕ) : Prop := d1Sufficient 11 p ∨ QRSufficient 11 p

/-- `k = 11` sufficiency implies a solution for `p`. -/
theorem k11_gives_solution (p : ℕ) (hp : Nat.Prime p) (hMH : MordellHard840 p)
    (hsuff : k11Sufficient p) : HasSolution p := by
  rcases hsuff with hsuff | hsuff
  · exact d1Sufficient_gives_solution (k := 11) (p := p) hp hMH (by norm_num) hsuff
  · exact QRSufficient_gives_solution (k := 11) (p := p) hp hMH hsuff

end ErdosStraus
