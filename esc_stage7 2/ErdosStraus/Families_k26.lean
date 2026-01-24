import ErdosStraus.FamiliesK10Common
import ErdosStraus.QRCommon

namespace ErdosStraus

/-- Sufficient condition for `k = 26` (d=1 family). -/
def k26Sufficient (p : ℕ) : Prop := d1Sufficient 26 p ∨ QRSufficient 26 p

/-- `k = 26` sufficiency implies a solution for `p`. -/
theorem k26_gives_solution (p : ℕ) (hp : Nat.Prime p) (hMH : MordellHard840 p)
    (hsuff : k26Sufficient p) : HasSolution p := by
  rcases hsuff with hsuff | hsuff
  · exact d1Sufficient_gives_solution (k := 26) (p := p) hp hMH (by norm_num) hsuff
  · exact QRSufficient_gives_solution (k := 26) (p := p) hp hMH hsuff

end ErdosStraus
