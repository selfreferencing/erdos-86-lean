import ErdosStraus.FamiliesK10Common
import ErdosStraus.QRCommon

namespace ErdosStraus

/-- Sufficient condition for `k = 29` (d=1 family). -/
def k29Sufficient (p : ℕ) : Prop := d1Sufficient 29 p ∨ QRSufficient 29 p

/-- `k = 29` sufficiency implies a solution for `p`. -/
theorem k29_gives_solution (p : ℕ) (hp : Nat.Prime p) (hMH : MordellHard840 p)
    (hsuff : k29Sufficient p) : HasSolution p := by
  rcases hsuff with hsuff | hsuff
  · exact d1Sufficient_gives_solution (k := 29) (p := p) hp hMH (by norm_num) hsuff
  · exact QRSufficient_gives_solution (k := 29) (p := p) hp hMH hsuff

end ErdosStraus
