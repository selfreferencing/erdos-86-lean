import ErdosStraus.FamiliesK10Common
import ErdosStraus.QRCommon

namespace ErdosStraus

/-- Sufficient condition for `k = 14` (d=1 family). -/
def k14Sufficient (p : ℕ) : Prop := d1Sufficient 14 p ∨ QRSufficient 14 p

/-- `k = 14` sufficiency implies a solution for `p`. -/
theorem k14_gives_solution (p : ℕ) (hp : Nat.Prime p) (hMH : MordellHard840 p)
    (hsuff : k14Sufficient p) : HasSolution p := by
  rcases hsuff with hsuff | hsuff
  · exact d1Sufficient_gives_solution (k := 14) (p := p) hp hMH (by norm_num) hsuff
  · exact QRSufficient_gives_solution (k := 14) (p := p) hp hMH hsuff

end ErdosStraus