import ErdosStraus.FamiliesK10Common
import ErdosStraus.QRCommon

namespace ErdosStraus

/-- Sufficient condition for `k = 7` (d=1 family). -/
def k7Sufficient (p : ℕ) : Prop := d1Sufficient 7 p ∨ QRSufficient 7 p

/-- `k = 7` sufficiency implies a solution for `p`. -/
theorem k7_gives_solution (p : ℕ) (hp : Nat.Prime p) (hMH : MordellHard840 p)
    (hsuff : k7Sufficient p) : HasSolution p := by
  rcases hsuff with hsuff | hsuff
  · exact d1Sufficient_gives_solution (k := 7) (p := p) hp hMH (by norm_num) hsuff
  · exact QRSufficient_gives_solution (k := 7) (p := p) hp hMH hsuff

end ErdosStraus
