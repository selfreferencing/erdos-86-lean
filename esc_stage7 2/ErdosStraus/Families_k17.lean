import ErdosStraus.FamiliesK10Common
import ErdosStraus.QRCommon

namespace ErdosStraus

/-- Sufficient condition for `k = 17` (d=1 family). -/
def k17Sufficient (p : ℕ) : Prop := d1Sufficient 17 p ∨ QRSufficient 17 p

/-- `k = 17` sufficiency implies a solution for `p`. -/
theorem k17_gives_solution (p : ℕ) (hp : Nat.Prime p) (hMH : MordellHard840 p)
    (hsuff : k17Sufficient p) : HasSolution p := by
  rcases hsuff with hsuff | hsuff
  · exact d1Sufficient_gives_solution (k := 17) (p := p) hp hMH (by norm_num) hsuff
  · exact QRSufficient_gives_solution (k := 17) (p := p) hp hMH hsuff

end ErdosStraus
