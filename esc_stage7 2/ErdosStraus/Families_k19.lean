import ErdosStraus.FamiliesK10Common
import ErdosStraus.QRCommon

namespace ErdosStraus

/-- Sufficient condition for `k = 19` (d=1 family). -/
def k19Sufficient (p : ℕ) : Prop := d1Sufficient 19 p ∨ QRSufficient 19 p

/-- `k = 19` sufficiency implies a solution for `p`. -/
theorem k19_gives_solution (p : ℕ) (hp : Nat.Prime p) (hMH : MordellHard840 p)
    (hsuff : k19Sufficient p) : HasSolution p := by
  rcases hsuff with hsuff | hsuff
  · exact d1Sufficient_gives_solution (k := 19) (p := p) hp hMH (by norm_num) hsuff
  · exact QRSufficient_gives_solution (k := 19) (p := p) hp hMH hsuff

end ErdosStraus
