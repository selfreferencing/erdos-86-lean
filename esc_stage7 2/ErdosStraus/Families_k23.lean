import ErdosStraus.FamiliesK10Common
import ErdosStraus.QRCommon

namespace ErdosStraus

/-- Sufficient condition for `k = 23` (d=1 family). -/
def k23Sufficient (p : ℕ) : Prop := d1Sufficient 23 p ∨ QRSufficient 23 p

/-- `k = 23` sufficiency implies a solution for `p`. -/
theorem k23_gives_solution (p : ℕ) (hp : Nat.Prime p) (hMH : MordellHard840 p)
    (hsuff : k23Sufficient p) : HasSolution p := by
  rcases hsuff with hsuff | hsuff
  · exact d1Sufficient_gives_solution (k := 23) (p := p) hp hMH (by norm_num) hsuff
  · exact QRSufficient_gives_solution (k := 23) (p := p) hp hMH hsuff

end ErdosStraus
