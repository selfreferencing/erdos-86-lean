import ErdosStraus.FamiliesK10Common
import ErdosStraus.QRCommon

namespace ErdosStraus

/-- Sufficient condition for `k = 9` (d=1 family). -/
def k9Sufficient (p : ℕ) : Prop := d1Sufficient 9 p ∨ QRSufficient 9 p

/-- `k = 9` sufficiency implies a solution for `p`. -/
theorem k9_gives_solution (p : ℕ) (hp : Nat.Prime p) (hMH : MordellHard840 p)
    (hsuff : k9Sufficient p) : HasSolution p := by
  rcases hsuff with hsuff | hsuff
  · exact d1Sufficient_gives_solution (k := 9) (p := p) hp hMH (by norm_num) hsuff
  · exact QRSufficient_gives_solution (k := 9) (p := p) hp hMH hsuff

end ErdosStraus
