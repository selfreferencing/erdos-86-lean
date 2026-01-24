import ErdosStraus.FamiliesK10Common
import ErdosStraus.QRCommon

namespace ErdosStraus

/-- Sufficient condition for `k = 5`.

Stage 8: `d=1` family OR the QR-based sufficient predicate.
-/
def k5Sufficient (p : ℕ) : Prop := d1Sufficient 5 p ∨ QRSufficient 5 p

/-- `k = 5` sufficiency implies a solution for `p`. -/
theorem k5_gives_solution (p : ℕ) (hp : Nat.Prime p) (hMH : MordellHard840 p)
    (hsuff : k5Sufficient p) : HasSolution p := by
  rcases hsuff with hsuff | hsuff
  · -- `d=1` parametric family
    exact d1Sufficient_gives_solution (k := 5) (p := p) hp hMH (by norm_num) hsuff
  · -- QR-based family (Stage 8)
    exact QRSufficient_gives_solution (k := 5) (p := p) hp hMH hsuff

end ErdosStraus
