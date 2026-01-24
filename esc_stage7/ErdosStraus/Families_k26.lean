import ErdosStraus.FamiliesK10Common

namespace ErdosStraus

/-!
# k=26 Family (m=107)

For k=26, we have m = 4×26 + 3 = 107.
-/

/-- Sufficient condition for k=26: d=1 works OR QR non-obstruction. -/
def k26Sufficient (p : ℕ) : Prop := kSufficientGeneric 26 p

/-- k=26 sufficiency implies HasSolution. -/
theorem k26_gives_solution (p : ℕ) (hp : Nat.Prime p) (hMH : MordellHard840 p)
    (hsuff : k26Sufficient p) : HasSolution p :=
  kSufficientGeneric_gives_solution 26 p hp hMH hsuff

/-- m-value for k=26. -/
def m26 : ℕ := mOfK 26  -- = 107

end ErdosStraus
