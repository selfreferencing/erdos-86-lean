import ErdosStraus.FamiliesK10Common

namespace ErdosStraus

/-!
# k=17 Family (m=71)

For k=17, we have m = 4×17 + 3 = 71.
-/

/-- Sufficient condition for k=17: d=1 works OR QR non-obstruction. -/
def k17Sufficient (p : ℕ) : Prop := kSufficientGeneric 17 p

/-- k=17 sufficiency implies HasSolution. -/
theorem k17_gives_solution (p : ℕ) (hp : Nat.Prime p) (hMH : MordellHard840 p)
    (hsuff : k17Sufficient p) : HasSolution p :=
  kSufficientGeneric_gives_solution 17 p hp hMH hsuff

/-- m-value for k=17. -/
def m17 : ℕ := mOfK 17  -- = 71

end ErdosStraus
