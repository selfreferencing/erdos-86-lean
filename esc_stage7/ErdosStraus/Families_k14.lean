import ErdosStraus.FamiliesK10Common

namespace ErdosStraus

/-!
# k=14 Family (m=59)

For k=14, we have m = 4×14 + 3 = 59.
-/

/-- Sufficient condition for k=14: d=1 works OR QR non-obstruction. -/
def k14Sufficient (p : ℕ) : Prop := kSufficientGeneric 14 p

/-- k=14 sufficiency implies HasSolution. -/
theorem k14_gives_solution (p : ℕ) (hp : Nat.Prime p) (hMH : MordellHard840 p)
    (hsuff : k14Sufficient p) : HasSolution p :=
  kSufficientGeneric_gives_solution 14 p hp hMH hsuff

/-- m-value for k=14. -/
def m14 : ℕ := mOfK 14  -- = 59

end ErdosStraus
