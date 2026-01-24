import ErdosStraus.FamiliesK10Common

namespace ErdosStraus

/-!
# k=7 Family (m=31)

For k=7, we have m = 4×7 + 3 = 31.
-/

/-- Sufficient condition for k=7: d=1 works OR QR non-obstruction. -/
def k7Sufficient (p : ℕ) : Prop := kSufficientGeneric 7 p

/-- k=7 sufficiency implies HasSolution. -/
theorem k7_gives_solution (p : ℕ) (hp : Nat.Prime p) (hMH : MordellHard840 p)
    (hsuff : k7Sufficient p) : HasSolution p :=
  kSufficientGeneric_gives_solution 7 p hp hMH hsuff

/-- m-value for k=7. -/
def m7 : ℕ := mOfK 7  -- = 31

end ErdosStraus
