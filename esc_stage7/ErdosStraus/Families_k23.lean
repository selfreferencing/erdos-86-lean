import ErdosStraus.FamiliesK10Common

namespace ErdosStraus

/-!
# k=23 Family (m=95)

For k=23, we have m = 4×23 + 3 = 95.
-/

/-- Sufficient condition for k=23: d=1 works OR QR non-obstruction. -/
def k23Sufficient (p : ℕ) : Prop := kSufficientGeneric 23 p

/-- k=23 sufficiency implies HasSolution. -/
theorem k23_gives_solution (p : ℕ) (hp : Nat.Prime p) (hMH : MordellHard840 p)
    (hsuff : k23Sufficient p) : HasSolution p :=
  kSufficientGeneric_gives_solution 23 p hp hMH hsuff

/-- m-value for k=23. -/
def m23 : ℕ := mOfK 23  -- = 95

end ErdosStraus
