import ErdosStraus.FamiliesK10Common

namespace ErdosStraus

/-!
# k=11 Family (m=47)

For k=11, we have m = 4×11 + 3 = 47.
-/

/-- Sufficient condition for k=11: d=1 works OR QR non-obstruction. -/
def k11Sufficient (p : ℕ) : Prop := kSufficientGeneric 11 p

/-- k=11 sufficiency implies HasSolution. -/
theorem k11_gives_solution (p : ℕ) (hp : Nat.Prime p) (hMH : MordellHard840 p)
    (hsuff : k11Sufficient p) : HasSolution p :=
  kSufficientGeneric_gives_solution 11 p hp hMH hsuff

/-- m-value for k=11. -/
def m11 : ℕ := mOfK 11  -- = 47

end ErdosStraus
