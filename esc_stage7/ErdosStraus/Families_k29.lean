import ErdosStraus.FamiliesK10Common

namespace ErdosStraus

/-!
# k=29 Family (m=119)

For k=29, we have m = 4×29 + 3 = 119.
-/

/-- Sufficient condition for k=29: d=1 works OR QR non-obstruction. -/
def k29Sufficient (p : ℕ) : Prop := kSufficientGeneric 29 p

/-- k=29 sufficiency implies HasSolution. -/
theorem k29_gives_solution (p : ℕ) (hp : Nat.Prime p) (hMH : MordellHard840 p)
    (hsuff : k29Sufficient p) : HasSolution p :=
  kSufficientGeneric_gives_solution 29 p hp hMH hsuff

/-- m-value for k=29. -/
def m29 : ℕ := mOfK 29  -- = 119

end ErdosStraus
