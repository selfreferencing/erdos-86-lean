import ErdosStraus.FamiliesK10Common

namespace ErdosStraus

/-!
# k=19 Family (m=79)

For k=19, we have m = 4×19 + 3 = 79.
-/

/-- Sufficient condition for k=19: d=1 works OR QR non-obstruction. -/
def k19Sufficient (p : ℕ) : Prop := kSufficientGeneric 19 p

/-- k=19 sufficiency implies HasSolution. -/
theorem k19_gives_solution (p : ℕ) (hp : Nat.Prime p) (hMH : MordellHard840 p)
    (hsuff : k19Sufficient p) : HasSolution p :=
  kSufficientGeneric_gives_solution 19 p hp hMH hsuff

/-- m-value for k=19. -/
def m19 : ℕ := mOfK 19  -- = 79

end ErdosStraus
