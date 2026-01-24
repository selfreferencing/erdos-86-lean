import ErdosStraus.FamiliesK10Common

namespace ErdosStraus

/-!
# k=5 Family (m=23)

For k=5, we have m = 4×5 + 3 = 23.

QR mod 23 = {1,2,3,4,6,8,9,12,13,16,18}
NQR mod 23 = {5,7,10,11,14,15,17,19,20,21,22}

Bradford fails at k=5 when:
- All prime factors of x are in {primes ≡ QR mod 23}
- -x mod 23 is NQR

Our analysis showed k=5 covers ~67.5% of all Mordell-hard primes.
The remaining ~32.5% have QR obstruction and need higher k values.
-/

/-- Sufficient condition for k=5: d=1 works OR QR non-obstruction. -/
def k5Sufficient (p : ℕ) : Prop := kSufficientGeneric 5 p

/-- k=5 sufficiency implies HasSolution. -/
theorem k5_gives_solution (p : ℕ) (hp : Nat.Prime p) (hMH : MordellHard840 p)
    (hsuff : k5Sufficient p) : HasSolution p :=
  kSufficientGeneric_gives_solution 5 p hp hMH hsuff

/-! ## k=5 Specific Constants -/

/-- m-value for k=5. -/
def m5 : ℕ := mOfK 5  -- = 23

/-- Quadratic residues mod 23 (the squares). -/
def QR23 : Finset ℕ := {1, 2, 3, 4, 6, 8, 9, 12, 13, 16, 18}

/-- Quadratic non-residues mod 23. -/
def NQR23 : Finset ℕ := {5, 7, 10, 11, 14, 15, 17, 19, 20, 21, 22}

end ErdosStraus
