import Mathlib

import ErdosStraus.Basic
import ErdosStraus.Bradford
import ErdosStraus.Covering

/-!
# Stage 7 helper lemmas for the 10-k covering system

This file provides *generic* interfaces for k-families used in Stage 7.

## Key Discovery: QR Obstruction Pattern

Analysis of 20,513 certificates revealed that Bradford Type II fails when:
1. All prime factors of x are quadratic residues mod m
2. -x mod m is a quadratic NON-residue

This means Bradford SUCCEEDS when EITHER:
- x has a prime factor that is NQR mod m (breaks the QR closure), OR
- -x mod m is a QR (target residue is reachable)

We implement both d=constant families AND QR-based sufficiency conditions.
-/

namespace ErdosStraus

/-! ## Basic Bradford Parameters -/

/-- Bradford's `m` parameter for a fixed shift `k` when `x = ⌈p/4⌉ + k`.
For Mordell-hard primes: `m = 4k + 3`.
-/
def mOfK (k : ℕ) : ℕ := 4 * k + 3

/-- The Bradford `x` candidate for a fixed `k`.
`x = (p + mOfK k) / 4 = ⌈p/4⌉ + k` for `p ≡ 1 (mod 4)`.
-/
def xOfK (p k : ℕ) : ℕ := (p + mOfK k) / 4

/-! ## Quadratic Residue Definitions -/

/-- Quadratic residues modulo m (for m prime, this is the set of squares). -/
def IsQR (m a : ℕ) : Prop := ∃ b : ℕ, b * b % m = a % m

/-- Quadratic non-residue modulo m. -/
def IsNQR (m a : ℕ) : Prop := a % m ≠ 0 ∧ ¬IsQR m a

/-- All prime factors of n are QR mod m. -/
def AllPrimeFactorsQR (m n : ℕ) : Prop :=
  ∀ q : ℕ, Nat.Prime q → q ∣ n → IsQR m q

/-- At least one prime factor of n is NQR mod m. -/
def HasNQRPrimeFactor (m n : ℕ) : Prop :=
  ∃ q : ℕ, Nat.Prime q ∧ q ∣ n ∧ IsNQR m q

/-! ## QR-Based Sufficiency Conditions -/

/-- QR non-obstruction: k works if x has an NQR prime factor mod m.

When x has an NQR prime factor q, the divisor residue set of x² includes
NQR classes, allowing us to hit any target residue -x mod m.
-/
def QRNonObstruction (k p : ℕ) : Prop :=
  HasNQRPrimeFactor (mOfK k) (xOfK p k)

/-- Alternative QR non-obstruction: -x is itself a QR mod m.

When -x is a QR, even if all prime factors of x are QR, we can still
find a divisor d ≡ -x (mod m) in the QR subgroup.
-/
def TargetIsQR (k p : ℕ) : Prop :=
  let x := xOfK p k
  let m := mOfK k
  IsQR m ((m - x % m) % m)

/-- Combined QR-based sufficiency: either condition breaks the obstruction. -/
def QRSufficient (k p : ℕ) : Prop :=
  QRNonObstruction k p ∨ TargetIsQR k p

/-! ## Constant-d Family Conditions -/

/-- The standard "d=1" parametric family (Stage 4/5):
If `p ≡ 12k+5 (mod 16k+12)`, then `d=1` is a Type II Bradford witness.
-/
def d1Sufficient (k p : ℕ) : Prop := p % (16 * k + 12) = (12 * k + 5)

/-- Generic "d=constant" family: p satisfies specific congruence for witness d.

For a fixed d to work as Bradford witness, we need:
- d | x² (satisfied if d | x or specific power conditions)
- d ≤ x
- d ≡ -x (mod m)

The congruence condition on p that makes d ≡ -x (mod m) depends on (k, d).
-/
def dConstantSufficient (k d : ℕ) (residue modulus : ℕ) (p : ℕ) : Prop :=
  p % modulus = residue

/-- d=2 family: works when x is even and 2 ≡ -x (mod m). -/
def d2Sufficient (k p : ℕ) : Prop :=
  let m := mOfK k
  let x := xOfK p k
  2 ∣ x ∧ Nat.ModEq m (2 + x) 0

/-- d=4 family: works when 4 | x² (i.e., 2 | x) and 4 ≡ -x (mod m). -/
def d4Sufficient (k p : ℕ) : Prop :=
  let m := mOfK k
  let x := xOfK p k
  2 ∣ x ∧ Nat.ModEq m (4 + x) 0

/-- d=8 family: works when 4 | x (so 8 | x²) and 8 ≡ -x (mod m).
Key pattern for k=5 failures.
-/
def d8Sufficient (k p : ℕ) : Prop :=
  let m := mOfK k
  let x := xOfK p k
  4 ∣ x ∧ Nat.ModEq m (8 + x) 0

/-- d=16 family: works when 4 | x and 16 ≡ -x (mod m).
Another key pattern for k=5 failures.
-/
def d16Sufficient (k p : ℕ) : Prop :=
  let m := mOfK k
  let x := xOfK p k
  4 ∣ x ∧ Nat.ModEq m (16 + x) 0

/-! ## Witness Lemmas (placeholders) -/

/-- Core witness lemma for the d=1 family. -/
theorem d1Sufficient_witness
    (k p : ℕ) (hp : Nat.Prime p) (hMH : MordellHard840 p)
    (hsuff : d1Sufficient k p) :
    TypeIIWitness p (xOfK p k) 1 := by
  sorry

/-- QR non-obstruction implies existence of Bradford witness. -/
theorem QRSufficient_witness
    (k p : ℕ) (hp : Nat.Prime p) (hMH : MordellHard840 p)
    (hsuff : QRSufficient k p) :
    ∃ d : ℕ, TypeIIWitness p (xOfK p k) d := by
  -- When x has an NQR prime factor q, we can construct d from powers of q
  -- to hit any residue class mod m.
  -- When -x is QR, d=1 or d from QR subgroup works.
  sorry

/-! ## Bridge Lemmas: Sufficiency → HasSolution -/

/-- Generic bridge: any TypeIIWitness implies HasSolution via Bradford. -/
theorem typeIIWitness_gives_solution
    (p x d : ℕ) (hp : Nat.Prime p) (hMH : MordellHard840 p)
    (hw : TypeIIWitness p x d) (hmpos : m p x > 0) (hxlt : x < p)
    (hcop : Nat.Coprime x (m p x)) (hxpos : x > 0) : HasSolution p := by
  have hpos_and_es := bradford_typeII_valid (p := p) (x := x) (d := d) hp hmpos hxlt hw hcop
  rcases hpos_and_es with ⟨hypos, hzpos, hES⟩
  exact ⟨x, bradfordY p x d, bradfordZ p x d, hxpos, hypos, hzpos, hES⟩

/-- d=1 sufficiency implies HasSolution. -/
theorem d1Sufficient_gives_solution
    (k p : ℕ) (hp : Nat.Prime p) (hMH : MordellHard840 p)
    (hsuff : d1Sufficient k p) : HasSolution p := by
  have hw := d1Sufficient_witness k p hp hMH hsuff
  have hmpos : m p (xOfK p k) > 0 := by sorry
  have hxlt : xOfK p k < p := by sorry
  have hcop : Nat.Coprime (xOfK p k) (m p (xOfK p k)) := by sorry
  have hxpos : xOfK p k > 0 := by sorry
  exact typeIIWitness_gives_solution p (xOfK p k) 1 hp hMH hw hmpos hxlt hcop hxpos

/-- QR sufficiency implies HasSolution. -/
theorem QRSufficient_gives_solution
    (k p : ℕ) (hp : Nat.Prime p) (hMH : MordellHard840 p)
    (hsuff : QRSufficient k p) : HasSolution p := by
  rcases QRSufficient_witness k p hp hMH hsuff with ⟨d, hw⟩
  have hmpos : m p (xOfK p k) > 0 := by sorry
  have hxlt : xOfK p k < p := by sorry
  have hcop : Nat.Coprime (xOfK p k) (m p (xOfK p k)) := by sorry
  have hxpos : xOfK p k > 0 := by sorry
  exact typeIIWitness_gives_solution p (xOfK p k) d hp hMH hw hmpos hxlt hcop hxpos

/-! ## Combined k-Sufficiency Predicate -/

/-- Combined sufficiency for k: either d=1 works OR QR non-obstruction holds.

This is the expanded predicate that should cover most/all Mordell-hard primes.
Each Families_k*.lean file defines kXSufficient using this pattern.
-/
def kSufficientGeneric (k p : ℕ) : Prop :=
  d1Sufficient k p ∨ QRSufficient k p

/-- Combined sufficiency implies HasSolution. -/
theorem kSufficientGeneric_gives_solution
    (k p : ℕ) (hp : Nat.Prime p) (hMH : MordellHard840 p)
    (hsuff : kSufficientGeneric k p) : HasSolution p := by
  rcases hsuff with hd1 | hqr
  · exact d1Sufficient_gives_solution k p hp hMH hd1
  · exact QRSufficient_gives_solution k p hp hMH hqr

end ErdosStraus
