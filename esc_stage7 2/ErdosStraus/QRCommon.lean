import Mathlib

import ErdosStraus.Basic
import ErdosStraus.FamiliesK10Common
import ErdosStraus.Covering
import ErdosStraus.Bradford

/-!
# Common quadratic-residue predicates for the Stage 8 cover

Stage 8 introduces the “QR obstruction” viewpoint.

For a fixed modulus `m` and integer `x`, a Type II witness divisor `d ∣ x^2` satisfying
`d ≡ -x (mod m)` can fail to exist for a *subgroup reason*:

* if every prime factor of `x` is a quadratic residue mod `m`, then every divisor of `x^2`
  is a quadratic residue mod `m` (closure of the QR subgroup);
* if, additionally, the target `-x (mod m)` is a quadratic **non**-residue, then no divisor
  of `x^2` can hit the required residue class.

This file packages these predicates in a uniform way so the covering lemma can be stated
cleanly.

⚠️  This is *infrastructure*: it does **not** prove the unbounded cover.
The key missing step is still `ten_k_cover_complete`.
-/

namespace ErdosStraus

/-!
## Small utilities
-/

/-- Canonical `(-a) mod m` representative as a natural. -/
def negMod (m a : ℕ) : ℕ := (m - (a % m)) % m

/-!
## Quadratic residuosity predicates

We deliberately phrase “quadratic residue mod `m`” using `ZMod m` and `IsSquare`.

This is the right notion for prime moduli (Legendre symbol) and is also a perfectly
reasonable *sufficient* notion for composite moduli.

Stage 8's obstruction pattern is formulated with these predicates.
-/

/-- `a` is a quadratic residue modulo `m` (in the sense of being a square in `ZMod m`). -/
def IsQR (m a : ℕ) : Prop :=
  IsSquare ((a : ZMod m))

/-- `a` is a quadratic non-residue modulo `m`. -/
def IsNQR (m a : ℕ) : Prop :=
  ¬ IsQR m a

/-- Every prime factor of `x` is a quadratic residue modulo `m`. -/
def PrimeFactorQR (m x : ℕ) : Prop :=
  ∀ q : ℕ, Nat.Prime q → q ∣ x → IsQR m q

/-- The Bradford Type II “target” residue class is a quadratic non-residue. -/
def TargetNQR (m x : ℕ) : Prop :=
  IsNQR m (negMod m x)

/-!
## Stage 8 “QR sufficient” predicate

The empirical finding is that the 10 k-set succeeds on the full dataset once we add
“QR-based sufficiency” alongside the `d=1` families.

For now we expose only the *minimal* logical interface used in Stage 8:

* `¬ QRSufficient k p` implies the QR obstruction (all prime factors are QR and the target is NQR).

This is enough to reduce the global cover theorem to ruling out the simultaneous obstruction
for all ten k.

In the final proof, `QRSufficient` should be strengthened to an *explicit witness-producing*
predicate.
-/

/-- The Stage 8 QR-based sufficient condition at shift `k`.

At the interface level we only require that failure implies the obstruction.

In this scaffold we take the *negation of the obstruction* itself.

This makes the logical reduction explicit:
`¬QRSufficient k p ↔ (PrimeFactorQR m x ∧ TargetNQR m x)`.

Note: this definition is intentionally conservative; proving that it actually implies a
Bradford witness is a separate lemma (expected from Stage 6A / Stage 8 algebra).
-/
def QRSufficient (k p : ℕ) : Prop :=
  let m := mOfK k
  let x := xOfK p k
  ¬ (PrimeFactorQR m x ∧ TargetNQR m x)

lemma not_QRSufficient_iff_obstruction (k p : ℕ) :
    (¬ QRSufficient k p) ↔
      let m := mOfK k
      let x := xOfK p k
      (PrimeFactorQR m x ∧ TargetNQR m x) := by
  simp [QRSufficient]

/-!
## Bridge: `QRSufficient` → `HasSolution`

Stage 8 needs a single *bridge lemma* turning the QR-based sufficient predicate into an
actual Erdős–Straus certificate.

Conceptually:

1. From `QRSufficient k p` we obtain (or construct) a divisor `d | x^2` such that
   `d ≡ -x (mod m)` (a Type II witness).
2. Apply the already-proven Bradford validity lemma `bradford_typeII_valid`.

The difficult part is (1): converting “non-obstruction” into an explicit witness.
This is precisely where the number-theoretic argument (Stage 8) lives.

We keep it as a single isolated `sorry` so that all k-family files can share it without
duplicating work.
-/

theorem QRSufficient_gives_solution
    (k p : ℕ) (hp : Nat.Prime p) (hMH : MordellHard840 p)
    (hsuff : QRSufficient k p) : HasSolution p := by
  -- TODO(Stage 8): turn `QRSufficient` into an explicit `TypeIIWitness` and apply Bradford.
  -- Expected shape:
  --   let x := xOfK p k
  --   obtain ⟨d, hw : TypeIIWitness p x d⟩ := ...
  --   have side conditions (m>0, x<p, coprime) from Stage 6A
  --   exact ⟨x, bradfordY p x d, bradfordZ p x d, ...⟩
  sorry

end ErdosStraus
