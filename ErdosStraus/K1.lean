import ErdosStraus.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

namespace ErdosStraus

/-- A minimal quadratic-residue predicate for `ZMod m`.

For odd prime `m`, this coincides with the usual notion “there exists `t` with `t^2 ≡ a (mod m)`”.
-/
def IsQuadraticResidue (a m : ℕ) : Prop :=
  IsSquare ( (a : ZMod m) )

/-- The local Bradford divisor condition for `k=1`, where empirically `m = 7`.

We separate it from the prime `p` context: it is purely a statement about `x` and residue class modulo 7.
-/
def K1Local (x : ℕ) : Prop :=
  ∃ d : ℕ, d ∣ x^2 ∧ d ≤ x ∧ Nat.ModEq 7 (x + d) 0

/-- **Obstruction lemma (k=1):**

If the `m=7` congruence has *no* divisor solution for a given `x`, then every prime divisor of `x`
must be a quadratic residue mod 7.

This is the beginning of the subgroup/coset argument:
if `x` had a prime factor that is a non-residue mod 7, then divisors of `x^2` realize both cosets of
`(Z/7Z)ˣ` modulo squares, and one can select a divisor congruent to `-x`.

TODO: complete the subgroup argument (or an explicit finite computation in `ZMod 7`).
-/
theorem k1_obstruction_lemma (x : ℕ)
    (hfail : ¬ K1Local x) :
    ∀ q : ℕ, Nat.Prime q → q ∣ x → IsQuadraticResidue q 7 := by
  intro q hqprime hqx
  -- TODO: formalize the standard QR-coset argument in `ZMod 7`.
  -- A pragmatic route is:
  --   * use the finiteness of `ZMod 7` and `native_decide` to classify squares
  --   * show that if `q` is a non-residue, then there exists a divisor `d ∣ x^2` with `d ≡ -x (mod 7)`
  --     (contradicting `hfail`).
  sorry

/-- **QR-closure lemma:**

If every prime divisor of `x` is a quadratic residue mod 7, then every divisor of `x^2` is also a
quadratic residue mod 7.

This is a general “subgroup closure” statement; we state it only for the `m=7` case needed for `k=1`.
-/
theorem qr_closure_divisors_sq_mod7 (x d : ℕ)
    (hpr : ∀ q : ℕ, Nat.Prime q → q ∣ x → IsQuadraticResidue q 7)
    (hd : d ∣ x^2) :
    IsQuadraticResidue d 7 := by
  -- TODO: reduce to the prime factorization of `d` and use multiplicativity of `IsSquare`.
  -- This is the natural lemma used to finish the obstruction argument.
  sorry

end ErdosStraus
