/-
  ErdosStraus/ED2/TopLevel.lean

  Top-level case split for the ED2 Dyachenko formalization:
  - Small primes (p < 1,000,001): closed by Certificate.lean (native_decide)
  - Large primes (p ≥ 1,000,001): closed by ed2_dyachenko_params_exist (Phase3)

  ## Sorry status
  - `ed2_dyachenko_params_exist`: needs full lattice argument (Phase3.lean)

  Source: GPT Part 4 (January 2026), adapted to project structure
-/

import Mathlib.Tactic
import ErdosStraus.ED2.ExistsGoodDivisor
import ErdosStraus.ED2.Certificate

namespace ED2

/-- Explicit bound separating certificate-based and theoretical arguments.
    Must equal certBound from Certificate.lean (both = 1000001). -/
def ed2TopLevelBound : ℕ := 1000001

/-- For large primes p ≡ 1 (mod 4), ED2 parameters exist.
    Uses the theoretical argument from ExistsGoodDivisor.lean.
    The sorry ultimately reduces to `exists_good_A_and_divisor`. -/
theorem ed2_large_params (p : ℕ) (hp : Nat.Prime p) (hp4 : p % 4 = 1)
    (hp_large : p ≥ ed2TopLevelBound) :
    ∃ α d' b' c' : ℕ,
      0 < α ∧ 0 < d' ∧ 0 < b' ∧ 0 < c' ∧
      p < 4 * α * b' * c' ∧
      b' + c' = (4 * α * b' * c' - p) * d' := by
  -- For now, delegate to the sorry'd existence in Phase3.lean.
  -- When exists_good_A_and_divisor is proved, this can instead go through
  -- ed2_from_good_divisor → divisor_gives_type2 → ed2_of_good_divisor,
  -- but that route produces (offset, b, c) not (α, d', b', c').
  --
  -- To fill THIS signature, either:
  -- (a) Prove exists_good_A_and_divisor and convert (A,d) → (α,d',b',c'), or
  -- (b) Fill ed2_dyachenko_params_exist in Phase3.lean directly.
  exact ed2_dyachenko_params_exist p hp hp4 (by omega)

/-- For small primes p ≡ 1 (mod 4) below the bound, ED2 parameters exist.
    Proved by the certificate-based native_decide computation in Certificate.lean. -/
theorem ed2_small_params (p : ℕ) (hp : Nat.Prime p) (hp4 : p % 4 = 1)
    (hp_small : p < ed2TopLevelBound) :
    ∃ α d' b' c' : ℕ,
      0 < α ∧ 0 < d' ∧ 0 < b' ∧ 0 < c' ∧
      p < 4 * α * b' * c' ∧
      b' + c' = (4 * α * b' * c' - p) * d' :=
  ed2_params_below_certBound hp hp4 hp_small

/-- Main theorem: for ALL primes p ≡ 1 (mod 4), ED2 parameters exist.
    Splits into small (certificates) and large (theoretical) cases. -/
theorem ed2_params_all (p : ℕ) (hp : Nat.Prime p) (hp4 : p % 4 = 1) :
    ∃ α d' b' c' : ℕ,
      0 < α ∧ 0 < d' ∧ 0 < b' ∧ 0 < c' ∧
      p < 4 * α * b' * c' ∧
      b' + c' = (4 * α * b' * c' - p) * d' := by
  by_cases h : p < ed2TopLevelBound
  · exact ed2_small_params p hp hp4 h
  · exact ed2_large_params p hp hp4 (by omega)

end ED2
