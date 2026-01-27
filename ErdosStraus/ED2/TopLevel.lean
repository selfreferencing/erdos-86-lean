/-
  ErdosStraus/ED2/TopLevel.lean

  Top-level case split for the ED2 Dyachenko formalization:
  - Small primes (p < 10,000,001): closed by certificates + native_decide
  - Large primes (p ≥ 10,000,001): closed by exists_good_A_and_divisor

  ## Sorry status
  - `ed2_params_small`: needs certificate integration (Python Parts 1-3)
  - `ed2_dyachenko_params_exist`: needs exists_good_A_and_divisor to be proved (GPT)

  Both depend on `ed2_from_good_divisor` from ExistsGoodDivisor.lean.

  Source: GPT Part 4 (January 2026), adapted to project structure
-/

import Mathlib.Tactic
import ErdosStraus.ED2.ExistsGoodDivisor

namespace ED2

/-- Explicit bound separating certificate-based and theoretical arguments. -/
def ed2TopLevelBound : ℕ := 10000001

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
    To be closed by integrating Type2 certificates via native_decide.
    Use the Python scripts (Parts 1-3) to generate the certificate data. -/
theorem ed2_small_params (p : ℕ) (hp : Nat.Prime p) (hp4 : p % 4 = 1)
    (hp_small : p < ed2TopLevelBound) :
    ∃ α d' b' c' : ℕ,
      0 < α ∧ 0 < d' ∧ 0 < b' ∧ 0 < c' ∧
      p < 4 * α * b' * c' ∧
      b' + c' = (4 * α * b' * c' - p) * d' := by
  -- To be closed by:
  -- 1. Generate certificates using python/ed2_witness_to_lean.py (Part 3)
  -- 2. Store in Type2CertData.lean / Type2CertDataExtended.lean
  -- 3. Verify with native_decide (strategy from Part 3)
  sorry

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
