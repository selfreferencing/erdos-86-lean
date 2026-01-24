/-
  CoveringRestructured.lean

  Restructured covering theorem based on GPT findings:
  - K10 alone fails for ~18 Mordell-hard primes under Type II
  - k ∈ {0, 1, 2} handles 86.7% of Mordell-hard primes
  - K10 handles the remaining "Hard10" primes

  Structure:
  1. Define when small k (0, 1, 2) provides a Type II witness
  2. Define Hard10 = MordellHard primes not covered by small k
  3. Prove K10 covers all Hard10 primes
  4. Combine into main ESC theorem
-/

import ErdosStraus.Basic
import ErdosStraus.FamiliesK10Common
import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic

namespace ErdosStraus

open scoped BigOperators

/-! ## Small k Coverage -/

/-- k=0 gives m=3. Type II witness exists when the congruence condition holds. -/
def TypeII_k0 (p : ℕ) : Prop :=
  ∃ d : ℕ, d ∣ (x0 p)^2 ∧ d ≤ x0 p ∧ Nat.ModEq 3 (x0 p + d) 0

/-- k=1 gives m=7. Type II witness exists when the congruence condition holds. -/
def TypeII_k1 (p : ℕ) : Prop :=
  ∃ d : ℕ, d ∣ (xK p 1)^2 ∧ d ≤ xK p 1 ∧ Nat.ModEq 7 (xK p 1 + d) 0

/-- k=2 gives m=11. Type II witness exists when the congruence condition holds. -/
def TypeII_k2 (p : ℕ) : Prop :=
  ∃ d : ℕ, d ∣ (xK p 2)^2 ∧ d ≤ xK p 2 ∧ Nat.ModEq 11 (xK p 2 + d) 0

/-! ## Hard10 Definition -/

/-- Hard10 primes are Mordell-hard primes NOT covered by k ∈ {0, 1, 2}.
    These are the primes that K10 must handle. -/
def Hard10 (p : ℕ) : Prop :=
  MordellHard p ∧ ¬TypeII_k0 p ∧ ¬TypeII_k1 p ∧ ¬TypeII_k2 p

/-! ## K10 Coverage for Hard10 -/

/-- The set K10 = {5, 7, 9, 11, 14, 17, 19, 23, 26, 29} -/
def K10 : Finset ℕ := {5, 7, 9, 11, 14, 17, 19, 23, 26, 29}

/-- Main theorem: K10 covers all Hard10 primes.

    This is the corrected version of ten_k_cover_exists.
    The original claimed K10 covers all Mordell-hard primes, which is false.
    This version correctly states K10 covers the residual primes after small-k handling.

    Proof strategy (to be filled):
    - For p large enough, use the QR/Legendre witness argument
    - For p small, use certificate verification
-/
theorem k10_covers_hard10 (p : ℕ) (hp : Nat.Prime p) (h10 : Hard10 p) :
    ∃ k ∈ K10, QRSufficient k p := by
  sorry

/-! ## Small k Lemmas -/

/-- Characterization of when k=0 (m=3) works.
    d=1 works iff x₀ ≡ 2 (mod 3), i.e., p ≡ 5 (mod 12). -/
theorem k0_d1_criterion (p : ℕ) (hp : Nat.Prime p) (hMH : MordellHard p) :
    (x0 p) % 3 = 2 → TypeII_k0 p := by
  sorry

/-- Characterization of when k=1 (m=7) works.
    d=1 works iff x₁ ≡ 6 (mod 7), i.e., p ≡ 17 (mod 28). -/
theorem k1_d1_criterion (p : ℕ) (hp : Nat.Prime p) (hMH : MordellHard p) :
    (xK p 1) % 7 = 6 → TypeII_k1 p := by
  sorry

/-- Characterization of when k=2 (m=11) works.
    d=1 works iff x₂ ≡ 10 (mod 11), i.e., p ≡ 29 (mod 44). -/
theorem k2_d1_criterion (p : ℕ) (hp : Nat.Prime p) (hMH : MordellHard p) :
    (xK p 2) % 11 = 10 → TypeII_k2 p := by
  sorry

/-! ## Main ESC Theorem for Mordell-Hard Primes -/

/-- The full ESC theorem for Mordell-hard primes.

    Every Mordell-hard prime has a Type II witness for some k ∈ {0,1,2} ∪ K10.

    Proof structure:
    1. Check if k=0 works → done
    2. Check if k=1 works → done
    3. Check if k=2 works → done
    4. Otherwise p is Hard10, so K10 covers it by k10_covers_hard10
-/
theorem esc_mordell_hard (p : ℕ) (hp : Nat.Prime p) (hMH : MordellHard p) :
    ∃ k : ℕ, QRSufficient k p := by
  by_cases h0 : TypeII_k0 p
  · -- k=0 works
    obtain ⟨d, hd_div, hd_le, hd_cong⟩ := h0
    exact ⟨0, d, hd_div, hd_le, hd_cong⟩
  · by_cases h1 : TypeII_k1 p
    · -- k=1 works
      obtain ⟨d, hd_div, hd_le, hd_cong⟩ := h1
      exact ⟨1, d, hd_div, hd_le, hd_cong⟩
    · by_cases h2 : TypeII_k2 p
      · -- k=2 works
        obtain ⟨d, hd_div, hd_le, hd_cong⟩ := h2
        exact ⟨2, d, hd_div, hd_le, hd_cong⟩
      · -- p is Hard10, so K10 covers it
        have h10 : Hard10 p := ⟨hMH, h0, h1, h2⟩
        obtain ⟨k, hk_mem, hk_suff⟩ := k10_covers_hard10 p hp h10
        exact ⟨k, hk_suff⟩

/-! ## Alternative: Full K13 Coverage -/

/-- K13 = {0, 1, 2} ∪ K10 -/
def K13 : Finset ℕ := {0, 1, 2, 5, 7, 9, 11, 14, 17, 19, 23, 26, 29}

/-- Alternative formulation: K13 covers all Mordell-hard primes. -/
theorem k13_covers_all (p : ℕ) (hp : Nat.Prime p) (hMH : MordellHard p) :
    ∃ k ∈ K13, QRSufficient k p := by
  obtain ⟨k, hk_suff⟩ := esc_mordell_hard p hp hMH
  -- Need to show k ∈ K13
  sorry

end ErdosStraus
