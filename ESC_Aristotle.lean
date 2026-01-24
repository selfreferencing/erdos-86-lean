/-
  ESC Theorems for Aristotle to prove
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic

-- Definitions
def esc_x (p : ℕ) : ℕ := (p + 1) / 4
def esc_y (p : ℕ) : ℕ := (p * p + p + 4) / 4
def esc_z (p : ℕ) : ℕ := (p * (p + 1) * (p * p + p + 4)) / 16

-- Already proved lemmas (from ESC_Verified.lean)
theorem p_plus_1_div_4 (p : ℕ) (hp : p % 4 = 3) : 4 ∣ (p + 1) := by
  have h2 : p + 1 = 4 * (p / 4 + 1) := by omega
  exact ⟨p / 4 + 1, h2⟩

theorem p_sq_p_4_div_4 (p : ℕ) (hp : p % 4 = 3) : 4 ∣ (p * p + p + 4) := by
  obtain ⟨q, hq⟩ : ∃ q, p = 4 * q + 3 := ⟨p / 4, by omega⟩
  use q * q * 4 + q * 7 + 4
  rw [hq]
  ring

theorem product_div_16 (p : ℕ) (hp : p % 4 = 3) :
    16 ∣ p * (p + 1) * (p * p + p + 4) := by
  have h1 : 4 ∣ (p + 1) := p_plus_1_div_4 p hp
  have h2 : 4 ∣ (p * p + p + 4) := p_sq_p_4_div_4 p hp
  obtain ⟨a, ha⟩ := h1
  obtain ⟨b, hb⟩ := h2
  use p * a * b
  calc p * (p + 1) * (p * p + p + 4)
      = p * (4 * a) * (4 * b) := by rw [ha, hb]
    _ = 16 * (p * a * b) := by ring

-- THEOREM 1: x is positive
theorem esc_x_pos (p : ℕ) (hp : p % 4 = 3) (hp3 : p ≥ 3) : esc_x p > 0 := by
  sorry

-- THEOREM 2: y is positive
theorem esc_y_pos (p : ℕ) (hp : p % 4 = 3) (hp3 : p ≥ 3) : esc_y p > 0 := by
  sorry

-- THEOREM 3: z is positive
theorem esc_z_pos (p : ℕ) (hp : p % 4 = 3) (hp3 : p ≥ 3) : esc_z p > 0 := by
  sorry

-- THEOREM 4: The main identity
theorem esc_formula_valid (p : ℕ) (hp : p % 4 = 3) (hp3 : p ≥ 3) :
    4 * (esc_x p) * (esc_y p) * (esc_z p) =
    p * ((esc_y p) * (esc_z p) + (esc_x p) * (esc_z p) + (esc_x p) * (esc_y p)) := by
  sorry
