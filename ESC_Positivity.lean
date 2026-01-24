/-
  ESC Positivity Proofs - Manual attempt
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Tactic

-- Definitions
def esc_x (p : ℕ) : ℕ := (p + 1) / 4
def esc_y (p : ℕ) : ℕ := (p * p + p + 4) / 4
def esc_z (p : ℕ) : ℕ := (p * (p + 1) * (p * p + p + 4)) / 16

-- x is positive when p ≡ 3 (mod 4) and p ≥ 3
theorem esc_x_pos (p : ℕ) (hp : p % 4 = 3) (hp3 : p ≥ 3) : esc_x p > 0 := by
  unfold esc_x
  -- p ≡ 3 (mod 4) and p ≥ 3 means p ≥ 3
  -- So p + 1 ≥ 4, thus (p + 1) / 4 ≥ 1
  have h : p + 1 ≥ 4 := by omega
  exact Nat.div_pos h (by norm_num)

-- y is positive when p ≡ 3 (mod 4)
theorem esc_y_pos (p : ℕ) (hp : p % 4 = 3) : esc_y p > 0 := by
  unfold esc_y
  -- p² + p + 4 ≥ 4 for all p ≥ 0
  have h : p * p + p + 4 ≥ 4 := by omega
  exact Nat.div_pos h (by norm_num)

-- z is positive when p ≡ 3 (mod 4) and p ≥ 3
theorem esc_z_pos (p : ℕ) (hp : p % 4 = 3) (hp3 : p ≥ 3) : esc_z p > 0 := by
  unfold esc_z
  -- For p ≥ 3, p(p+1)(p²+p+4) ≥ 3 * 4 * 16 = 192 ≥ 16
  have h1 : p ≥ 3 := hp3
  have h2 : p + 1 ≥ 4 := by omega
  have h3 : p * p + p + 4 ≥ 16 := by nlinarith
  have h4 : p * (p + 1) * (p * p + p + 4) ≥ 16 := by nlinarith
  exact Nat.div_pos h4 (by norm_num)

#check esc_x_pos
#check esc_y_pos
#check esc_z_pos
