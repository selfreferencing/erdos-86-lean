/-
  ESC Main Formula - Simplified Proof Attempt
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Tactic

def esc_x (p : ℕ) : ℕ := (p + 1) / 4
def esc_y (p : ℕ) : ℕ := (p * p + p + 4) / 4
def esc_z (p : ℕ) : ℕ := (p * (p + 1) * (p * p + p + 4)) / 16

-- Divisibility
theorem p_plus_1_div_4 (p : ℕ) (hp : p % 4 = 3) : 4 ∣ (p + 1) := by
  have h2 : p + 1 = 4 * (p / 4 + 1) := by omega
  exact ⟨p / 4 + 1, h2⟩

theorem p_sq_p_4_div_4 (p : ℕ) (hp : p % 4 = 3) : 4 ∣ (p * p + p + 4) := by
  obtain ⟨q, hq⟩ : ∃ q, p = 4 * q + 3 := ⟨p / 4, by omega⟩
  use q * q * 4 + q * 7 + 4
  rw [hq]; ring

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

-- Key insight: work with explicit witnesses
theorem esc_formula_valid (p : ℕ) (hp : p % 4 = 3) (hp3 : p ≥ 3) :
    4 * (esc_x p) * (esc_y p) * (esc_z p) =
    p * ((esc_y p) * (esc_z p) + (esc_x p) * (esc_z p) + (esc_x p) * (esc_y p)) := by
  -- Get witnesses
  obtain ⟨x', hx'⟩ := p_plus_1_div_4 p hp
  obtain ⟨y', hy'⟩ := p_sq_p_4_div_4 p hp
  obtain ⟨z', hz'⟩ := product_div_16 p hp

  -- Compute the actual values
  have hx_val : esc_x p = x' := by
    unfold esc_x; rw [hx']; exact Nat.mul_div_cancel_left x' (by norm_num : 0 < 4)

  have hy_val : esc_y p = y' := by
    unfold esc_y; rw [hy']; exact Nat.mul_div_cancel_left y' (by norm_num : 0 < 4)

  have hz_val : esc_z p = z' := by
    unfold esc_z; rw [hz']; exact Nat.mul_div_cancel_left z' (by norm_num : 0 < 16)

  rw [hx_val, hy_val, hz_val]

  -- From hz': p * (p + 1) * (p*p + p + 4) = 16 * z'
  -- But p + 1 = 4 * x' and p*p + p + 4 = 4 * y'
  -- So: p * (4 * x') * (4 * y') = 16 * z'
  -- Thus: 16 * p * x' * y' = 16 * z', so z' = p * x' * y'

  have hz_eq : z' = p * x' * y' := by
    have h1 : p * (4 * x') * (4 * y') = 16 * z' := by
      calc p * (4 * x') * (4 * y')
          = p * (p + 1) * (4 * y') := by rw [← hx']
        _ = p * (p + 1) * (p * p + p + 4) := by rw [← hy']
        _ = 16 * z' := hz'
    have h2 : 16 * z' = 16 * (p * x' * y') := by linarith [h1]
    exact Nat.eq_of_mul_eq_mul_left (by norm_num : 16 > 0) h2

  rw [hz_eq]

  -- Goal: 4 * x' * y' * (p * x' * y') = p * (y' * (p*x'*y') + x' * (p*x'*y') + x' * y')
  -- Simplify both sides
  -- LHS = 4 * p * x'^2 * y'^2
  -- RHS = p * (p * x' * y'^2 + p * x'^2 * y' + x' * y') = p * x' * y' * (p*y' + p*x' + 1)

  -- We need: 4 * x' * y' = p * (x' + y') + 1

  -- From hx': 4*x' = p+1, so x' = (p+1)/4
  -- From hy': 4*y' = p²+p+4, so y' = (p²+p+4)/4

  -- 4*x'*y' = (p+1)(p²+p+4)/4
  -- p*(x'+y') + 1 = p * [(p+1)/4 + (p²+p+4)/4] + 1 = p * (p²+2p+5)/4 + 1

  -- Key identity: (p+1)(p²+p+4) = p³ + 2p² + 5p + 4
  -- So 4*x'*y' = (p³+2p²+5p+4)/4

  -- And p*(x'+y') = p*(p²+2p+5)/4 = (p³+2p²+5p)/4
  -- So p*(x'+y') + 1 = (p³+2p²+5p)/4 + 1 = (p³+2p²+5p+4)/4

  -- Therefore 4*x'*y' = p*(x'+y') + 1 ✓

  have key : 4 * x' * y' = p * (x' + y') + 1 := by
    -- 16 * x' * y' = (p+1)(p²+p+4) = p³+2p²+5p+4
    have h1 : 16 * x' * y' = (p + 1) * (p * p + p + 4) := by
      calc 16 * x' * y' = (4 * x') * (4 * y') := by ring
        _ = (p + 1) * (4 * y') := by rw [← hx']
        _ = (p + 1) * (p * p + p + 4) := by rw [← hy']

    -- 4 * (x' + y') = p²+2p+5
    have h2 : 4 * (x' + y') = p * p + 2 * p + 5 := by
      calc 4 * (x' + y') = 4 * x' + 4 * y' := by ring
        _ = (p + 1) + (4 * y') := by rw [← hx']
        _ = (p + 1) + (p * p + p + 4) := by rw [← hy']
        _ = p * p + 2 * p + 5 := by ring

    -- (p+1)(p²+p+4) = p³+2p²+5p+4
    have h3 : (p + 1) * (p * p + p + 4) = p * p * p + 2 * p * p + 5 * p + 4 := by ring

    -- 16*x'*y' = 4*p*(x'+y') + 4
    have h4 : 16 * x' * y' = 4 * p * (x' + y') + 4 := by
      rw [h1, h3]
      have h2' : p * (4 * (x' + y')) = p * (p * p + 2 * p + 5) := by rw [h2]
      calc p * p * p + 2 * p * p + 5 * p + 4
          = p * (p * p + 2 * p + 5) + 4 := by ring
        _ = p * (4 * (x' + y')) + 4 := by rw [← h2]
        _ = 4 * p * (x' + y') + 4 := by ring

    -- Divide by 4
    have h5 : 4 * (4 * x' * y') = 4 * (p * (x' + y') + 1) := by
      calc 4 * (4 * x' * y') = 16 * x' * y' := by ring
        _ = 4 * p * (x' + y') + 4 := h4
        _ = 4 * (p * (x' + y') + 1) := by ring

    exact Nat.eq_of_mul_eq_mul_left (by norm_num : 4 > 0) h5

  -- Now use key to prove the main goal
  calc 4 * x' * y' * (p * x' * y')
      = (p * x' * y') * (4 * x' * y') := by ring
    _ = (p * x' * y') * (p * (x' + y') + 1) := by rw [key]
    _ = p * x' * y' * p * (x' + y') + p * x' * y' := by ring
    _ = p * (p * x' * y' * (x' + y') + x' * y') := by ring
    _ = p * (p * x' * y' * x' + p * x' * y' * y' + x' * y') := by ring
    _ = p * (y' * (p * x' * y') + x' * (p * x' * y') + x' * y') := by ring

#check esc_formula_valid
