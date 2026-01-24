/-
  ESC Main Formula - Complete Proof

  Goal: 4xyz = p(yz + xz + xy)

  Strategy: Use the key identity (p+1)(p²+p+4) = p³+2p²+5p+4
  which we've already proved.
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Tactic

-- Definitions
def esc_x (p : ℕ) : ℕ := (p + 1) / 4
def esc_y (p : ℕ) : ℕ := (p * p + p + 4) / 4
def esc_z (p : ℕ) : ℕ := (p * (p + 1) * (p * p + p + 4)) / 16

-- Divisibility lemmas (already proved)
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

-- Key equations
theorem esc_x_eq (p : ℕ) (hp : p % 4 = 3) : 4 * esc_x p = p + 1 := by
  unfold esc_x
  exact Nat.mul_div_cancel' (p_plus_1_div_4 p hp)

theorem esc_y_eq (p : ℕ) (hp : p % 4 = 3) : 4 * esc_y p = p * p + p + 4 := by
  unfold esc_y
  exact Nat.mul_div_cancel' (p_sq_p_4_div_4 p hp)

theorem esc_z_eq (p : ℕ) (hp : p % 4 = 3) :
    16 * esc_z p = p * (p + 1) * (p * p + p + 4) := by
  unfold esc_z
  exact Nat.mul_div_cancel' (product_div_16 p hp)

-- The key algebraic identity
theorem key_identity (p : ℕ) :
    (p + 1) * (p * p + p + 4) = p * p * p + 2 * p * p + 5 * p + 4 := by ring

-- Now the main proof
-- We work with scaled values to avoid division issues
-- Let X = 4x, Y = 4y, Z = 16z (the "unscaled" values)
-- Then: X = p + 1, Y = p² + p + 4, Z = p * X * Y

-- LHS: 4xyz = 4 * (X/4) * (Y/4) * (Z/16) = XYZ / 64
-- RHS: p(yz + xz + xy) = p[(Y/4)(Z/16) + (X/4)(Z/16) + (X/4)(Y/4)]
--    = p[YZ/64 + XZ/64 + XY/16]
--    = p[YZ + XZ + 4XY] / 64

-- For equality: XYZ = p(YZ + XZ + 4XY) = pZ(Y + X) + 4pXY
-- Since Z = pXY: XY * pXY = pXY(X + Y) * p + 4pXY
-- Simplify: pX²Y² = p²XY(X + Y) + 4pXY = pXY[p(X + Y) + 4]
-- So: XY = p(X + Y) + 4
-- i.e., (p+1)(p²+p+4) = p[(p+1) + (p²+p+4)] + 4
--     = p[p² + 2p + 5] + 4 = p³ + 2p² + 5p + 4 ✓

-- This is exactly the key_identity!

theorem esc_formula_valid (p : ℕ) (hp : p % 4 = 3) (hp3 : p ≥ 3) :
    4 * (esc_x p) * (esc_y p) * (esc_z p) =
    p * ((esc_y p) * (esc_z p) + (esc_x p) * (esc_z p) + (esc_x p) * (esc_y p)) := by
  -- Get the scaled equations
  have hx : 4 * esc_x p = p + 1 := esc_x_eq p hp
  have hy : 4 * esc_y p = p * p + p + 4 := esc_y_eq p hp
  have hz : 16 * esc_z p = p * (p + 1) * (p * p + p + 4) := esc_z_eq p hp
  -- Use the key identity
  have hkey : (p + 1) * (p * p + p + 4) = p * p * p + 2 * p * p + 5 * p + 4 := key_identity p
  -- The proof requires showing the scaled identity holds
  -- We need: 4 * x * y * z = p * (y*z + x*z + x*y)
  -- Multiply both sides by 64:
  -- 256 * x * y * z = 64 * p * (y*z + x*z + x*y)
  -- LHS = 4 * (4x) * (4y) * (4z) = 4 * X * Y * (Z/4) where Z = 16z
  -- This gets complicated with natural number division...

  -- Alternative: work directly with the witnesses
  -- Since 4 | X and 4 | Y and 16 | Z, we can use:
  obtain ⟨x', hx'⟩ := p_plus_1_div_4 p hp
  obtain ⟨y', hy'⟩ := p_sq_p_4_div_4 p hp
  obtain ⟨z', hz'⟩ := product_div_16 p hp

  -- Now esc_x p = x', esc_y p = y', esc_z p = z'
  have hx_val : esc_x p = x' := by
    unfold esc_x
    rw [hx']
    simp [Nat.mul_div_cancel_left]

  have hy_val : esc_y p = y' := by
    unfold esc_y
    rw [hy']
    simp [Nat.mul_div_cancel_left]

  have hz_val : esc_z p = z' := by
    unfold esc_z
    rw [hz']
    simp [Nat.mul_div_cancel_left]

  -- Now prove the identity using x', y', z'
  rw [hx_val, hy_val, hz_val]

  -- We have: 4*x' = p+1, 4*y' = p²+p+4, 16*z' = p(p+1)(p²+p+4)
  -- From hx': p + 1 = 4 * x'
  -- From hy': p*p + p + 4 = 4 * y'
  -- From hz': p * (p + 1) * (p*p + p + 4) = 16 * z'

  -- Goal: 4 * x' * y' * z' = p * (y' * z' + x' * z' + x' * y')

  -- Substitute using the equations
  have eq1 : p + 1 = 4 * x' := hx'
  have eq2 : p * p + p + 4 = 4 * y' := hy'
  have eq3 : p * (p + 1) * (p * p + p + 4) = 16 * z' := hz'

  -- From eq3: p * (4*x') * (4*y') = 16 * z'
  -- So: 16 * p * x' * y' = 16 * z'
  -- Thus: z' = p * x' * y'
  have hz_simp : z' = p * x' * y' := by
    have h1 : p * (4 * x') * (4 * y') = 16 * z' := by rw [← eq1, ← eq2]; exact hz'
    have h2 : 16 * p * x' * y' = 16 * z' := by linarith [h1]
    omega

  rw [hz_simp]

  -- Goal: 4 * x' * y' * (p * x' * y') = p * (y' * (p * x' * y') + x' * (p * x' * y') + x' * y')
  -- LHS = 4 * p * x'^2 * y'^2
  -- RHS = p * (p * x' * y'^2 + p * x'^2 * y' + x' * y')
  --     = p * x' * y' * (p * y' + p * x' + 1)
  --     = p * x' * y' * (p * (x' + y') + 1)

  -- For LHS = RHS: 4 * x' * y' = p * (x' + y') + 1
  -- i.e., 4 * x' * y' - 1 = p * (x' + y')

  -- From eq1: x' = (p+1)/4
  -- From eq2: y' = (p²+p+4)/4
  -- So x' + y' = (p+1 + p²+p+4)/4 = (p²+2p+5)/4

  -- 4*x'*y' = (p+1)(p²+p+4)/4 = (p³+2p²+5p+4)/4  [by key_identity]
  -- p*(x'+y') = p*(p²+2p+5)/4

  -- We need: (p³+2p²+5p+4)/4 - 1/4 ≠ p*(p²+2p+5)/4... wait that's not right

  -- Let me recalculate. Actually:
  -- LHS = 4 * x' * y' * z' = 4 * x' * y' * p * x' * y' = 4p * x'^2 * y'^2
  -- RHS = p * (y'*z' + x'*z' + x'*y')
  --     = p * (y' * p*x'*y' + x' * p*x'*y' + x'*y')
  --     = p * (p*x'*y'^2 + p*x'^2*y' + x'*y')
  --     = p * x' * y' * (p*y' + p*x' + 1)

  -- For equality: 4 * x' * y' = p * y' + p * x' + 1
  --              4 * x' * y' = p * (x' + y') + 1

  -- Now 4*x' = p+1 and 4*y' = p²+p+4
  -- So 16*x'*y' = (p+1)(p²+p+4) = p³+2p²+5p+4 [by key_identity]
  -- And 4*(x'+y') = (p+1) + (p²+p+4) = p²+2p+5

  -- We need: 4*x'*y' = p*(x'+y') + 1
  -- Multiply by 4: 16*x'*y' = 4p*(x'+y') + 4
  -- i.e., p³+2p²+5p+4 = p*(p²+2p+5) + 4
  --     = p³ + 2p² + 5p + 4 ✓

  -- So the key is: 16*x'*y' = 4*p*(x'+y') + 4

  have h_xy : 16 * x' * y' = (p + 1) * (p * p + p + 4) := by
    calc 16 * x' * y' = (4 * x') * (4 * y') := by ring
      _ = (p + 1) * (p * p + p + 4) := by rw [eq1, eq2]

  have h_sum : 4 * (x' + y') = p * p + 2 * p + 5 := by
    calc 4 * (x' + y') = 4 * x' + 4 * y' := by ring
      _ = (p + 1) + (p * p + p + 4) := by rw [eq1, eq2]
      _ = p * p + 2 * p + 5 := by ring

  -- The key algebraic fact
  have h_key_calc : 16 * x' * y' = 4 * p * (x' + y') + 4 := by
    rw [h_xy]
    have h1 : (p + 1) * (p * p + p + 4) = p * p * p + 2 * p * p + 5 * p + 4 := by ring
    have h2 : 4 * p * (x' + y') + 4 = p * (4 * (x' + y')) + 4 := by ring
    rw [h2, h_sum, h1]
    ring

  -- Now derive: 4 * x' * y' = p * (x' + y') + 1
  have h_main : 4 * x' * y' = p * (x' + y') + 1 := by
    have h := h_key_calc
    omega

  -- Finally prove the goal
  ring_nf
  calc 4 * x' * y' * (p * x' * y')
      = 4 * p * (x' * y') ^ 2 := by ring
    _ = p * (x' * y') * (4 * x' * y') := by ring
    _ = p * (x' * y') * (p * (x' + y') + 1) := by rw [h_main]
    _ = p * (p * x' * y' * (x' + y') + x' * y') := by ring
    _ = p * (p * x' * y' * x' + p * x' * y' * y' + x' * y') := by ring
    _ = p * (p * x' ^ 2 * y' + p * x' * y' ^ 2 + x' * y') := by ring
    _ = p * (x' * (p * x' * y') + y' * (p * x' * y') + x' * y') := by ring
    _ = p * (y' * (p * x' * y') + x' * (p * x' * y') + x' * y') := by ring

#check esc_formula_valid
