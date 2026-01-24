/-
  Erdős-Straus Conjecture - Verified Lean 4 Lemmas

  These are the lemmas we can fully verify without sorry.
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic

-- ============================================================================
-- PART 1: Divisibility Lemmas for p ≡ 3 (mod 4)
-- ============================================================================

/-- (p + 1) is divisible by 4 when p ≡ 3 (mod 4) -/
theorem p_plus_1_div_4 (p : ℕ) (hp : p % 4 = 3) : 4 ∣ (p + 1) := by
  have h2 : p + 1 = 4 * (p / 4 + 1) := by omega
  exact ⟨p / 4 + 1, h2⟩

/-- (p² + p + 4) is divisible by 4 when p ≡ 3 (mod 4) -/
theorem p_sq_p_4_div_4 (p : ℕ) (hp : p % 4 = 3) : 4 ∣ (p * p + p + 4) := by
  obtain ⟨q, hq⟩ : ∃ q, p = 4 * q + 3 := ⟨p / 4, by omega⟩
  use q * q * 4 + q * 7 + 4
  rw [hq]
  ring

/-- The product p(p+1) is divisible by 4 when p ≡ 3 (mod 4) -/
theorem p_times_p_plus_1_div_4 (p : ℕ) (hp : p % 4 = 3) : 4 ∣ p * (p + 1) := by
  have hdiv : 4 ∣ (p + 1) := p_plus_1_div_4 p hp
  obtain ⟨k, hk⟩ := hdiv
  use p * k
  rw [hk]
  ring

/-- The full product is divisible by 16 -/
theorem product_div_16 (p : ℕ) (hp : p % 4 = 3) :
    16 ∣ p * (p + 1) * (p * p + p + 4) := by
  have h1 : 4 ∣ p * (p + 1) := p_times_p_plus_1_div_4 p hp
  have h2 : 4 ∣ (p * p + p + 4) := p_sq_p_4_div_4 p hp
  obtain ⟨a, ha⟩ := h1
  obtain ⟨b, hb⟩ := h2
  use a * b
  calc p * (p + 1) * (p * p + p + 4)
      = (4 * a) * (4 * b) := by rw [ha, hb]
    _ = 16 * (a * b) := by ring

/-- Key algebraic identity: p³ + 2p² + 5p + 4 = (p + 1)(p² + p + 4) -/
theorem cubic_factor (p : ℕ) :
    p^3 + 2*p^2 + 5*p + 4 = (p + 1) * (p^2 + p + 4) := by
  ring

-- ============================================================================
-- PART 2: Explicit ESC Solutions (Fully Verified)
-- ============================================================================

/-- ESC for p = 2 -/
theorem esc_p2 : ∃ x y z : ℕ, x > 0 ∧ y > 0 ∧ z > 0 ∧
    4 * x * y * z = 2 * (y * z + x * z + x * y) := ⟨1, 2, 2, by norm_num⟩

/-- ESC for p = 3 -/
theorem esc_p3 : ∃ x y z : ℕ, x > 0 ∧ y > 0 ∧ z > 0 ∧
    4 * x * y * z = 3 * (y * z + x * z + x * y) := ⟨1, 4, 12, by norm_num⟩

/-- ESC for p = 5 -/
theorem esc_p5 : ∃ x y z : ℕ, x > 0 ∧ y > 0 ∧ z > 0 ∧
    4 * x * y * z = 5 * (y * z + x * z + x * y) := ⟨2, 4, 20, by norm_num⟩

/-- ESC for p = 7 -/
theorem esc_p7 : ∃ x y z : ℕ, x > 0 ∧ y > 0 ∧ z > 0 ∧
    4 * x * y * z = 7 * (y * z + x * z + x * y) := ⟨2, 15, 210, by norm_num⟩

/-- ESC for p = 11 -/
theorem esc_p11 : ∃ x y z : ℕ, x > 0 ∧ y > 0 ∧ z > 0 ∧
    4 * x * y * z = 11 * (y * z + x * z + x * y) := ⟨3, 34, 1122, by norm_num⟩

/-- ESC for p = 13 -/
theorem esc_p13 : ∃ x y z : ℕ, x > 0 ∧ y > 0 ∧ z > 0 ∧
    4 * x * y * z = 13 * (y * z + x * z + x * y) := ⟨4, 18, 468, by norm_num⟩

/-- ESC for p = 17 -/
theorem esc_p17 : ∃ x y z : ℕ, x > 0 ∧ y > 0 ∧ z > 0 ∧
    4 * x * y * z = 17 * (y * z + x * z + x * y) := ⟨5, 30, 510, by norm_num⟩

/-- ESC for p = 19 -/
theorem esc_p19 : ∃ x y z : ℕ, x > 0 ∧ y > 0 ∧ z > 0 ∧
    4 * x * y * z = 19 * (y * z + x * z + x * y) := ⟨5, 96, 9120, by norm_num⟩

/-- ESC for p = 23 -/
theorem esc_p23 : ∃ x y z : ℕ, x > 0 ∧ y > 0 ∧ z > 0 ∧
    4 * x * y * z = 23 * (y * z + x * z + x * y) := ⟨6, 139, 19182, by norm_num⟩

/-- ESC for p = 29 -/
theorem esc_p29 : ∃ x y z : ℕ, x > 0 ∧ y > 0 ∧ z > 0 ∧
    4 * x * y * z = 29 * (y * z + x * z + x * y) := ⟨8, 78, 9048, by norm_num⟩

/-- ESC for p = 31 -/
theorem esc_p31 : ∃ x y z : ℕ, x > 0 ∧ y > 0 ∧ z > 0 ∧
    4 * x * y * z = 31 * (y * z + x * z + x * y) := ⟨8, 249, 61752, by norm_num⟩

/-- ESC for p = 37 -/
theorem esc_p37 : ∃ x y z : ℕ, x > 0 ∧ y > 0 ∧ z > 0 ∧
    4 * x * y * z = 37 * (y * z + x * z + x * y) := ⟨10, 124, 22940, by norm_num⟩

/-- ESC for p = 41 -/
theorem esc_p41 : ∃ x y z : ℕ, x > 0 ∧ y > 0 ∧ z > 0 ∧
    4 * x * y * z = 41 * (y * z + x * z + x * y) := ⟨11, 154, 6314, by norm_num⟩

/-- ESC for p = 43 -/
theorem esc_p43 : ∃ x y z : ℕ, x > 0 ∧ y > 0 ∧ z > 0 ∧
    4 * x * y * z = 43 * (y * z + x * z + x * y) := ⟨11, 474, 224202, by norm_num⟩

/-- ESC for p = 47 -/
theorem esc_p47 : ∃ x y z : ℕ, x > 0 ∧ y > 0 ∧ z > 0 ∧
    4 * x * y * z = 47 * (y * z + x * z + x * y) := ⟨12, 565, 318660, by norm_num⟩

-- ============================================================================
-- PART 3: m_k and n_k Properties
-- ============================================================================

/-- m_k = 4k + 3 -/
def m_k (k : ℕ) : ℕ := 4 * k + 3

/-- n_k = (p + 4k + 3) / 4 -/
def n_k (p k : ℕ) : ℕ := (p + 4 * k + 3) / 4

/-- m_k is always odd -/
theorem m_k_odd (k : ℕ) : m_k k % 2 = 1 := by unfold m_k; omega

/-- m_k ≥ 3 -/
theorem m_k_ge_3 (k : ℕ) : m_k k ≥ 3 := by unfold m_k; omega

/-- m_k is never divisible by 2 -/
theorem m_k_not_div_2 (k : ℕ) : ¬ (2 ∣ m_k k) := by
  unfold m_k; intro ⟨r, hr⟩; omega

/-- m_k values -/
theorem m_k_values : m_k 0 = 3 ∧ m_k 1 = 7 ∧ m_k 2 = 11 ∧ m_k 3 = 15 ∧
    m_k 4 = 19 ∧ m_k 5 = 23 := by unfold m_k; norm_num

/-- n_k is well-defined when p ≡ 1 (mod 4) -/
theorem n_k_div (p k : ℕ) (hp : p % 4 = 1) : 4 ∣ (p + 4 * k + 3) := by
  have h : (p + 4 * k + 3) % 4 = 0 := by omega
  exact Nat.dvd_of_mod_eq_zero h

/-- 4 * n_k = p + 4k + 3 when p ≡ 1 (mod 4) -/
theorem n_k_eq (p k : ℕ) (hp : p % 4 = 1) : 4 * n_k p k = p + 4 * k + 3 := by
  unfold n_k
  exact Nat.mul_div_cancel' (n_k_div p k hp)

-- ============================================================================
-- PART 4: Verified Formula Components
-- ============================================================================

/-- x value for ESC formula -/
def esc_x (p : ℕ) : ℕ := (p + 1) / 4

/-- y value for ESC formula -/
def esc_y (p : ℕ) : ℕ := (p * p + p + 4) / 4

/-- z value for ESC formula -/
def esc_z (p : ℕ) : ℕ := p * (p + 1) * (p * p + p + 4) / 16

/-- 4 * x = p + 1 when p ≡ 3 (mod 4) -/
theorem esc_x_eq (p : ℕ) (hp : p % 4 = 3) : 4 * esc_x p = p + 1 := by
  unfold esc_x
  exact Nat.mul_div_cancel' (p_plus_1_div_4 p hp)

/-- 4 * y = p² + p + 4 when p ≡ 3 (mod 4) -/
theorem esc_y_eq (p : ℕ) (hp : p % 4 = 3) : 4 * esc_y p = p * p + p + 4 := by
  unfold esc_y
  exact Nat.mul_div_cancel' (p_sq_p_4_div_4 p hp)

/-- 16 * z = p(p+1)(p² + p + 4) when p ≡ 3 (mod 4) -/
theorem esc_z_eq (p : ℕ) (hp : p % 4 = 3) :
    16 * esc_z p = p * (p + 1) * (p * p + p + 4) := by
  unfold esc_z
  exact Nat.mul_div_cancel' (product_div_16 p hp)

-- ============================================================================
-- Summary of What's Verified
-- ============================================================================

/-
FULLY VERIFIED (no sorry):

1. DIVISIBILITY LEMMAS:
   - p_plus_1_div_4: 4 | (p + 1) when p ≡ 3 (mod 4)
   - p_sq_p_4_div_4: 4 | (p² + p + 4) when p ≡ 3 (mod 4)
   - p_times_p_plus_1_div_4: 4 | p(p+1) when p ≡ 3 (mod 4)
   - product_div_16: 16 | p(p+1)(p² + p + 4) when p ≡ 3 (mod 4)

2. ALGEBRAIC IDENTITY:
   - cubic_factor: p³ + 2p² + 5p + 4 = (p + 1)(p² + p + 4)

3. EXPLICIT ESC SOLUTIONS for p = 2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47

4. m_k PROPERTIES:
   - m_k_odd: m_k is always odd
   - m_k_ge_3: m_k ≥ 3
   - m_k_not_div_2: 2 ∤ m_k
   - m_k_values: m_0 = 3, m_1 = 7, m_2 = 11, etc.

5. n_k PROPERTIES:
   - n_k_div: 4 | (p + 4k + 3) when p ≡ 1 (mod 4)
   - n_k_eq: 4 * n_k = p + 4k + 3 when p ≡ 1 (mod 4)

6. FORMULA COMPONENTS:
   - esc_x_eq: 4 * x = p + 1 when p ≡ 3 (mod 4)
   - esc_y_eq: 4 * y = p² + p + 4 when p ≡ 3 (mod 4)
   - esc_z_eq: 16 * z = p(p+1)(p² + p + 4) when p ≡ 3 (mod 4)

TOTAL: 25+ theorems fully verified in Lean 4
-/
