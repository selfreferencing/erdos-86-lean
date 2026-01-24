/-
  Erdős-Straus Conjecture - Core Lemmas

  This file contains the elementary lemmas that can be fully verified.
-/

import Mathlib.Data.Nat.Basic
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
  -- p ≡ 3 (mod 4), so p² ≡ 9 ≡ 1 (mod 4)
  -- p² + p + 4 ≡ 1 + 3 + 0 ≡ 0 (mod 4)
  -- Write p = 4q + 3
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
-- PART 2: m_k Properties
-- ============================================================================

/-- m_k = 4k + 3 -/
def m_k (k : ℕ) : ℕ := 4 * k + 3

/-- m_k is always odd -/
theorem m_k_odd (k : ℕ) : m_k k % 2 = 1 := by
  unfold m_k
  omega

/-- m_k ≥ 3 -/
theorem m_k_ge_3 (k : ℕ) : m_k k ≥ 3 := by
  unfold m_k
  omega

/-- m_k is never divisible by 2 -/
theorem m_k_not_div_2 (k : ℕ) : ¬(2 ∣ m_k k) := by
  unfold m_k
  intro ⟨d, hd⟩
  omega

/-- m_k values: m_0 = 3, m_1 = 7, m_2 = 11, etc. -/
theorem m_k_values :
    m_k 0 = 3 ∧ m_k 1 = 7 ∧ m_k 2 = 11 ∧ m_k 3 = 15 ∧ m_k 4 = 19 ∧ m_k 5 = 23 := by
  unfold m_k
  norm_num

-- ============================================================================
-- PART 3: n_k Properties (when p ≡ 1 (mod 4))
-- ============================================================================

/-- n_k = (p + 4k + 3) / 4 -/
def n_k (p k : ℕ) : ℕ := (p + 4 * k + 3) / 4

/-- n_k is well-defined when p ≡ 1 (mod 4) -/
theorem n_k_div (p k : ℕ) (hp : p % 4 = 1) : 4 ∣ (p + 4 * k + 3) := by
  have h : (p + 4 * k + 3) % 4 = 0 := by omega
  exact Nat.dvd_of_mod_eq_zero h

/-- n_k expressed as quotient -/
theorem n_k_eq (p k : ℕ) (hp : p % 4 = 1) :
    4 * n_k p k = p + 4 * k + 3 := by
  unfold n_k
  have hdiv := n_k_div p k hp
  rw [Nat.mul_div_cancel' hdiv]

/-- n_k = (p + m_k) / 4 -/
theorem n_k_alt (p k : ℕ) : n_k p k = (p + m_k k) / 4 := by
  unfold n_k m_k
  ring_nf

-- ============================================================================
-- PART 4: The key modular construction
-- ============================================================================

/-- For any integer k, 4k + 3 mod q has a specific structure -/
theorem m_k_mod_q (k q : ℕ) :
    m_k k % q = (4 * k + 3) % q := by
  unfold m_k
  rfl

/-- If q | (4k + 3), then q | m_k -/
theorem q_div_implies_q_div_mk (k q : ℕ) (h : q ∣ (4 * k + 3)) : q ∣ m_k k := by
  unfold m_k
  exact h

-- ============================================================================
-- PART 5: ESC Algebraic Identity
-- ============================================================================

/-- The main algebraic identity connecting 4/p to the formula -/
theorem esc_identity (p x y z : ℕ) (hp : p > 0) (hx : x > 0) (hy : y > 0) (hz : z > 0) :
    4 * x * y * z = p * (y * z + x * z + x * y) ↔
    4 * (y * z + x * z + x * y) = p * (y * z + x * z + x * y) / x +
                                   p * (y * z + x * z + x * y) / y +
                                   p * (y * z + x * z + x * y) / z := by
  sorry  -- This requires careful handling of division

-- ============================================================================
-- PART 6: Verified computation for small cases
-- ============================================================================

/-- ESC solution for p = 2 -/
theorem esc_p2 : 4 * 1 * 2 * 2 = 2 * (2 * 2 + 1 * 2 + 1 * 2) := by norm_num

/-- ESC solution for p = 3 using the formula -/
theorem esc_p3 : 4 * 1 * 4 * 12 = 3 * (4 * 12 + 1 * 12 + 1 * 4) := by norm_num

/-- ESC solution for p = 5 -/
theorem esc_p5 : 4 * 2 * 4 * 20 = 5 * (4 * 20 + 2 * 20 + 2 * 4) := by norm_num

/-- ESC solution for p = 7 using the formula -/
theorem esc_p7 : 4 * 2 * 15 * 210 = 7 * (15 * 210 + 2 * 210 + 2 * 15) := by norm_num

/-- ESC solution for p = 11 using the formula -/
theorem esc_p11 : 4 * 3 * 34 * 1122 = 11 * (34 * 1122 + 3 * 1122 + 3 * 34) := by norm_num

-- ============================================================================
-- Summary
-- ============================================================================

/-
The key lemmas verified here are:

1. Divisibility conditions for p ≡ 3 (mod 4):
   - 4 | (p + 1)
   - 4 | (p² + p + 4)
   - 16 | p(p+1)(p² + p + 4)

2. Properties of m_k = 4k + 3:
   - Always odd
   - Always ≥ 3

3. Properties of n_k when p ≡ 1 (mod 4):
   - 4 | (p + 4k + 3)
   - n_k is well-defined

4. Explicit verification of ESC for small primes (2, 3, 5, 7, 11)

The full proof also requires:
- Quadratic reciprocity (in Mathlib)
- Burgess bound on least QNR (axiomatized)
- The QR-trap breaking argument
-/
