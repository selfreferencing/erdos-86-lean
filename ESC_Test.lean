/-
  Simple test: p ≡ 3 (mod 4) implies 4 | (p + 1)
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Tactic

-- Simple divisibility lemma
theorem p_plus_1_div_4 (p : ℕ) (hp : p % 4 = 3) : 4 ∣ (p + 1) := by
  -- p % 4 = 3 means p = 4q + 3 for some q
  -- So p + 1 = 4q + 4 = 4(q + 1)
  have h : p + 1 = 4 * (p / 4) + (p % 4) + 1 := by omega
  rw [hp] at h
  -- p + 1 = 4 * (p / 4) + 4
  have h2 : p + 1 = 4 * (p / 4 + 1) := by omega
  exact ⟨p / 4 + 1, h2⟩

-- Test the cubic factorization
theorem cubic_factor (p : ℕ) :
    p^3 + 2*p^2 + 5*p + 4 = (p + 1) * (p^2 + p + 4) := by
  ring
