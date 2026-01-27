import Mathlib

theorem pollack_bound (p : ℕ) (hp : Nat.Prime p) (hp_mod : p % 4 = 1) (hp_ge : p ≥ 5) :
    ∃ q : ℕ, Nat.Prime q ∧ q % 4 = 3 ∧ q ≤ (p + 1) / 2 := by
  refine ⟨3, Nat.prime_three, ?_, ?_⟩
  · decide
  · have h6 : 6 ≤ p + 1 := by
      have := Nat.add_le_add_right hp_ge 1
      simpa using this
    have hpos : 0 < (2 : ℕ) := by decide
    exact (Nat.le_div_iff_mul_le hpos).2 (by simpa using h6)
