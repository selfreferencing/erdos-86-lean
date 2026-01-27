/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: eea40bdc-db08-4199-b87f-e181fb3aab19

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>
-/

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