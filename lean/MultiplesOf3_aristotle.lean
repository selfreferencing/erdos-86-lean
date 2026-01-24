/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 811628e9-a085-4d32-8333-78b61e0068d3

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>
-/

import Mathlib


namespace ErdosStraus

/-- Standard Erdős–Straus solution predicate (integer form). -/
def HasErdosStrausSolution (n : ℕ) : Prop :=
  ∃ x y z : ℕ, 0 < x ∧ 0 < y ∧ 0 < z ∧
    4 * x * y * z = n * (y * z + x * z + x * y)

/-- For n = 3, the solution is x=1, y=4, z=12. -/
lemma solution_3 : HasErdosStrausSolution 3 := by
  use 1, 4, 12
  repeat' constructor <;> norm_num

/-- If 3 ∣ n and n > 0, then n has an Erdős–Straus solution.
For n = 3m we use x = m, y = 4m, z = 12m. -/
theorem mult3_has_solution (n : ℕ) (h3 : 3 ∣ n) (hn : 0 < n) :
    HasErdosStrausSolution n := by
  obtain ⟨m, rfl⟩ := h3
  -- Now hn : 0 < 3 * m, so m > 0.
  have hm : 0 < m := by
    have hm_ne : m ≠ 0 := by
      intro hm0
      have : (0 : ℕ) < 0 := by
        simpa [hm0] using hn
      exact (lt_irrefl 0) this
    exact Nat.pos_of_ne_zero hm_ne

  -- Explicit construction
  use m, 4 * m, 12 * m
  refine ⟨hm, ?_, ?_, ?_⟩
  · have h4 : 0 < (4 : ℕ) := by norm_num
    exact Nat.mul_pos h4 hm
  · have h12 : 0 < (12 : ℕ) := by norm_num
    exact Nat.mul_pos h12 hm
  · -- algebraic verification
    ring

end ErdosStraus