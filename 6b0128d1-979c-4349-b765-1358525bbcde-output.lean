/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 6b0128d1-979c-4349-b765-1358525bbcde

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The version of Mathlib expected in this file appears to be incompatible with Aristotle's.
Please either switch your project to use the same version, or try again with `import Mathlib` only.
Details:
object file '/code/harmonic-lean/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib/Data/Nat/Parity.olean' of module Mathlib.Data.Nat.Parity does not exist
-/

/-
GPT Prompt 11: EvenNumbers.lean

Goal: prove that every even `n ≥ 2` has an Erdős–Straus solution:
  4/n = 1/x + 1/y + 1/z

We work in the cleared-denominator form:
  4 * x * y * z = n * (y*z + x*z + x*y)
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Parity
import Mathlib.Tactic

namespace ErdosStraus

/-- A natural number `n` has an Erdős–Straus solution if there exist positive naturals
`x y z` such that `4/n = 1/x + 1/y + 1/z`.  We use the standard cleared-denominator form:
`4xyz = n(yz + xz + xy)`. -/
def HasErdosStrausSolution (n : ℕ) : Prop :=
  ∃ x y z : ℕ, 0 < x ∧ 0 < y ∧ 0 < z ∧
    4 * x * y * z = n * (y * z + x * z + x * y)

/-- A concrete solution for `n = 2`: take `x=1, y=2, z=2`. -/
lemma solution_2 : HasErdosStrausSolution 2 := by
  use 1, 2, 2
  norm_num

/-- If `n` is even and `n ≥ 2`, then `n` has an Erdős–Straus solution.

For `n = 2m` with `m ≥ 1`, take:
`x = m`, `y = 2m`, `z = 2m`. -/
theorem even_has_solution (n : ℕ) (heven : 2 ∣ n) (hn : 2 ≤ n) :
    HasErdosStrausSolution n := by
  -- Write `n = 2*m`.
  obtain ⟨m, rfl⟩ := heven
  -- From `2 ≤ 2*m` we get `m ≠ 0`, hence `0 < m`.
  have hm0 : m ≠ 0 := by
    intro h
    subst h
    -- Now `hn : 2 ≤ 2*0`, contradiction.
    have : ¬ (2 : ℕ) ≤ 2 * 0 := by decide
    exact this hn
  have hm : 0 < m := Nat.pos_of_ne_zero hm0
  have h2 : 0 < (2 : ℕ) := by decide
  have h2m : 0 < 2 * m := Nat.mul_pos h2 hm

  -- Use the explicit witnesses.
  use m, 2 * m, 2 * m
  refine ⟨hm, h2m, h2m, ?_⟩
  -- Verify the algebraic identity.
  ring

end ErdosStraus
