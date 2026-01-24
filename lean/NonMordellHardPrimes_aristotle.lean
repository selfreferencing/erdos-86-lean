/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: a1ea0f5a-fee9-44c8-9b46-820390ca0f08

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>
-/

import Mathlib


namespace ErdosStraus

/-- Cleared-denominator form of `4/n = 1/x + 1/y + 1/z`. -/
def HasErdosStrausSolution (n : ℕ) : Prop :=
  ∃ x y z : ℕ, 0 < x ∧ 0 < y ∧ 0 < z ∧
    4 * x * y * z = n * (y * z + x * z + x * y)

/-- Mordell-hard residue classes mod 840. -/
def MordellHardClasses : Finset ℕ := {1, 121, 169, 289, 361, 529}

/-- A prime that is *not* Mordell-hard. -/
def isNonMordellHardPrime (p : ℕ) : Prop :=
  Nat.Prime p ∧ p % 840 ∉ MordellHardClasses

/-
  Small prime solutions (direct).
  Note: the prompt's table lists (3,12,132) for p=11, but the correct one is (3,44,132).
-/
lemma solution_2 : HasErdosStrausSolution 2 := by
  refine ⟨1, 2, 2, ?_, ?_, ?_, ?_⟩ <;> norm_num

lemma solution_3 : HasErdosStrausSolution 3 := by
  refine ⟨1, 4, 12, ?_, ?_, ?_, ?_⟩ <;> norm_num

lemma solution_5 : HasErdosStrausSolution 5 := by
  refine ⟨2, 4, 20, ?_, ?_, ?_, ?_⟩ <;> norm_num

lemma solution_7 : HasErdosStrausSolution 7 := by
  refine ⟨2, 28, 28, ?_, ?_, ?_, ?_⟩ <;> norm_num

lemma solution_11 : HasErdosStrausSolution 11 := by
  refine ⟨3, 44, 132, ?_, ?_, ?_, ?_⟩ <;> norm_num

lemma solution_13 : HasErdosStrausSolution 13 := by
  refine ⟨4, 18, 468, ?_, ?_, ?_, ?_⟩ <;> norm_num

/--
Primes `p ≡ 2 (mod 3)` have a Type I solution:

Let `p+1 = 3a`. Then
`4/p = 1/p + 1/a + 1/(p*a)`.

In cleared form, we witness with `(x,y,z) = (p, a, p*a)`.
-/
lemma prime_2_mod_3_has_solution (p : ℕ) (hp : Nat.Prime p) (hmod : p % 3 = 2) :
    HasErdosStrausSolution p := by
  -- First show `3 ∣ p + 1` from `p % 3 = 2`.
  have hdiv : 3 ∣ p + 1 := by
    have h0 : (p + 1) % 3 = 0 := by
      -- (p+1) % 3 = (p % 3 + 1 % 3) % 3 = (2+1) % 3 = 0
      simp [Nat.add_mod, hmod]
    exact Nat.dvd_of_mod_eq_zero h0

  rcases hdiv with ⟨a, ha⟩
  -- ha : p + 1 = 3 * a

  have hp_pos : 0 < p := hp.pos

  have ha_ne : a ≠ 0 := by
    intro ha0
    have : p + 1 = 0 := by simpa [ha0] using ha
    exact Nat.succ_ne_zero p this

  have ha_pos : 0 < a := Nat.pos_of_ne_zero ha_ne

  refine ⟨p, a, p * a, hp_pos, ha_pos, Nat.mul_pos hp_pos ha_pos, ?_⟩

  -- Main cleared-denominator equality:
  -- show 4 * p * a * (p * a) = p * (a * (p * a) + p * (p * a) + p * a)
  -- We rewrite the RHS so that `p+1` appears, then substitute `p+1 = 3a`.
  have hR :
      p * (a * (p * a) + p * (p * a) + p * a) = 4 * p * a * (p * a) := by
    calc
      p * (a * (p * a) + p * (p * a) + p * a)
          = p * (p * a * a + p * a * (p + 1)) := by
              ring
      _ = p * (p * a * a + p * a * (3 * a)) := by
              -- use `ha : p+1 = 3a`
              simpa [ha]
      _ = p * (4 * p * a * a) := by
              ring
      _ = 4 * p * a * (p * a) := by
              ring

  exact hR.symm

/- Aristotle failed to find a proof. -/
/--
The remaining non-Mordell-hard primes not covered by the `p % 3 = 2` family
(i.e. effectively `p % 3 = 1` but `p % 840 ∉ MordellHardClasses`) are intended
to be discharged by the Bradford Type II analysis for `k ∈ {0,1,2}`.

Fill this in by importing your `Bradford.lean` / `Families...` files and applying
the appropriate "k=0/1/2 works" lemmas.
-/
lemma nonMordellHard_not_mod3eq2_has_solution
    (p : ℕ) (hp : Nat.Prime p) (hp3 : p ≠ 3) (hmod2 : p % 3 ≠ 2)
    (hnonMH : p % 840 ∉ MordellHardClasses) :
    HasErdosStrausSolution p := by
  -- At this point, for prime `p ≠ 3`, one can show `p % 3 = 1`.
  -- Then use residue-class / Bradford k∈{0,1,2} coverage for the non-Mordell-hard classes.
  --
  -- Suggested approach (once you import the project lemmas):
  --   have : p % 3 = 1 := by
  --     -- since p%3 ≠ 0 (else 3 ∣ p) and p%3 ≠ 2, remainder must be 1
  --     ...
  --   exact (your_k012_cover_lemma p hp hnonMH this)
  --
  sorry

/-- Non-Mordell-hard primes all have Erdős–Straus solutions. -/
theorem nonMordellHard_has_solution (p : ℕ) (hp : Nat.Prime p)
    (hnonMH : p % 840 ∉ MordellHardClasses) :
    HasErdosStrausSolution p := by
  by_cases hp3 : p = 3
  · subst hp3
    exact solution_3
  by_cases hmod2 : p % 3 = 2
  · exact prime_2_mod_3_has_solution p hp hmod2
  · exact nonMordellHard_not_mod3eq2_has_solution p hp hp3 hmod2 hnonMH

/-- Convenience wrapper using `isNonMordellHardPrime`. -/
theorem isNonMordellHardPrime_has_solution (p : ℕ) (h : isNonMordellHardPrime p) :
    HasErdosStrausSolution p :=
  nonMordellHard_has_solution p h.1 h.2

end ErdosStraus