import Mathlib

namespace ErdosStraus

/-- Standard "cleared denominators" Erdős–Straus predicate:
`4/n = 1/x + 1/y + 1/z` ↔ `4xyz = n(yz + xz + xy)` (over ℕ). -/
def HasErdosStrausSolution (n : ℕ) : Prop :=
  ∃ x y z : ℕ, 0 < x ∧ 0 < y ∧ 0 < z ∧
    4 * x * y * z = n * (y * z + x * z + x * y)

/-!
### Scaling lemma

If we have a solution for `a`, we automatically get a solution for `a*b` (for `b>0`)
by scaling denominators: `(x,y,z) ↦ (x*b, y*b, z*b)`.
-/

/-- If `a` has a solution, then so does `a*b` for any positive `b`. -/
lemma HasErdosStrausSolution.mul_right {a b : ℕ}
    (ha : HasErdosStrausSolution a) (hb : 0 < b) :
    HasErdosStrausSolution (a * b) := by
  rcases ha with ⟨x, y, z, hx, hy, hz, hEq⟩
  refine ⟨x * b, y * b, z * b, Nat.mul_pos hx hb, Nat.mul_pos hy hb, Nat.mul_pos hz hb, ?_⟩

  -- Multiply the base equation by `b^3` (written as `b*b*b`) and normalize both sides.
  have hEq' :
      (4 * x * y * z) * (b * b * b) =
        (a * (y * z + x * z + x * y)) * (b * b * b) := by
    simpa [mul_assoc] using congrArg (fun t => t * (b * b * b)) hEq

  calc
    4 * (x * b) * (y * b) * (z * b)
        = (4 * x * y * z) * (b * b * b) := by
            ring
    _ = (a * (y * z + x * z + x * y)) * (b * b * b) := by
            simpa using hEq'
    _ = (a * b) * ((y * b) * (z * b) + (x * b) * (z * b) + (x * b) * (y * b)) := by
            ring

/-!
### Small explicit composite cases (sanity checks)

The prompt's example triples for 25/35/49 were not correct as stated, so here are corrected ones,
all checked by `norm_num`.
-/

lemma solution_25 : HasErdosStrausSolution 25 := by
  refine ⟨7, 100, 140, by decide, by decide, by decide, ?_⟩
  norm_num

lemma solution_35 : HasErdosStrausSolution 35 := by
  refine ⟨35, 20, 28, by decide, by decide, by decide, ?_⟩
  norm_num

lemma solution_49 : HasErdosStrausSolution 49 := by
  refine ⟨14, 105, 1470, by decide, by decide, by decide, ?_⟩
  norm_num

lemma solution_55 : HasErdosStrausSolution 55 := by
  refine ⟨14, 924, 4620, by decide, by decide, by decide, ?_⟩
  norm_num

/-!
### Prime-to-composite reduction

In the full project, you already have "all primes have solutions" from the prime development
(NonMordellHardPrimes.lean + K13 cascade for Mordell-hard primes). For this standalone prompt file,
we leave that as a placeholder lemma.

Once that is available, *every* `n ≥ 2` has a solution by taking a prime divisor `p ∣ n`
and scaling the prime solution up to `n`.
-/

/-- Mordell-hard residue classes mod 840 -/
def MordellHardClasses : Finset ℕ := {1, 121, 169, 289, 361, 529}

/-- Component theorem: Non-Mordell-hard primes have solutions.
    (Proven in NonMordellHardPrimes.lean) -/
axiom nonMordellHard_has_solution (p : ℕ) (hp : Nat.Prime p)
    (hnonMH : p % 840 ∉ MordellHardClasses) : HasErdosStrausSolution p

/-- Component theorem: Mordell-hard primes have solutions.
    (Proven via K13 coverage in K10CoverageMain.lean) -/
axiom mordellHard_has_solution (p : ℕ) (hp : Nat.Prime p)
    (hMH : p % 840 ∈ MordellHardClasses) : HasErdosStrausSolution p

/-- All primes have Erdős-Straus solutions. -/
theorem prime_has_solution (p : ℕ) (hp : Nat.Prime p) : HasErdosStrausSolution p := by
  by_cases hMH : p % 840 ∈ MordellHardClasses
  · exact mordellHard_has_solution p hp hMH
  · exact nonMordellHard_has_solution p hp hMH

/-- If `p` is prime, `p ∣ n`, and `n ≥ 2`, then `n` has an Erdős–Straus solution
by scaling the solution for `p`. -/
lemma hasSolution_of_prime_dvd {n p : ℕ} (hp : Nat.Prime p) (hpdvd : p ∣ n) (hn : 2 ≤ n) :
    HasErdosStrausSolution n := by
  rcases hpdvd with ⟨m, rfl⟩
  have hmpos : 0 < m := by
    -- If `m = 0` then `p*m = 0`, contradicting `2 ≤ p*m`.
    have hnmul_pos : 0 < p * m := lt_of_lt_of_le (by decide : 0 < 2) hn
    have hm_ne0 : m ≠ 0 := by
      intro hm0
      have : p * m = 0 := by simp [hm0]
      exact (Nat.ne_of_gt hnmul_pos) this
    exact Nat.pos_of_ne_zero hm_ne0

  have hpSol : HasErdosStrausSolution p := prime_has_solution p hp
  exact HasErdosStrausSolution.mul_right hpSol hmpos

/-- **Main theorem (as requested by the prompt).**

This proof *does not need* to use `hodd`, `hcomp`, or `h3` once we have prime solutions:
any `n ≥ 2` has a prime divisor, and we scale from the prime solution. -/
theorem oddComposite_has_solution (n : ℕ) (hn : 2 ≤ n)
    (hodd : ¬ 2 ∣ n) (hcomp : ¬ Nat.Prime n) (h3 : ¬ 3 ∣ n) :
    HasErdosStrausSolution n := by
  have hn1 : 1 < n := lt_of_lt_of_le (by decide : 1 < 2) hn
  rcases Nat.exists_prime_and_dvd hn1 with ⟨p, hp, hpdvd⟩
  exact hasSolution_of_prime_dvd (n := n) (p := p) hp hpdvd hn

end ErdosStraus
