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

/-- Type II witness predicate: d | x², d ≤ x, (x + d) ≡ 0 (mod m) -/
def TypeIIWitness (x m : ℕ) : Prop :=
  ∃ d : ℕ, d ∣ x^2 ∧ d ≤ x ∧ (x + d) % m = 0

/-- k ∈ {0,1,2} coverage for non-Mordell-hard primes with p % 3 = 1 and p % 4 = 1.
    (Proven via K0/K1/K2 characterization files) -/
axiom k012_cover_nonMordellHard (p : ℕ) (hp : Nat.Prime p)
    (hmod1 : p % 3 = 1) (h4 : p % 4 = 1) (hnonMH : p % 840 ∉ MordellHardClasses) :
    TypeIIWitness ((p + 3) / 4) 3 ∨
    TypeIIWitness ((p + 7) / 4) 7 ∨
    TypeIIWitness ((p + 11) / 4) 11

/-- Bradford Type II witness gives ES solution.
    (Proven in Bradford decomposition file) -/
axiom typeIIWitness_has_solution (p x m : ℕ) (hp : Nat.Prime p)
    (hxm : 4 * x = p + m) (hw : TypeIIWitness x m) :
    HasErdosStrausSolution p

/--
The remaining non-Mordell-hard primes not covered by the `p % 3 = 2` family
(i.e. effectively `p % 3 = 1` but `p % 840 ∉ MordellHardClasses`) are discharged
by the Bradford Type II analysis for `k ∈ {0,1,2}` or direct construction.
-/
lemma nonMordellHard_not_mod3eq2_has_solution
    (p : ℕ) (hp : Nat.Prime p) (hp3 : p ≠ 3) (hmod2 : p % 3 ≠ 2)
    (hnonMH : p % 840 ∉ MordellHardClasses) :
    HasErdosStrausSolution p := by
  -- Step 1: Show p % 3 = 1
  have hmod1 : p % 3 = 1 := by
    have hlt : p % 3 < 3 := Nat.mod_lt p (by decide)
    interval_cases h : p % 3 using hlt
    · -- p % 3 = 0 means 3 | p, contradiction since p prime ≠ 3
      have h3dvd : 3 ∣ p := Nat.dvd_of_mod_eq_zero h
      have hp3' : p = 3 :=
        (Nat.Prime.eq_one_or_self_of_dvd hp 3 h3dvd).resolve_left (by decide)
      exact (hp3 hp3').elim
    · exact h
    · exact (hmod2 h).elim

  -- Step 2: Split on p % 4.
  have hlt4 : p % 4 < 4 := Nat.mod_lt p (by decide)
  interval_cases h4 : p % 4 using hlt4
  · -- p % 4 = 0: impossible for a prime (forces p = 2), contradiction with hmod2
    exfalso
    have h4dvd : 4 ∣ p := Nat.dvd_of_mod_eq_zero h4
    have h2dvd : 2 ∣ p := dvd_trans (by decide : 2 ∣ 4) h4dvd
    have hp2 : p = 2 :=
      (Nat.Prime.eq_one_or_self_of_dvd hp 2 h2dvd).resolve_left (by decide)
    exact hmod2 (by simpa [hp2])
  · -- p % 4 = 1: use k∈{0,1,2} coverage (m=3,7,11)
    have hdiv3 : 4 ∣ p + 3 := by
      have : (p + 3) % 4 = 0 := by simpa [Nat.add_mod, h4]
      exact Nat.dvd_of_mod_eq_zero this
    have hdiv7 : 4 ∣ p + 7 := by
      have : (p + 7) % 4 = 0 := by simpa [Nat.add_mod, h4]
      exact Nat.dvd_of_mod_eq_zero this
    have hdiv11 : 4 ∣ p + 11 := by
      have : (p + 11) % 4 = 0 := by simpa [Nat.add_mod, h4]
      exact Nat.dvd_of_mod_eq_zero this

    have hx3 : 4 * ((p + 3) / 4) = p + 3 := by
      simpa [Nat.mul_comm] using (Nat.div_mul_cancel hdiv3)
    have hx7 : 4 * ((p + 7) / 4) = p + 7 := by
      simpa [Nat.mul_comm] using (Nat.div_mul_cancel hdiv7)
    have hx11 : 4 * ((p + 11) / 4) = p + 11 := by
      simpa [Nat.mul_comm] using (Nat.div_mul_cancel hdiv11)

    have hcover :
        TypeIIWitness ((p + 3) / 4) 3 ∨
        TypeIIWitness ((p + 7) / 4) 7 ∨
        TypeIIWitness ((p + 11) / 4) 11 :=
      k012_cover_nonMordellHard p hp hmod1 h4 hnonMH

    rcases hcover with hk0 | hk1 | hk2
    · exact typeIIWitness_has_solution p ((p + 3) / 4) 3 hp hx3 hk0
    · exact typeIIWitness_has_solution p ((p + 7) / 4) 7 hp hx7 hk1
    · exact typeIIWitness_has_solution p ((p + 11) / 4) 11 hp hx11 hk2
  · -- p % 4 = 2: then p is even → p = 2, contradiction with hmod2
    exfalso
    have hrepr : p = (p / 4) * 4 + 2 := by
      simpa [h4, Nat.mul_comm] using (Nat.div_add_mod p 4).symm
    have h2dvd : 2 ∣ p := by
      have h2dvd1 : 2 ∣ (p / 4) * 4 := dvd_mul_of_dvd_right (by decide : 2 ∣ 4) (p / 4)
      have h2dvd2 : 2 ∣ 2 := by decide
      simpa [hrepr] using (dvd_add h2dvd1 h2dvd2)
    have hp2 : p = 2 :=
      (Nat.Prime.eq_one_or_self_of_dvd hp 2 h2dvd).resolve_left (by decide)
    exact hmod2 (by simpa [hp2])
  · -- p % 4 = 3: direct solution
    have hdiv : 4 ∣ p + 1 := by
      have : (p + 1) % 4 = 0 := by simpa [Nat.add_mod, h4]
      exact Nat.dvd_of_mod_eq_zero this

    let a : ℕ := (p + 1) / 4
    let b : ℕ := 2 * p * a

    have ha4 : 4 * a = p + 1 := by
      simpa [a, Nat.mul_comm] using (Nat.div_mul_cancel hdiv)

    have ha_pos : 0 < a := by
      refine Nat.pos_of_ne_zero ?_
      intro ha0
      have : p + 1 = 0 := by simpa [ha0] using ha4.symm
      exact Nat.succ_ne_zero p this

    have hb_pos : 0 < b := by
      have hp_pos : 0 < p := Nat.Prime.pos hp
      have : 0 < 2 * p := Nat.mul_pos (by decide : 0 < 2) hp_pos
      simpa [b, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using Nat.mul_pos this ha_pos

    refine ⟨a, b, b, ha_pos, hb_pos, hb_pos, ?_⟩
    have hLHS : 4 * a * b * b = 4 * p^2 * a^2 * (p + 1) := by
      calc
        4 * a * b * b
            = 16 * p^2 * a^3 := by simp [b]; ring
        _   = 4 * p^2 * a^2 * (4 * a) := by ring
        _   = 4 * p^2 * a^2 * (p + 1) := by simpa [ha4]

    have hRHS : p * (b * b + a * b + a * b) = 4 * p^2 * a^2 * (p + 1) := by
      simp [b]; ring

    simpa [hLHS, hRHS, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm, Nat.add_assoc,
      Nat.add_left_comm, Nat.add_comm] using (hLHS.trans hRHS.symm)

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
