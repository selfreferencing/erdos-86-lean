/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: ae90206e-1bbe-4717-8722-5693a5eefbeb

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>
-/

import Mathlib


/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

unexpected token '·'; expected command
unexpected token '·'; expected command-/
open Finset

def QR7  : Finset ℕ := {1,2,4}

def NQR7 : Finset ℕ := {3,5,6}

-- Useful: NQR membership implies not QR and not 0
lemma nqr_not_qr_and_ne0 {r : ℕ} (hr : r ∈ NQR7) : r ∉ QR7 ∧ r ≠ 0 := by
  have hr' : r = 3 ∨ r = 5 ∨ r = 6 := by
    simpa [NQR7] using hr
  rcases hr' with rfl | hr'
  · constructor
    · simp [QR7]
    · decide
  · rcases hr' with rfl | rfl
    · constructor
      · simp [QR7]
      · decide
    · constructor
      · simp [QR7]
      · decide

-- If r<7, r≠0, and r∉QR7, then r∈NQR7
lemma mod7_mem_NQR7_of_lt7 {r : ℕ} (hrlt : r < 7) (hr0 : r ≠ 0) (hrnot : r ∉ QR7) :
    r ∈ NQR7 := by
  interval_cases r using hrlt

· cases hr0 rfl
  · -- r=1
    exfalso
    exact hrnot (by simp [QR7])
  · -- r=2
    exfalso
    exact hrnot (by simp [QR7])
  · -- r=3
    simp [NQR7]
  · -- r=4
    exfalso
    exact hrnot (by simp [QR7])
  · -- r=5
    simp [NQR7]
  · -- r=6
    simp [NQR7]

-- 1) QR7 is multiplicatively closed mod 7
lemma qr7_mul_closed (a b : ℕ) (ha : a % 7 ∈ QR7) (hb : b % 7 ∈ QR7) :
    (a * b) % 7 ∈ QR7 := by
  have ha' : a % 7 = 1 ∨ a % 7 = 2 ∨ a % 7 = 4 := by
    simpa [QR7] using ha
  have hb' : b % 7 = 1 ∨ b % 7 = 2 ∨ b % 7 = 4 := by
    simpa [QR7] using hb

  rcases ha' with ha1 | ha24
  · rcases hb' with hb1 | hb24
    · have : ((1 * 1) % 7) ∈ QR7 := by decide
      simpa [Nat.mul_mod, ha1, hb1] using this
    · rcases hb24 with hb2 | hb4
      · have : ((1 * 2) % 7) ∈ QR7 := by decide
        simpa [Nat.mul_mod, ha1, hb2] using this
      · have : ((1 * 4) % 7) ∈ QR7 := by decide
        simpa [Nat.mul_mod, ha1, hb4] using this
  · rcases ha24 with ha2 | ha4
    · rcases hb' with hb1 | hb24
      · have : ((2 * 1) % 7) ∈ QR7 := by decide
        simpa [Nat.mul_mod, ha2, hb1] using this
      · rcases hb24 with hb2 | hb4
        · have : ((2 * 2) % 7) ∈ QR7 := by decide
          simpa [Nat.mul_mod, ha2, hb2] using this
        · have : ((2 * 4) % 7) ∈ QR7 := by decide
          simpa [Nat.mul_mod, ha2, hb4] using this
    · rcases hb' with hb1 | hb24
      · have : ((4 * 1) % 7) ∈ QR7 := by decide
        simpa [Nat.mul_mod, ha4, hb1] using this
      · rcases hb24 with hb2 | hb4
        · have : ((4 * 2) % 7) ∈ QR7 := by decide
          simpa [Nat.mul_mod, ha4, hb2] using this
        · have : ((4 * 4) % 7) ∈ QR7 := by decide
          simpa [Nat.mul_mod, ha4, hb4] using this

-- Strong-induction helper:
-- If n>0 and every prime divisor of n is QR mod 7, then n % 7 ∈ QR7.
lemma mod7_mem_QR7_of_primes_qr7 (n : ℕ) :
    0 < n →
    (∀ p, Nat.Prime p → p ∣ n → p % 7 ∈ QR7) →
    n % 7 ∈ QR7 := by
  classical
  refine Nat.strong_induction_on n
    (motive := fun n => 0 < n →
      (∀ p, Nat.Prime p → p ∣ n → p % 7 ∈ QR7) →
      n % 7 ∈ QR7) ?_
  intro n ih hn h
  by_cases h1 : n = 1
  · subst h1
    simp [QR7]
  · have hn1 : 1 < n := Nat.one_lt_iff_ne_zero_and_ne_one.2 ⟨Nat.ne_of_gt hn, h1⟩
    rcases Nat.exists_prime_and_dvd hn1 with ⟨p, hp, hpd⟩
    rcases hpd with ⟨m, rfl⟩
    have hmpos : 0 < m := by
      have hm0 : m ≠ 0 := by
        intro hm0
        have : p * m = 0 := by simp [hm0]
        exact (Nat.ne_of_gt hn) this
      exact Nat.pos_of_ne_zero hm0
    have hmlt : m < p * m := by
      have hp1 : 1 < p := hp.one_lt
      have : 1 * m < p * m := mul_lt_mul_of_pos_right hp1 hmpos
      simpa using this

    have hpqr : p % 7 ∈ QR7 := h p hp (Nat.dvd_mul_right p m)

    have hmprop : ∀ q, Nat.Prime q → q ∣ m → q % 7 ∈ QR7 := by
      intro q hq hqm
      apply h q hq
      exact dvd_trans hqm (by
        simpa [Nat.mul_comm] using Nat.dvd_mul_right m p)

    have hmqr : m % 7 ∈ QR7 := ih m hmlt hmpos hmprop
    exact qr7_mul_closed p m hpqr hmqr

-- 2) If all prime divisors of n are QR7, then every divisor of n^2 has residue in QR7 ∪ {0}.
lemma divisors_qr7_of_primes_qr7 (n : ℕ) (hn : 0 < n)
    (h : ∀ p, Nat.Prime p → p ∣ n → p % 7 ∈ QR7) :
    ∀ d, d ∣ n^2 → d % 7 ∈ QR7 ∪ {0} := by
  intro d hd
  classical
  have hn2pos : 0 < n^2 := by
    simpa [pow_two] using Nat.mul_pos hn hn
  have hn2ne : n^2 ≠ 0 := Nat.ne_of_gt hn2pos

  have hdne : d ≠ 0 := by
    intro hd0
    have : 0 ∣ n^2 := by simpa [hd0] using hd
    have : n^2 = 0 := by
      simpa [zero_dvd] using this
    exact hn2ne this

  have hdpos : 0 < d := Nat.pos_of_ne_zero hdne

  have hdprop : ∀ p, Nat.Prime p → p ∣ d → p % 7 ∈ QR7 := by
    intro p hp hpd
    apply h p hp
    have hpn2 : p ∣ n^2 := dvd_trans hpd hd
    exact hp.dvd_of_dvd_pow hpn2

  have hdqr : d % 7 ∈ QR7 :=
    mod7_mem_QR7_of_primes_qr7 d hdpos hdprop

  exact Finset.mem_union.2 (Or.inl hdqr)

-- 3) If n has an NQR7 prime factor, then n^2 has an NQR7 divisor (take d=p).
lemma exists_nqr7_divisor (n : ℕ)
    (h : ∃ p, Nat.Prime p ∧ p ∣ n ∧ p % 7 ∈ NQR7) :
    ∃ d, d ∣ n^2 ∧ d % 7 ∈ NQR7 := by
  rcases h with ⟨p, hp, hpn, hpmod⟩
  refine ⟨p, ?_, hpmod⟩
  have hn2 : n ∣ n^2 := by
    simpa [pow_two] using (Nat.dvd_mul_right n n)
  exact dvd_trans hpn hn2

-- 4) The target residue (-x mod 7) is always in NQR7 when x%7 ∈ QR7.
lemma target_is_nqr7 (x : ℕ) (hx : x % 7 ∈ QR7) :
    (7 - x % 7) % 7 ∈ NQR7 := by
  have hx' : x % 7 = 1 ∨ x % 7 = 2 ∨ x % 7 = 4 := by
    simpa [QR7] using hx
  rcases hx' with hx1 | hx24
  · simpa [hx1, NQR7]
  · rcases hx24 with hx2 | hx4
    · simpa [hx2, NQR7]
    · simpa [hx4, NQR7]

-- Helper: If x%7 ∈ QR7 and (x+d)%7=0, then d%7 ∈ NQR7.
-- (This is just case-bashing on x%7 ∈ {1,2,4} and d%7 ∈ {0..6}.)
lemma d_mod7_in_NQR7_of_x_QR7 (x d : ℕ) (hx : x % 7 ∈ QR7) (hxd : (x + d) % 7 = 0) :
    d % 7 ∈ NQR7 := by
  have hx' : x % 7 = 1 ∨ x % 7 = 2 ∨ x % 7 = 4 := by
    simpa [QR7] using hx
  have hadd : ((x % 7) + (d % 7)) % 7 = 0 := by
    simpa [Nat.add_mod] using hxd

  rcases hx' with hx1 | hx24
  · have hadd1 : (1 + d % 7) % 7 = 0 := by simpa [hx1] using hadd
    have hlt : d % 7 < 7 := Nat.mod_lt d (by decide)
    interval_cases hd : d % 7 using hlt

· exfalso
      have hEq : (1 + 0) % 7 = 0 := by simpa [hd] using hadd1
      have hNe : (1 + 0) % 7 ≠ 0 := by decide
      exact hNe hEq
    · exfalso
      have hEq : (1 + 1) % 7 = 0 := by simpa [hd] using hadd1
      have hNe : (1 + 1) % 7 ≠ 0 := by decide
      exact hNe hEq
    · exfalso
      have hEq : (1 + 2) % 7 = 0 := by simpa [hd] using hadd1
      have hNe : (1 + 2) % 7 ≠ 0 := by decide
      exact hNe hEq
    · exfalso
      have hEq : (1 + 3) % 7 = 0 := by simpa [hd] using hadd1
      have hNe : (1 + 3) % 7 ≠ 0 := by decide
      exact hNe hEq
    · exfalso
      have hEq : (1 + 4) % 7 = 0 := by simpa [hd] using hadd1
      have hNe : (1 + 4) % 7 ≠ 0 := by decide
      exact hNe hEq
    · exfalso
      have hEq : (1 + 5) % 7 = 0 := by simpa [hd] using hadd1
      have hNe : (1 + 5) % 7 ≠ 0 := by decide
      exact hNe hEq
    · simpa [NQR7, hd]
  · rcases hx24 with hx2 | hx4
    · have hadd2 : (2 + d % 7) % 7 = 0 := by simpa [hx2] using hadd
      have hlt : d % 7 < 7 := Nat.mod_lt d (by decide)
      interval_cases hd : d % 7 using hlt
      · exfalso
        have hEq : (2 + 0) % 7 = 0 := by simpa [hd] using hadd2
        have hNe : (2 + 0) % 7 ≠ 0 := by decide
        exact hNe hEq
      · exfalso
        have hEq : (2 + 1) % 7 = 0 := by simpa [hd] using hadd2
        have hNe : (2 + 1) % 7 ≠ 0 := by decide
        exact hNe hEq
      · exfalso
        have hEq : (2 + 2) % 7 = 0 := by simpa [hd] using hadd2
        have hNe : (2 + 2) % 7 ≠ 0 := by decide
        exact hNe hEq
      · exfalso
        have hEq : (2 + 3) % 7 = 0 := by simpa [hd] using hadd2
        have hNe : (2 + 3) % 7 ≠ 0 := by decide
        exact hNe hEq
      · exfalso
        have hEq : (2 + 4) % 7 = 0 := by simpa [hd] using hadd2
        have hNe : (2 + 4) % 7 ≠ 0 := by decide
        exact hNe hEq
      · simpa [NQR7, hd]
      · exfalso
        have hEq : (2 + 6) % 7 = 0 := by simpa [hd] using hadd2
        have hNe : (2 + 6) % 7 ≠ 0 := by decide
        exact hNe hEq
    · have hadd4 : (4 + d % 7) % 7 = 0 := by simpa [hx4] using hadd
      have hlt : d % 7 < 7 := Nat.mod_lt d (by decide)
      interval_cases hd : d % 7 using hlt
      · exfalso
        have hEq : (4 + 0) % 7 = 0 := by simpa [hd] using hadd4
        have hNe : (4 + 0) % 7 ≠ 0 := by decide
        exact hNe hEq
      · exfalso
        have hEq : (4 + 1) % 7 = 0 := by simpa [hd] using hadd4
        have hNe : (4 + 1) % 7 ≠ 0 := by decide
        exact hNe hEq
      · exfalso
        have hEq : (4 + 2) % 7 = 0 := by simpa [hd] using hadd4
        have hNe : (4 + 2) % 7 ≠ 0 := by decide
        exact hNe hEq
      · simpa [NQR7, hd]
      · exfalso
        have hEq : (4 + 4) % 7 = 0 := by simpa [hd] using hadd4
        have hNe : (4 + 4) % 7 ≠ 0 := by decide
        exact hNe hEq
      · exfalso
        have hEq : (4 + 5) % 7 = 0 := by simpa [hd] using hadd4
        have hNe : (4 + 5) % 7 ≠ 0 := by decide
        exact hNe hEq
      · exfalso
        have hEq : (4 + 6) % 7 = 0 := by simpa [hd] using hadd4
        have hNe : (4 + 6) % 7 ≠ 0 := by decide
        exact hNe hEq

-- What *is* provable in general from the above machinery:
-- Witness ⇒ ∃ NQR7 prime factor.
-- NOTE: The REVERSE direction is FALSE in general (counterexample: x₁=9)
-- But this direction suffices for our obstruction proof.
theorem k1_witness_imp (x₁ : ℕ) (hx : 0 < x₁) (hx_qr : x₁ % 7 ∈ QR7) :
    (∃ d, d ∣ x₁^2 ∧ d ≤ x₁ ∧ (x₁ + d) % 7 = 0) →
    (∃ p, Nat.Prime p ∧ p ∣ x₁ ∧ p % 7 ∈ NQR7) := by
  intro hw
  classical
  rcases hw with ⟨d, hddiv, hdle, hmod⟩
  have hd_nqr : d % 7 ∈ NQR7 :=
    d_mod7_in_NQR7_of_x_QR7 x₁ d hx_qr hmod

  have hnotAll : ¬ (∀ p, Nat.Prime p → p ∣ x₁ → p % 7 ∈ QR7) := by
    intro hall
    have hd_qr0 : d % 7 ∈ QR7 ∪ ({0} : Finset ℕ) :=
      divisors_qr7_of_primes_qr7 x₁ hx hall d hddiv
    have hd_qr_or0 : d % 7 ∈ QR7 ∨ d % 7 = 0 := by
      simpa [Finset.mem_union, Finset.mem_singleton] using hd_qr0
    have hd_not : d % 7 ∉ QR7 ∧ d % 7 ≠ 0 :=
      nqr_not_qr_and_ne0 hd_nqr
    cases hd_qr_or0 with
    | inl hdqr => exact (hd_not.1 hdqr).elim
    | inr hd0  => exact (hd_not.2 hd0).elim

  have hEx : ∃ p, Nat.Prime p ∧ p ∣ x₁ ∧ p % 7 ∉ QR7 := by
    have := hnotAll
    push_neg at this
    simpa using this
  rcases hEx with ⟨p, hp, hpx, hpnot⟩

  have hx0 : x₁ % 7 ≠ 0 := by
    intro hx0
    have : 0 ∈ QR7 := by simpa [hx0] using hx_qr
    simpa [QR7] using this

  have hp0 : p % 7 ≠ 0 := by
    intro hp0
    have hp7 : 7 ∣ p := Nat.dvd_of_mod_eq_zero hp0
    have hx7 : 7 ∣ x₁ := dvd_trans hp7 hpx
    have : x₁ % 7 = 0 := Nat.mod_eq_zero_of_dvd hx7
    exact hx0 this

  have hp_nqr : p % 7 ∈ NQR7 :=
    mod7_mem_NQR7_of_lt7 (r := p % 7) (Nat.mod_lt p (by decide)) hp0 hpnot
  exact ⟨p, hp, hpx, hp_nqr⟩