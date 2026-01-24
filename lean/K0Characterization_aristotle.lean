/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 90f13eff-4927-4ad6-9f80-496878b40156

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>
-/

import Mathlib


open Nat

/-- Helper: if all prime divisors of `n` satisfy `p % 3 = 1`, then `n % 3 = 1`. -/
lemma mod3_eq_one_of_primes_mod3 (n : ℕ) (hn : 0 < n)
    (h : ∀ p, Nat.Prime p → p ∣ n → p % 3 = 1) :
    n % 3 = 1 := by
  classical
  let P : ℕ → Prop := fun n =>
    ∀ hn : 0 < n, (∀ p, Nat.Prime p → p ∣ n → p % 3 = 1) → n % 3 = 1
  have hP : ∀ n, (∀ m, m < n → P m) → P n := by
    intro n ih hn hfac
    cases n with
    | zero =>
        cases hn
    | succ n =>
        cases n with
        | zero =>
            -- n = 1
            simp
        | succ n =>
            -- n = succ (succ n) ≥ 2
            have hNgt1 : 1 < Nat.succ (Nat.succ n) := by
              exact Nat.succ_lt_succ (Nat.succ_pos n)
            obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd hNgt1
            rcases hpdvd with ⟨m, rfl⟩
            have hpm_pos : 0 < p * m := lt_trans Nat.zero_lt_one hNgt1
            have hmpos : 0 < m := by
              have hm_dvd : m ∣ p * m := by
                refine ⟨p, by simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]⟩
              exact Nat.pos_of_dvd_of_pos hm_dvd hpm_pos
            have hp1 : 1 < p := hp.one_lt
            have hm_lt : m < p * m := by
              have : m * 1 < m * p := mul_lt_mul_of_pos_left hp1 hmpos
              simpa [Nat.mul_one, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using this
            have hmP : P m := ih m hm_lt
            have hm_mod : m % 3 = 1 := by
              refine hmP hmpos ?_
              intro q hq hq_dvd_m
              apply hfac q hq
              rcases hq_dvd_m with ⟨t, rfl⟩
              refine ⟨p * t, by simp [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]⟩
            have hp_mod : p % 3 = 1 := by
              apply hfac p hp
              exact ⟨m, rfl⟩
            calc
              (p * m) % 3 = ((p % 3) * (m % 3)) % 3 := by
                simpa [Nat.mul_mod]
              _ = (1 * 1) % 3 := by simp [hp_mod, hm_mod]
              _ = 1 := by decide
  have hAll : P n := Nat.strong_induction_on n hP
  exact hAll hn h

lemma divisors_mod3_of_primes_mod3 (n : ℕ) (hn : 0 < n)
    (h : ∀ p, Nat.Prime p → p ∣ n → p % 3 = 1) :
    ∀ d, d ∣ n^2 → d % 3 = 1 := by
  intro d hd
  have hn2pos : 0 < n^2 := by
    have : 0 < n * n := Nat.mul_pos hn hn
    simpa [pow_two] using this
  have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hd hn2pos
  have h' : ∀ p, Nat.Prime p → p ∣ d → p % 3 = 1 := by
    intro p hp hpd
    have hpn2 : p ∣ n^2 := dvd_trans hpd hd
    have hpn : p ∣ n := hp.dvd_of_dvd_pow hpn2
    exact h p hp hpn
  exact mod3_eq_one_of_primes_mod3 d hdpos h'

lemma exists_divisor_mod3_2 (n : ℕ) (hn : 0 < n)
    (h : ∃ p, Nat.Prime p ∧ p ∣ n ∧ p % 3 = 2) :
    ∃ d, d ∣ n^2 ∧ d % 3 = 2 := by
  rcases h with ⟨p, hp, hpn, hpmod⟩
  refine ⟨p, ?_, hpmod⟩
  rcases hpn with ⟨t, rfl⟩
  refine ⟨t * (p * t), by
    simp [pow_two, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]⟩

theorem k0_witness_iff (x₀ : ℕ) (hx : 0 < x₀) (hx_mod : x₀ % 3 = 1) :
    (∃ d, d ∣ x₀^2 ∧ d ≤ x₀ ∧ (x₀ + d) % 3 = 0) ↔
    (∃ p, Nat.Prime p ∧ p ∣ x₀ ∧ p % 3 = 2) := by
  classical
  constructor
  · intro hw
    rcases hw with ⟨d, hd_dvd, _hd_le, hsum⟩
    -- From `x₀ % 3 = 1` and `(x₀ + d) % 3 = 0`, we get `d % 3 = 2`.
    have hd_mod : d % 3 = 2 := by
      have hsum' : ((x₀ % 3) + (d % 3)) % 3 = 0 := by
        simpa [Nat.add_mod] using hsum
      have hsum'' : (1 + (d % 3)) % 3 = 0 := by
        simpa [hx_mod] using hsum'
      have hlt : d % 3 < 3 := Nat.mod_lt d (by decide)
      interval_cases hrd : d % 3 using hlt