import ErdosStraus.Basic
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Nat.Factors
import Mathlib.Tactic

namespace ErdosStraus

/-- Helper: if every element of a list is `≡ 1 (mod 3)`, then so is the product. -/
lemma prod_mod3_eq_one_of_all_one (l : List ℕ) (h : ∀ a ∈ l, a % 3 = 1) :
    l.prod % 3 = 1 := by
  induction l with
  | nil =>
      simp
  | cons a l ih =>
      have ha : a % 3 = 1 := h a (by simp)
      have hl : ∀ b ∈ l, b % 3 = 1 := by
        intro b hb
        exact h b (by simp [hb])
      -- `(a * l.prod) % 3 = ((a%3) * (l.prod%3)) % 3`
      simp [List.prod_cons, Nat.mul_mod, ha, ih hl]

/-- If `n ≡ 2 (mod 3)`, then some prime factor of `n` is `≡ 2 (mod 3)`.

This is the key number-theoretic fact behind the `k=0` criterion.
-/
lemma exists_primeFactor_mod3_eq_two (n : ℕ) (hn : n % 3 = 2) :
    ∃ q : ℕ, q ∈ n.primeFactorsList ∧ q % 3 = 2 := by
  classical
  by_contra h
  have hn0 : n ≠ 0 := by
    intro hn0
    simpa [hn0] using hn
  have hn3 : ¬ (3 ∣ n) := by
    intro h3
    have : n % 3 = 0 := Nat.mod_eq_zero_of_dvd h3
    simpa [this] using hn

  -- Every prime factor q of n has q%3=1
  have hall1 : ∀ q ∈ n.primeFactorsList, q % 3 = 1 := by
    intro q hq
    have hqprime : Nat.Prime q := Nat.prime_of_mem_primeFactorsList hq
    have hqdvn : q ∣ n := Nat.dvd_of_mem_primeFactorsList hq

    have hqnot2 : q % 3 ≠ 2 := by
      intro h2
      apply h
      exact ⟨q, hq, h2⟩

    have hqnot0 : q % 3 ≠ 0 := by
      intro h0
      have h3dq : 3 ∣ q := Nat.dvd_of_mod_eq_zero h0
      -- Prime q and 3|q => q=3
      have hqeq : q = 3 := by
        have := (Nat.dvd_prime hqprime).1 h3dq
        rcases this with h31 | h3q
        · cases (by decide : (3:ℕ) ≠ 1) h31
        · exact h3q.symm
      have : 3 ∣ n := by
        simpa [hqeq] using hqdvn
      exact hn3 this

    -- Now q%3 is one of {0,1,2}; exclude 0 and 2.
    have hlt : q % 3 < 3 := Nat.mod_lt q (by decide : 0 < 3)
    -- Use `interval_cases` to split r = q%3 into 0,1,2.
    interval_cases hr : q % 3 using hlt
    · cases hqnot0 hr
    · exact hr
    · cases hqnot2 hr

  have hprod1 : n.primeFactorsList.prod % 3 = 1 :=
    prod_mod3_eq_one_of_all_one n.primeFactorsList hall1
  have hprod_eq : n.primeFactorsList.prod = n := by
    simpa using Nat.prod_primeFactorsList hn0
  have : n % 3 = 1 := by
    simpa [hprod_eq] using hprod1
  simpa [this] using hn

/-- The **k=0 characterization** in its local (x-only) form.

Let `m=3`. In the Mordell-hard situation one has `x ≡ 1 (mod 3)`, so
`d ≡ -x (mod 3)` becomes `d ≡ 2 (mod 3)`.

This lemma isolates the *pure arithmetic* fact:

`∃ d ∣ x^2` with `d ≤ x` and `d ≡ 2 (mod 3)`
iff
`x` has a prime divisor `q ≡ 2 (mod 3)`.
-/
theorem k0_local_iff (x : ℕ) (hxpos : 0 < x) :
    (∃ d : ℕ, d ∣ x^2 ∧ d ≤ x ∧ d % 3 = 2)
      ↔ (∃ q : ℕ, Nat.Prime q ∧ q ∣ x ∧ q % 3 = 2) := by
  constructor
  · rintro ⟨d, hd, hdle, hdmod⟩
    have hdpos : 0 < d := by
      -- d%3=2 implies d≠0
      have : d ≠ 0 := by
        intro h0
        simpa [h0] using hdmod
      exact Nat.pos_of_ne_zero this

    -- Pick a prime factor q of d with q%3=2
    obtain ⟨q, hqmem, hqmod⟩ := exists_primeFactor_mod3_eq_two d (by simpa [hdmod])
    have hqprime : Nat.Prime q := Nat.prime_of_mem_primeFactorsList hqmem
    have hqdvd_d : q ∣ d := Nat.dvd_of_mem_primeFactorsList hqmem

    -- q divides x^2 because q|d and d|x^2
    have hqdvd_x2 : q ∣ x^2 := dvd_trans hqdvd_d hd

    -- q divides x (prime divides a square)
    have hqdvd_x : q ∣ x := by
      have hmul : q ∣ x * x := by
        simpa [pow_two] using hqdvd_x2
      have : q ∣ x ∨ q ∣ x := hqprime.dvd_of_dvd_mul hmul
      exact this.elim (fun h => h) (fun h => h)

    exact ⟨q, hqprime, hqdvd_x, hqmod⟩

  · rintro ⟨q, hqprime, hqdvd_x, hqmod⟩
    refine ⟨q, ?_, ?_, hqmod⟩
    · -- q | x^2
      have : q ∣ x * x := by
        exact dvd_mul_of_dvd_left hqdvd_x x
      simpa [pow_two] using this
    · -- q ≤ x (since q|x and x>0)
      exact Nat.le_of_dvd hxpos hqdvd_x

end ErdosStraus
