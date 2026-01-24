import Mathlib

namespace ErdosStraus

/-- The set `K10 = {5, 7, 9, 11, 14, 17, 19, 23, 26, 29}` as a `Finset ℕ`. -/
def K10 : Finset ℕ := {5, 7, 9, 11, 14, 17, 19, 23, 26, 29}

/-!
## 1) GCD coupling lemma

`gcd(r+a, r+b) ∣ |a-b|` for integers `r a b`.
-/

/--
GCD coupling lemma: any common divisor of `r+a` and `r+b` divides their difference `a-b`,
hence divides `|a-b|`.
-/
lemma gcd_shift_divides_diff (r a b : ℤ) :
    (Int.gcd (r + a) (r + b)) ∣ |a - b| := by
  -- Let `g = gcd(r+a, r+b)` (a natural number).
  set g : ℕ := Int.gcd (r + a) (r + b)

  -- `g` (viewed in `ℤ`) divides both arguments.
  have hg₁ : (g : ℤ) ∣ (r + a) := by
    simpa [g] using (Int.gcd_dvd_left (r + a) (r + b))
  have hg₂ : (g : ℤ) ∣ (r + b) := by
    simpa [g] using (Int.gcd_dvd_right (r + a) (r + b))

  -- Therefore `g` divides their difference `(r+a) - (r+b) = a-b`.
  have hg_sub : (g : ℤ) ∣ (a - b) := by
    have : (g : ℤ) ∣ (r + a) - (r + b) := dvd_sub hg₁ hg₂
    have hlin : (r + a) - (r + b) = a - b := by ring
    simpa [hlin] using this

  -- Convert `ℤ`-divisibility to `ℕ`-divisibility of the absolute value:
  -- if `a-b = g*t`, then `|a-b| = g * |t|`.
  rcases hg_sub with ⟨t, ht⟩
  refine ⟨|t|, ?_⟩
  -- Taking absolute values; `simp` uses `Int.abs_mul` and `Int.abs_ofNat`.
  -- The goal is in `ℕ` because `|·|` on `ℤ` is `Int.abs : ℤ → ℕ`.
  simpa [ht, Int.abs_mul]

/-!
## 2) Prime corollary: a prime `p > 24` divides at most one shift `r+k` with `k ∈ K10`.
-/

/-- Membership in `K10` unfolds to a finite disjunction of equalities. -/
lemma mem_K10_cases {n : ℕ} (hn : n ∈ K10) :
    n = 5 ∨ n = 7 ∨ n = 9 ∨ n = 11 ∨ n = 14 ∨
    n = 17 ∨ n = 19 ∨ n = 23 ∨ n = 26 ∨ n = 29 := by
  simpa [K10] using hn

/-- If `a,b ∈ K10` then `|a-b| ≤ 24` (as an integer absolute value, hence a `ℕ`). -/
lemma abs_sub_le_24_of_mem_K10 {a b : ℕ} (ha : a ∈ K10) (hb : b ∈ K10) :
    |((a : ℤ) - (b : ℤ))| ≤ 24 := by
  -- Brute-force over the 10×10 possibilities; `decide` finishes each numeric inequality.
  rcases mem_K10_cases ha with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  rcases mem_K10_cases hb with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  decide

/--
If `p > 24` is prime, then it cannot divide two distinct shifts `r+a` and `r+b`
with `a,b ∈ K10`.
-/
lemma prime_divides_at_most_one_shift (r : ℤ) (p : ℕ) (hp : Nat.Prime p) (hp24 : p > 24)
    (a b : ℕ) (ha : a ∈ K10) (hb : b ∈ K10) (hab : a ≠ b)
    (hpa : (p : ℤ) ∣ r + a) (hpb : (p : ℤ) ∣ r + b) : False := by
  -- From `p ∣ (r+a)` and `p ∣ (r+b)`, we get `p ∣ (a-b)` by subtraction.
  have hdiv_diff : (p : ℤ) ∣ ((a : ℤ) - (b : ℤ)) := by
    have h : (p : ℤ) ∣ (r + (a : ℤ)) - (r + (b : ℤ)) := dvd_sub hpa hpb
    have hlin : (r + (a : ℤ)) - (r + (b : ℤ)) = (a : ℤ) - (b : ℤ) := by ring
    simpa [hlin] using h

  -- Hence `p ∣ |a-b|` in `ℕ` (since `|·|` on `ℤ` returns `ℕ`).
  have hp_abs : p ∣ |((a : ℤ) - (b : ℤ))| := by
    rcases hdiv_diff with ⟨t, ht⟩
    refine ⟨|t|, ?_⟩
    -- `simp` turns `|p*t|` into `p*|t|`.
    simpa [ht, Int.abs_mul]

  -- But `|a-b| ≤ 24` for `a,b ∈ K10`, hence `|a-b| < p` since `p > 24`.
  have hle : |((a : ℤ) - (b : ℤ))| ≤ 24 := abs_sub_le_24_of_mem_K10 ha hb
  have hlt : |((a : ℤ) - (b : ℤ))| < p := lt_of_le_of_lt hle hp24

  -- A prime cannot divide a smaller positive number; thus `|a-b| = 0`.
  have hn_eq_zero : |((a : ℤ) - (b : ℤ))| = 0 := by
    by_contra hn0
    have hp_le : p ≤ |((a : ℤ) - (b : ℤ))| :=
      hp.le_of_dvd (Nat.pos_of_ne_zero hn0) hp_abs
    exact (not_le_of_lt hlt) hp_le

  -- `|a-b| = 0` implies `a = b`, contradicting `hab`.
  have hzero : ((a : ℤ) - (b : ℤ)) = 0 := by
    exact (Int.abs_eq_zero.mp hn_eq_zero)
  have hab' : (a : ℤ) = (b : ℤ) := sub_eq_zero.mp hzero
  have : a = b := by
    exact_mod_cast hab'
  exact hab this

end ErdosStraus
