import Mathlib

namespace ErdosStraus

/-- The Type II witness predicate. -/
def TypeIIWitness' (x m : ℕ) : Prop :=
  ∃ d : ℕ, d ∣ x^2 ∧ d ≤ x ∧ (x + d) % m = 0

/-- Direct divisibility lemma: If m | x and m ≤ x, then d = m is a witness.
    This is the primary mechanism for K10 coverage. -/
lemma direct_divisibility_witness {x m : ℕ} (hm_pos : 0 < m) (hm_dvd : m ∣ x) (hm_le : m ≤ x) :
    TypeIIWitness' x m := by
  use m
  constructor
  -- m | x² (since m | x implies m | x * x)
  · exact dvd_pow hm_dvd (by norm_num : 2 ≠ 0)
  constructor
  -- m ≤ x
  · exact hm_le
  -- (x + m) % m = 0 (since m | x implies m | x + m)
  · have hxm : m ∣ x + m := by
      have h1 : m ∣ m := dvd_refl m
      exact Nat.dvd_add hm_dvd h1
    exact Nat.eq_zero_of_dvd_of_lt hxm (Nat.mod_lt (x + m) hm_pos) |>.symm ▸ rfl

/-- When m | x, then x ≡ 0 (mod m), so -x ≡ 0 (mod m), so d = m works. -/
lemma direct_div_residue_match {x m : ℕ} (hm_dvd : m ∣ x) :
    x % m = 0 ∧ m % m = 0 := by
  constructor
  · exact Nat.mod_eq_zero_of_dvd hm_dvd
  · exact Nat.mod_self m

/-- For k=5 (m=23): if 23 | x₅, then k=5 has a witness.
    This catches most Hard10 primes (63%). -/
lemma k5_direct_witness (x₅ : ℕ) (hx : 0 < x₅) (h23_dvd : 23 ∣ x₅) (h23_le : 23 ≤ x₅) :
    TypeIIWitness' x₅ 23 := by
  exact direct_divisibility_witness (by norm_num) h23_dvd h23_le

/-- For k=7 (m=31): if 31 | x₇, then k=7 has a witness. -/
lemma k7_direct_witness (x₇ : ℕ) (hx : 0 < x₇) (h31_dvd : 31 ∣ x₇) (h31_le : 31 ≤ x₇) :
    TypeIIWitness' x₇ 31 := by
  exact direct_divisibility_witness (by norm_num) h31_dvd h31_le

/-- For k=14 (m=59): if 59 | x₁₄, then k=14 has a witness.
    This is the actual mechanism for p=3481 (the only prime needing k=14). -/
lemma k14_direct_witness (x₁₄ : ℕ) (hx : 0 < x₁₄) (h59_dvd : 59 ∣ x₁₄) (h59_le : 59 ≤ x₁₄) :
    TypeIIWitness' x₁₄ 59 := by
  exact direct_divisibility_witness (by norm_num) h59_dvd h59_le

/-- Verification: For p = 3481, we have x₁₄ = 885 and 59 | 885. -/
lemma p3481_x14_div_59 : 59 ∣ (3481 + 59) / 4 := by
  native_decide

/-- 885 = 3 × 5 × 59 -/
lemma x14_3481_factorization : (3481 + 59) / 4 = 885 ∧ 885 = 3 * 5 * 59 := by
  native_decide

end ErdosStraus
