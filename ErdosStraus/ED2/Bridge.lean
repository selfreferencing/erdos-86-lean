/-
  ED2 Bridge Lemmas
  =================

  Bridge lemmas connecting ED2 parameters to the ESC Type III formula.

  Key results:
  - typeIIeq_to_type3Z: The Type II equation implies Type III works
  - ED2Params → type3_works: ED2 parameters yield valid Type III solution
-/

import Mathlib.Data.Int.ModEq
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic

namespace ED2

/-! ## Type III in ℤ

Working in ℤ avoids Nat.sub issues and makes algebraic manipulation easier.
-/

/-- Type III solution predicate (integer version) -/
def type3Z_works (p offset c : ℤ) : Prop :=
  offset % 4 = 3 ∧
  0 < c ∧
  let d : ℤ := (4*c - 1) * offset - p
  0 < d ∧
  d ∣ (p + offset) * c * p

/-- Decidable instance for type3Z_works -/
instance (p offset c : ℤ) : Decidable (type3Z_works p offset c) := by
  unfold type3Z_works
  infer_instance

/-! ## Bridge 1: Type II Equation → Type III

The algebraic identity:
  (p + offset)(b + c) = 4 * offset * b * c
implies type3Z_works p offset b.

This is pure algebra: from the Type II Diophantine equation,
we derive the divisibility condition for Type III.
-/

/-- The Type II equation implies Type III works -/
theorem typeIIeq_to_type3Z
    (p offset b c : ℤ)
    (hoff : offset % 4 = 3)
    (hp : 0 < p) (ho : 0 < offset) (hb : 0 < b) (hc : 0 < c)
    (h : (p + offset) * (b + c) = 4 * offset * b * c) :
    type3Z_works p offset b := by
  unfold type3Z_works
  refine ⟨hoff, hb, ?_, ?_⟩
  · -- d > 0 where d = (4*b - 1) * offset - p
    -- Key identity: ((4b-1)*offset - p)*(b+c) = offset*(4*b²)
    have hbc : 0 < b + c := by linarith
    have h_prod : ((4 * b - 1) * offset - p) * (b + c) = offset * (4 * b ^ 2) := by
      linear_combination -h
    have h_rhs_pos : 0 < offset * (4 * b ^ 2) := by positivity
    by_contra hle
    push_neg at hle
    have : ((4 * b - 1) * offset - p) * (b + c) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hle (le_of_lt hbc)
    linarith
  · -- d | (p + offset) * b * p
    -- Key identity: (p+offset)*b = ((4b-1)*offset - p)*c
    have h_factor : (p + offset) * b = ((4 * b - 1) * offset - p) * c := by
      linear_combination h
    exact ⟨c * p, by linear_combination p * h_factor⟩

/-! ## Type III ℕ ↔ ℤ Equivalence

Showing that type3_works on ℕ corresponds to type3Z_works on ℤ.
-/

/-- Type III formula (natural number version, matches ESC_TypeII_Prime_Covering) -/
def type3_works (p offset c : ℕ) : Prop :=
  offset % 4 = 3 ∧
  c > 0 ∧
  let d := (4 * c - 1) * offset - p
  d > 0 ∧
  d ∣ (p + offset) * c * p

/-- Decidable instance for type3_works -/
instance (p offset c : ℕ) : Decidable (type3_works p offset c) := by
  unfold type3_works
  infer_instance

/-- type3_works on ℕ implies type3Z_works on ℤ -/
theorem type3_nat_to_int {p offset c : ℕ}
    (h : type3_works p offset c) :
    type3Z_works (p : ℤ) (offset : ℤ) (c : ℤ) := by
  unfold type3_works at h
  unfold type3Z_works
  obtain ⟨hmod, hc_pos, hd_pos, hd_dvd⟩ := h
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- offset % 4 = 3 in ℤ
    exact_mod_cast hmod
  · -- 0 < (c : ℤ)
    exact_mod_cast hc_pos
  · -- 0 < (4*c - 1)*offset - p in ℤ
    -- In ℕ, d = (4*c-1)*offset - p > 0, so (4*c-1)*offset > p
    -- Since d > 0 in ℕ (with truncated sub), we know (4*c-1)*offset ≥ p + 1
    have h_ge : (4 * c - 1) * offset ≥ p + 1 := by omega
    have hc1 : 1 ≤ 4 * c := by omega
    have : (4 * (c : ℤ) - 1) * (offset : ℤ) - (p : ℤ) > 0 := by
      have : (4 * c - 1) * offset ≥ p + 1 := h_ge
      zify [hc1] at this; linarith
    exact this
  · -- d ∣ (p + offset) * c * p in ℤ
    -- In ℕ: (4*c-1)*offset - p | (p + offset) * c * p
    -- Need to show ℤ version
    have h_ge : p ≤ (4 * c - 1) * offset := by omega
    -- The ℕ subtraction equals the ℤ subtraction when the ℕ sub is positive
    have hc1 : 1 ≤ 4 * c := by omega
    have h_eq : ((((4 * c - 1) * offset - p : ℕ) : ℤ)) = (4 * (c : ℤ) - 1) * (offset : ℤ) - (p : ℤ) := by
      zify [h_ge, hc1]
    -- Lift the ℕ product equation
    have h_prod : (((p + offset) * c * p : ℕ) : ℤ) = ((p : ℤ) + (offset : ℤ)) * (c : ℤ) * (p : ℤ) := by
      push_cast; ring
    obtain ⟨k, hk⟩ := hd_dvd
    exact ⟨(k : ℤ), by rw [← h_eq, ← h_prod]; exact_mod_cast hk⟩

/-- type3Z_works on ℤ with positive values implies type3_works on ℕ -/
theorem type3_int_to_nat {p offset c : ℕ}
    (hp : 0 < p) (ho : 0 < offset) (hc : 0 < c)
    (h : type3Z_works (p : ℤ) (offset : ℤ) (c : ℤ)) :
    type3_works p offset c := by
  unfold type3Z_works at h
  unfold type3_works
  obtain ⟨hmod, hc_pos, hd_pos, hd_dvd⟩ := h
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- offset % 4 = 3 in ℕ
    exact_mod_cast hmod
  · -- c > 0
    exact hc
  · -- (4*c - 1)*offset - p > 0 in ℕ
    -- We know (4*(c:ℤ) - 1)*(offset:ℤ) - (p:ℤ) > 0
    -- Since c ≥ 1, we have 4*c ≥ 4 > 1, so 4*c - 1 ≥ 1 in ℕ
    have hc1 : 1 ≤ 4 * c := by omega
    -- The ℤ positivity tells us (4*c-1)*offset > p in ℤ
    have h_ineq : (p : ℤ) < (4 * (c : ℤ) - 1) * (offset : ℤ) := by linarith
    -- Convert back to ℕ
    have h_ge : p < (4 * c - 1) * offset := by
      zify [hc1]
      linarith
    omega
  · -- (4*c - 1)*offset - p | (p + offset)*c*p in ℕ
    have hc1 : 1 ≤ 4 * c := by omega
    have h_ge : p ≤ (4 * c - 1) * offset := by
      have : (p : ℤ) < (4 * (c : ℤ) - 1) * (offset : ℤ) := by linarith
      zify [hc1]; linarith
    -- Equate ℕ and ℤ expressions
    have h_eq : ((((4 * c - 1) * offset - p : ℕ) : ℤ)) = (4 * (c : ℤ) - 1) * (offset : ℤ) - (p : ℤ) := by
      zify [h_ge, hc1]
    have h_prod : (((p + offset) * c * p : ℕ) : ℤ) = ((p : ℤ) + (offset : ℤ)) * (c : ℤ) * (p : ℤ) := by
      push_cast; ring
    -- Extract divisor from ℤ
    obtain ⟨k, hk⟩ := hd_dvd
    -- k must be non-negative since both d and product are positive
    have hd_pos_nat : 0 < (4 * c - 1) * offset - p := by
      zify [h_ge, hc1]; linarith
    have h_prod_eq : ((p : ℤ) + (offset : ℤ)) * (c : ℤ) * (p : ℤ) = ((((4 * c - 1) * offset - p : ℕ) : ℤ)) * k := by
      rw [h_eq]; exact hk
    have hk_nonneg : 0 ≤ k := by
      by_contra hk_neg
      push_neg at hk_neg
      have h1 : ((p : ℤ) + (offset : ℤ)) * (c : ℤ) * (p : ℤ) > 0 := by positivity
      have h2 : ((((4 * c - 1) * offset - p : ℕ) : ℤ)) > 0 := by exact_mod_cast hd_pos_nat
      have h3 : ((((4 * c - 1) * offset - p : ℕ) : ℤ)) * k < 0 := by
        exact mul_neg_of_pos_of_neg h2 hk_neg
      linarith
    -- Now convert k to ℕ
    obtain ⟨kn, rfl⟩ := Int.eq_ofNat_of_zero_le hk_nonneg
    exact ⟨kn, by exact_mod_cast h_prod_eq⟩

/-! ## ED2 Parameters Structure

ED2-admissible parameters encode a solution to the core identity:
  A * (4*b*c - b - c) = p * (b*c)

This corresponds to the Egyptian fraction 4/p = 1/A + 1/(b*p) + 1/(c*p).
-/

/-- ED2-admissible parameters for prime p -/
structure ED2Params (p : ℕ) where
  δ : ℕ      -- offset parameter
  b : ℕ      -- first denominator factor
  c : ℕ      -- second denominator factor
  A : ℕ      -- the x in 4/p = 1/x + ...
  -- Core Diophantine identity:
  ed2_id : (A : ℤ) * (4*b*c - b - c) = (p : ℤ) * (b*c)
  -- Offset-A relationship: δ = 4A - p (in ℤ, since 4A > p)
  hδA : (δ : ℤ) = 4 * (A : ℤ) - (p : ℤ)
  -- Positivity constraints
  hb : b > 0
  hc : c > 0
  hA : A > 0
  hδ : δ > 0
  -- Offset constraint (δ ≡ 3 mod 4)
  hδ_mod : δ % 4 = 3

/-! ## Bridge 2: ED2Params → type3_works

From ED2 parameters, extract a valid Type III solution.
-/

/-- ED2 parameters yield a Type III solution -/
theorem type3_of_ed2 (p : ℕ) (hp : 0 < p) (params : ED2Params p) :
    ∃ offset c : ℕ, type3_works p offset c := by
  use params.δ, params.b
  apply type3_int_to_nat hp params.hδ params.hb
  -- Show type3Z_works p δ b in ℤ via typeIIeq_to_type3Z
  apply typeIIeq_to_type3Z (p : ℤ) (params.δ : ℤ) (params.b : ℤ) (params.c : ℤ)
      (by exact_mod_cast params.hδ_mod)
  · exact_mod_cast hp
  · exact_mod_cast params.hδ
  · exact_mod_cast params.hb
  · exact_mod_cast params.hc
  · -- Need: (↑p + ↑δ)*(↑b + ↑c) = 4*↑δ*↑b*↑c
    -- From ed2_id: A*(4bc - b - c) = p*bc  and  hδA: δ = 4A - p
    -- So p + δ = 4A, hence (p+δ)*(b+c) = 4A*(b+c) = 4*(A*(b+c))
    -- From ed2_id: A*(4bc - b - c) = p*bc means A*4bc - A*(b+c) = p*bc
    -- So A*(b+c) = A*4bc - p*bc = (4A - p)*bc = δ*bc
    -- Hence (p+δ)*(b+c) = 4A*(b+c) = 4*δ*bc = 4*δ*b*c ✓
    have h_id := params.ed2_id
    have h_dA := params.hδA
    -- Derive: (↑p + ↑δ) = 4 * ↑A
    have h_sum : (p : ℤ) + (params.δ : ℤ) = 4 * (params.A : ℤ) := by linarith
    -- Derive: ↑A * (↑b + ↑c) = ↑δ * ↑b * ↑c
    -- From h_id: A*(4bc - b - c) = p*bc, i.e., 4*A*bc - A*(b+c) = p*bc
    -- So A*(b+c) = (4*A - p)*bc = δ*bc
    have h_abc : (params.A : ℤ) * ((params.b : ℤ) + (params.c : ℤ)) = (params.δ : ℤ) * (params.b : ℤ) * (params.c : ℤ) := by
      linear_combination -h_id - (params.b : ℤ) * (params.c : ℤ) * h_dA
    -- Now: (p + δ)*(b + c) = 4*A*(b+c) = 4*δ*b*c
    linear_combination ((params.b : ℤ) + (params.c : ℤ)) * h_sum + 4 * h_abc

end ED2
