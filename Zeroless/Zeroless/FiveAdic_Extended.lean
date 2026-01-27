/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: f685d570-f951-49ad-afbc-64fef25230e5

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem s_eq_three (k : ℕ) (hk : k ≥ 1) :
    (m k : ZMod (5^(k+1))) = 1 + 3 * 5^k
-/

/-
  Zeroless/FiveAdic_Extended.lean
  Extended 5-adic Infrastructure with full four_or_five_children proof

  This file contains the complete proof of the "4-or-5 Children Theorem"
  which is the key combinatorial result for the survivor dynamics.
-/

import Mathlib

namespace Zeroless

open scoped BigOperators

/-! ## Basic Definitions (duplicated from FiveAdic.lean for standalone verification) -/

/-- Period for k trailing zeroless digits: T_k = 4 · 5^(k-1) -/
def T (k : ℕ) : ℕ := 4 * 5^(k-1)

/-- The 5-adic state: u_{k+1}(n) = 2^{n-k-1} mod 5^{k+1} -/
noncomputable def u (k : ℕ) (n : ℕ) : ZMod (5^(k+1)) :=
  (2 : ZMod (5^(k+1)))^(n-k-1)

/-- The multiplier: m_k = 2^{T_k} mod 5^{k+1} -/
noncomputable def m (k : ℕ) : ZMod (5^(k+1)) :=
  (2 : ZMod (5^(k+1)))^(T k)

/-- The top digit of u: the coefficient of 5^k in the 5-adic expansion -/
def top_digit (k : ℕ) (u : ZMod (5^(k+1))) : Fin 5 :=
  ⟨u.val / 5^k, by
    have hu : u.val < 5^k * 5 := by
      simpa [pow_succ] using (u.val_lt : u.val < (5 : ℕ)^(k+1))
    exact Nat.div_lt_of_lt_mul hu⟩

/-- A state u survives at level k if its top digit is nonzero -/
def survives (k : ℕ) (u : ZMod (5^(k+1))) : Prop :=
  (top_digit k u).val ≠ 0

/-- Specifically: s_k = 3 for all k (the expansion coefficient is constant) -/
theorem s_eq_three (k : ℕ) (hk : k ≥ 1) :
    (m k : ZMod (5^(k+1))) = 1 + 3 * 5^k := by
  -- We'll use that $2^{T_k} \equiv 1 + 3 \cdot 5^k \pmod{5^{k+1}}$.
  have h_cong : 2 ^ (4 * 5 ^ (k - 1)) ≡ 1 + 3 * 5 ^ k [MOD 5 ^ (k + 1)] := by
    -- We proceed by induction on $k$.
    induction' k with k ih;
    · contradiction;
    · rcases k with ( _ | k ) <;> simp_all +decide [ Nat.modEq_iff_dvd ];
      obtain ⟨ m, hm ⟩ := ih;
      -- We can rewrite $2^{4 \cdot 5^{k+1}}$ as $(2^{4 \cdot 5^k})^5$ and apply the binomial theorem.
      have h_binom : (2 ^ (4 * 5 ^ (k + 1)) : ℤ) = (1 + 3 * 5 ^ (k + 1) - 5 ^ (k + 2) * m) ^ 5 := by
        rw [ ← hm ] ; ring;
      rw [ h_binom ] ; ring_nf;
      refine' dvd_add _ _;
      · refine' dvd_add _ _;
        · refine' dvd_add _ _;
          · refine' dvd_add _ _;
            · refine' dvd_add _ _;
              · refine' dvd_add _ _;
                · refine' dvd_add _ _;
                  · refine' dvd_add _ _;
                    · refine' dvd_add _ _;
                      · exact ⟨ m + m * 5 ^ k * 60 + m * 5 ^ ( k * 2 ) * 1350 + m * 5 ^ ( k * 3 ) * 13500 + m * 5 ^ ( k * 4 ) * 50625, by ring ⟩;
                      · exact ⟨ -m ^ 2 * 5 ^ k * 50 - m ^ 2 * 5 ^ ( k * 2 ) * 2250, by ring ⟩;
                    · exact ⟨ -m ^ 2 * 5 ^ ( k * 3 ) * 33750 - m ^ 2 * 5 ^ ( k * 4 ) * 168750, by ring ⟩;
                  · exact ⟨ m ^ 3 * 5 ^ ( k * 2 ) * 1250, by ring ⟩;
                · exact ⟨ m ^ 3 * 5 ^ ( k * 3 ) * 37500, by ring ⟩;
              · exact ⟨ m ^ 3 * 5 ^ ( k * 4 ) * 281250, by ring ⟩;
            · exact ⟨ -m ^ 4 * 5 ^ ( k * 3 ) * 15625 - m ^ 4 * 5 ^ ( k * 4 ) * 234375, by ring ⟩;
          · exact ⟨ m ^ 5 * 5 ^ ( k * 4 ) * 78125, by ring ⟩;
        · exact ⟨ -5 ^ k * 18 - 5 ^ ( k * 2 ) * 270, by ring ⟩;
      · exact ⟨ -5 ^ ( k * 3 ) * 2025 - 5 ^ ( k * 4 ) * 6075, by ring ⟩;
  erw [ ← ZMod.natCast_eq_natCast_iff ] at * ; norm_num at * ; aesop;

-- Proved by Aristotle in FiveAdic.lean

/-! ## Auxiliary lemmas for the digit computation -/

/-- If a^2 = 0 in a commutative semiring, then (1+a)^n = 1 + n*a -/
private lemma one_add_pow_of_sq_zero
    {R : Type*} [CommSemiring R] (a : R) (ha : a^2 = 0) (n : ℕ) :
    (1 + a)^n = 1 + (n : R) * a := by
  induction n with
  | zero => simp
  | succ n ih =>
      have haa : a * a = 0 := by simpa [pow_two] using ha
      calc
        (1 + a)^(Nat.succ n) = (1 + a)^n * (1 + a) := by simp [pow_succ]
        _ = (1 + (n : R) * a) * (1 + a) := by simpa [ih]
        _ = (1 + (n : R) * a) + (1 + (n : R) * a) * a := by simp [mul_add]
        _ = (1 + (n : R) * a) + (a + (n : R) * a * a) := by simp [add_mul, mul_assoc]
        _ = (1 + (n : R) * a) + a := by simp [haa, mul_assoc]
        _ = 1 + ((n : R) * a + a) := by ac_rfl
        _ = 1 + (Nat.succ n : R) * a := by
            simp [Nat.cast_succ, add_mul, one_mul, add_assoc, add_comm, add_left_comm]

/-- 5 * 5^k = 0 in ZMod (5^(k+1)) -/
lemma five_q_zero (k : ℕ) :
    (5 : ZMod (5^(k+1))) * (5^k : ZMod (5^(k+1))) = 0 := by
  have hmul : (5 * 5^k : ℕ) = 5^(k+1) := by
    simpa [pow_succ] using (Nat.mul_comm (5 : ℕ) (5^k))
  have hdvd : (5^(k+1) : ℕ) ∣ (5 * 5^k : ℕ) := by
    simpa [hmul] using (dvd_refl (5^(k+1)))
  have hcast : ((5 * 5^k : ℕ) : ZMod (5^(k+1))) = 0 := by
    exact (ZMod.natCast_zmod_eq_zero_iff_dvd (a := 5 * 5^k) (b := 5^(k+1))).2 hdvd
  simpa [Nat.cast_mul] using hcast

/-- (5^k)^2 = 0 in ZMod (5^(k+1)) when k ≥ 1 -/
lemma q_sq_zero (k : ℕ) (hk : k ≥ 1) :
    (5^k : ZMod (5^(k+1))) * (5^k : ZMod (5^(k+1))) = 0 := by
  have hle : k + 1 ≤ k + k := by omega
  have hdvd : (5^(k+1) : ℕ) ∣ (5^k * 5^k : ℕ) := by
    simpa [pow_add] using (Nat.pow_dvd_pow 5 hle)
  have hcast : ((5^k * 5^k : ℕ) : ZMod (5^(k+1))) = 0 := by
    exact (ZMod.natCast_zmod_eq_zero_iff_dvd (a := 5^k * 5^k) (b := 5^(k+1))).2 hdvd
  simpa [Nat.cast_mul] using hcast

/-- (3 * 5^k)^2 = 0 in ZMod (5^(k+1)) when k ≥ 1 -/
private lemma three_mul_pow_k_sq_zero (k : ℕ) (hk : k ≥ 1) :
    ((3 : ZMod (5^(k+1))) * (5^k : ZMod (5^(k+1))))^2 = 0 := by
  have hqq := q_sq_zero k hk
  calc ((3 : ZMod (5^(k+1))) * (5^k : ZMod (5^(k+1))))^2
      = 9 * ((5^k : ZMod (5^(k+1))) * (5^k : ZMod (5^(k+1)))) := by ring
    _ = 9 * 0 := by rw [hqq]
    _ = 0 := by ring

/-- (m k)^j = 1 + j * 3 * 5^k in ZMod (5^(k+1)) -/
lemma m_pow_eq (k : ℕ) (hk : k ≥ 1) (j : ℕ) :
    (m k : ZMod (5^(k+1)))^j = 1 + (j : ZMod (5^(k+1))) * 3 * (5^k : ZMod (5^(k+1))) := by
  rw [s_eq_three k hk]
  have hsq := three_mul_pow_k_sq_zero k hk
  have h := one_add_pow_of_sq_zero ((3 : ZMod (5^(k+1))) * (5^k : ZMod (5^(k+1)))) hsq j
  simpa [mul_assoc] using h

/-- The product u * (m k)^j in ZMod (5^(k+1)) equals lo + b * q -/
lemma product_zmod_eq (k : ℕ) (hk : k ≥ 1) (u : ZMod (5^(k+1))) (j : ℕ) :
    let q := 5^k
    let hi := u.val / q
    let lo := u.val % q
    let b := (hi + lo * j * 3) % 5
    u * (m k : ZMod (5^(k+1)))^j =
      (lo : ZMod (5^(k+1))) + (b : ZMod (5^(k+1))) * (q : ZMod (5^(k+1))) := by
  classical
  dsimp
  set q : ℕ := 5^k with hq
  set hi : ℕ := u.val / q with hhi
  set lo : ℕ := u.val % q with hlo
  set a : ℕ := hi + lo * j * 3 with ha
  set b : ℕ := a % 5 with hb
  -- Bridge between (5 : ZMod ...)^k and ↑q (= Nat.cast q)
  have hcast5k : (5 : ZMod (5^(k+1)))^k = (q : ZMod (5^(k+1))) := by
    rw [hq]; push_cast; ring
  have hm :
      (m k : ZMod (5^(k+1)))^j =
      1 + (j : ZMod (5^(k+1))) * 3 * (q : ZMod (5^(k+1))) := by
    have h := m_pow_eq k hk j; rw [hcast5k] at h; exact h
  have hqq : (q : ZMod (5^(k+1))) * (q : ZMod (5^(k+1))) = 0 := by
    have h := q_sq_zero k hk; rw [hcast5k] at h; exact h
  have h5q : (5 : ZMod (5^(k+1))) * (q : ZMod (5^(k+1))) = 0 := by
    have h := five_q_zero k; rw [hcast5k] at h; exact h
  have huval : (u.val : ZMod (5^(k+1))) = u := ZMod.natCast_zmod_val u
  have hdiv : u.val = q * hi + lo := by
    simpa [hhi.symm, hlo.symm] using (Nat.div_add_mod u.val q).symm
  have hu : u = (lo : ZMod (5^(k+1))) + (hi : ZMod (5^(k+1))) * (q : ZMod (5^(k+1))) := by
    calc
      u = (u.val : ZMod (5^(k+1))) := by simpa using huval.symm
      _ = ((q * hi + lo : ℕ) : ZMod (5^(k+1))) := by simpa [hdiv]
      _ = (lo : ZMod (5^(k+1))) + (hi : ZMod (5^(k+1))) * (q : ZMod (5^(k+1))) := by
          simp [Nat.cast_add, Nat.cast_mul]
          ring
  have hmain :
      u * (m k : ZMod (5^(k+1)))^j =
      (lo : ZMod (5^(k+1))) + (a : ZMod (5^(k+1))) * (q : ZMod (5^(k+1))) := by
    have hcoef :
        (a : ZMod (5^(k+1))) =
        (hi : ZMod (5^(k+1))) + (lo : ZMod (5^(k+1))) * (j : ZMod (5^(k+1))) * 3 := by
      simp [ha, Nat.cast_add, Nat.cast_mul, mul_assoc, mul_left_comm, mul_comm]
    have hterm :
        (hi : ZMod (5^(k+1))) * (q : ZMod (5^(k+1))) *
            ((j : ZMod (5^(k+1))) * 3 * (q : ZMod (5^(k+1)))) = 0 := by
      calc
        (hi : ZMod (5^(k+1))) * (q : ZMod (5^(k+1))) *
            ((j : ZMod (5^(k+1))) * 3 * (q : ZMod (5^(k+1))))
            =
            (hi : ZMod (5^(k+1))) * (j : ZMod (5^(k+1))) * 3 *
              ((q : ZMod (5^(k+1))) * (q : ZMod (5^(k+1)))) := by
              ring
        _ = 0 := by simp [hqq]
    calc
      u * (m k : ZMod (5^(k+1)))^j
          = u * (1 + (j : ZMod (5^(k+1))) * 3 * (q : ZMod (5^(k+1)))) := by
              simpa [hm]
      _ = u + u * ((j : ZMod (5^(k+1))) * 3 * (q : ZMod (5^(k+1)))) := by ring
      _ = ((lo : ZMod (5^(k+1))) + (hi : ZMod (5^(k+1))) * (q : ZMod (5^(k+1)))) +
            (((lo : ZMod (5^(k+1))) + (hi : ZMod (5^(k+1))) * (q : ZMod (5^(k+1)))) *
              ((j : ZMod (5^(k+1))) * 3 * (q : ZMod (5^(k+1))))) := by
              simpa [hu]
      _ = (lo : ZMod (5^(k+1))) + (hi : ZMod (5^(k+1))) * (q : ZMod (5^(k+1))) +
            (lo : ZMod (5^(k+1))) * ((j : ZMod (5^(k+1))) * 3 * (q : ZMod (5^(k+1)))) +
            (hi : ZMod (5^(k+1))) * (q : ZMod (5^(k+1))) *
              ((j : ZMod (5^(k+1))) * 3 * (q : ZMod (5^(k+1)))) := by
              ring
      _ = (lo : ZMod (5^(k+1))) + (hi : ZMod (5^(k+1))) * (q : ZMod (5^(k+1))) +
            (lo : ZMod (5^(k+1))) * ((j : ZMod (5^(k+1))) * 3 * (q : ZMod (5^(k+1)))) := by
              simp [hterm]
      _ = (lo : ZMod (5^(k+1))) +
            ((hi : ZMod (5^(k+1))) + (lo : ZMod (5^(k+1))) * (j : ZMod (5^(k+1))) * 3) *
              (q : ZMod (5^(k+1))) := by
              ring
      _ = (lo : ZMod (5^(k+1))) + (a : ZMod (5^(k+1))) * (q : ZMod (5^(k+1))) := by
              simpa [hcoef.symm]
  have haq :
      (a : ZMod (5^(k+1))) * (q : ZMod (5^(k+1))) =
      (b : ZMod (5^(k+1))) * (q : ZMod (5^(k+1))) := by
    have hadecomp : a = (a / 5) * 5 + b := by
      simpa [Nat.mul_comm, hb.symm] using (Nat.div_add_mod a 5).symm
    -- Rewrite ↑a using the decomposition
    have ha_cast : (a : ZMod (5^(k+1))) =
        ((a / 5 : ℕ) : ZMod (5^(k+1))) * 5 + (b : ZMod (5^(k+1))) := by
      conv_lhs => rw [show a = (a / 5) * 5 + b from hadecomp]
      push_cast; ring
    calc
      (a : ZMod (5^(k+1))) * (q : ZMod (5^(k+1)))
          = (((a / 5 : ℕ) : ZMod (5^(k+1))) * 5 + (b : ZMod (5^(k+1)))) *
            (q : ZMod (5^(k+1))) := by rw [ha_cast]
      _ = ((a / 5 : ℕ) : ZMod (5^(k+1))) * (5 * (q : ZMod (5^(k+1)))) +
            (b : ZMod (5^(k+1))) * (q : ZMod (5^(k+1))) := by ring
      _ = (b : ZMod (5^(k+1))) * (q : ZMod (5^(k+1))) := by simp [h5q]
  calc
    u * (m k : ZMod (5^(k+1)))^j
      = (lo : ZMod (5^(k+1))) + (a : ZMod (5^(k+1))) * (q : ZMod (5^(k+1))) := hmain
    _ = (lo : ZMod (5^(k+1))) + (b : ZMod (5^(k+1))) * (q : ZMod (5^(k+1))) := by
        simpa using congrArg (fun x => (lo : ZMod (5^(k+1))) + x) haq

/-- If lo < q, then (lo + b * q) / q = b -/
lemma nat_add_mul_div (lo q b : ℕ) (hlo : lo < q) (hq : 0 < q) :
    (lo + b * q) / q = b := by
  rw [Nat.add_mul_div_right lo b hq, Nat.div_eq_of_lt hlo, zero_add]

/-- Casting a small natural to ZMod preserves its value -/
lemma val_of_small_nat (k : ℕ) (lo b : ℕ) (hlo : lo < 5^k) (hb : b < 5) :
    ((lo + b * 5^k : ℕ) : ZMod (5^(k+1))).val = lo + b * 5^k := by
  have hb4 : b ≤ 4 := Nat.lt_succ_iff.mp (by simpa using hb)
  have hmul : b * 5^k ≤ 4 * 5^k := Nat.mul_le_mul_right (5^k) hb4
  have hle : lo + b * 5^k ≤ lo + 4 * 5^k := Nat.add_le_add_left hmul lo
  have hlt₁ : lo + 4 * 5^k < 5^k + 4 * 5^k := Nat.add_lt_add_right hlo (4 * 5^k)
  have hlt₂ : lo + b * 5^k < 5^k + 4 * 5^k := lt_of_le_of_lt hle hlt₁
  have hbound : 5^k + 4 * 5^k = 5^(k+1) := by
    calc
      5^k + 4 * 5^k = 5 * 5^k := by ring
      _ = 5^(k+1) := by
        calc
          5 * 5^k = 5^k * 5 := by simpa [Nat.mul_comm]
          _ = 5^(k+1) := by simpa [pow_succ]
  have hlt : lo + b * 5^k < 5^(k+1) := lt_of_lt_of_eq hlt₂ hbound
  rw [ZMod.val_natCast]
  exact Nat.mod_eq_of_lt hlt

/-- For b < 5: b ≠ 0 ↔ (b : ZMod 5) ≠ 0 -/
lemma ne_zero_iff_cast_ne_zero (b : ℕ) (hb : b < 5) :
    b ≠ 0 ↔ (b : ZMod 5) ≠ 0 := by
  have h0 : ((b : ZMod 5) = 0) ↔ b = 0 := by
    constructor
    · intro hbz
      have hdvd : (5 : ℕ) ∣ b := by
        exact (ZMod.natCast_zmod_eq_zero_iff_dvd b 5).1 (by simpa using hbz)
      rcases hdvd with ⟨c, rfl⟩
      cases c with
      | zero => simp
      | succ c =>
        have hge : 5 ≤ 5 * Nat.succ c := by
          have : (1 : ℕ) ≤ Nat.succ c := Nat.succ_le_succ (Nat.zero_le c)
          simpa using (Nat.mul_le_mul_left 5 this)
        exfalso
        exact (not_lt_of_ge hge hb)
    · intro hb0
      subst hb0
      simp
  exact (not_congr h0).symm

/-- The mod-5 coefficient cast to ZMod 5 equals the digit function -/
lemma mod_cast_eq_digit (hi lo j : ℕ) :
    (((hi + lo * j * 3) % 5 : ℕ) : ZMod 5) =
      (hi : ZMod 5) + ((lo % 5 : ℕ) : ZMod 5) * (3 : ZMod 5) * (j : ZMod 5) := by
  have cast_mod5 : ∀ a : ℕ, ((a % 5 : ℕ) : ZMod 5) = (a : ZMod 5) := by
    intro a
    rw [← Nat.mod_add_div a 5]
    push_cast
    simp [show (5 : ZMod 5) = 0 from by decide]
  rw [cast_mod5 (hi + lo * j * 3), cast_mod5 lo]
  push_cast
  ring

/-! ## The 4-or-5 Children Theorem (Full Proof) -/

open Classical in
/-- A survivor has exactly 4 or 5 children that also survive.
    This is the "4-or-5 Children Theorem". -/
theorem four_or_five_children (k : ℕ) (hk : k ≥ 1) (u : ZMod (5^(k+1)))
    (hu : survives k u) :
    (Finset.filter (fun j : Fin 5 => survives k (u * (m k)^j.val)) Finset.univ).card ∈ ({4, 5} : Set ℕ) := by
  classical

  -- Convenient shorthands (Nat)
  let q : ℕ := 5^k
  let N : ℕ := 5^(k+1)

  -- hi/lo decomposition of u.val
  let hi : ℕ := u.val / q
  let lo : ℕ := u.val % q

  have hhi_lt5 : hi < 5 := by
    -- top_digit's bound is exactly this
    simpa [top_digit, q, hi] using (top_digit k u).isLt

  have hhi_ne0 : hi ≠ 0 := by
    -- hu : (top_digit k u).val ≠ 0, but (top_digit k u).val = u.val / q
    simpa [survives, top_digit, q, hi] using hu

  -- The digit-affine map over ZMod 5 that governs survival of children.
  let digit : Fin 5 → ZMod 5 :=
    fun j => (hi : ZMod 5) + ((lo % 5 : ℕ) : ZMod 5) * (3 : ZMod 5) * (j.val : ZMod 5)

  -- Predicate of surviving child
  let P : Fin 5 → Prop := fun j => survives k (u * (m k)^j.val)

  --------------------------------------------------------------------
  -- The single "hard" arithmetic lemma: connect survives ↔ digit ≠ 0.
  -- Everything below is pure finite-field/Finset counting.
  --------------------------------------------------------------------
  have hdigit_iff (j : Fin 5) : P j ↔ digit j ≠ 0 := by
    -- Assembled from micro-lemmas C1-C5 + Lemma A + Lemma B
    have hq_pos : 0 < q := Nat.pos_of_ne_zero (by positivity)
    have hlo_lt : lo < q := Nat.mod_lt u.val hq_pos
    let b : ℕ := (hi + lo * j.val * 3) % 5
    have hb_lt5 : b < 5 := Nat.mod_lt _ (by decide)
    -- Step 1: ZMod equality (from product_zmod_eq / C2)
    have hprod : u * (m k : ZMod (5^(k+1)))^j.val =
        (lo : ZMod (5^(k+1))) + (b : ZMod (5^(k+1))) * (q : ZMod (5^(k+1))) :=
      product_zmod_eq k hk u j.val
    -- Step 2: Compute .val of the product (using val_of_small_nat / C3)
    have hcast : (lo : ZMod (5^(k+1))) + (b : ZMod (5^(k+1))) * (q : ZMod (5^(k+1))) =
        ((lo + b * q : ℕ) : ZMod (5^(k+1))) := by push_cast; ring
    have hval : (u * (m k : ZMod (5^(k+1)))^j.val).val = lo + b * q := by
      rw [hprod, hcast]
      exact val_of_small_nat k lo b hlo_lt hb_lt5
    -- Step 3: Division gives b (from nat_add_mul_div / Lemma A)
    have hdiv : (u * (m k : ZMod (5^(k+1)))^j.val).val / q = b := by
      rw [hval]; exact nat_add_mul_div lo q b hlo_lt hq_pos
    -- Step 4: Connect P j to b ≠ 0
    have hP_b : P j ↔ b ≠ 0 := by
      have key : (top_digit k (u * (m k)^j.val)).val = b := by
        show (u * (m k)^j.val).val / 5^k = b
        exact hdiv
      show survives k (u * (m k)^j.val) ↔ b ≠ 0
      unfold survives
      rw [key]
    -- Step 5: b ≠ 0 ↔ (b : ZMod 5) ≠ 0 (from ne_zero_iff_cast_ne_zero / C4)
    have hb_cast := ne_zero_iff_cast_ne_zero b hb_lt5
    -- Step 6: (b : ZMod 5) = digit j (from mod_cast_eq_digit / C5)
    have hb_digit : (b : ZMod 5) = digit j :=
      mod_cast_eq_digit hi lo j.val
    -- Combine: P j ↔ b ≠ 0 ↔ (b : ZMod 5) ≠ 0 ↔ digit j ≠ 0
    exact hP_b.trans (hb_cast.trans (by rw [hb_digit]))

  --------------------------------------------------------------------
  -- Case split on whether the "step" (lo % 5) is zero.
  --------------------------------------------------------------------
  by_cases hlo0 : lo % 5 = 0
  · -- Step is 0: digit is constant = hi, so every child survives.
    have hconst : ∀ j : Fin 5, digit j = (hi : ZMod 5) := by
      intro j
      simp [digit, hlo0, mul_assoc, mul_left_comm, mul_comm]

    -- show (hi : ZMod 5) ≠ 0 from hi ≠ 0 and hi < 5
    have hhi5_ne : (hi : ZMod 5) ≠ 0 := by
      intro h0
      have hdvd : 5 ∣ hi := by
        simpa using (ZMod.natCast_zmod_eq_zero_iff_dvd hi 5).1 h0
      have : hi = 0 := by
        have hlt : hi < 5 := hhi_lt5
        exact Nat.eq_zero_of_dvd_of_lt hdvd hlt
      exact hhi_ne0 this

    have hall : ∀ j : Fin 5, P j := by
      intro j
      have : digit j ≠ 0 := by simpa [hconst j] using hhi5_ne
      exact (hdigit_iff j).2 this

    have hfilter : Finset.filter P Finset.univ = Finset.univ := by
      ext j
      simp [Finset.mem_filter, hall j]

    have hcard : (Finset.filter P Finset.univ).card = 5 := by
      simp [hfilter]

    rw [hcard]; right; rfl
  · -- Step is nonzero: digit is a non-constant affine map over the field ZMod 5,
    -- so it has exactly one zero, hence exactly 4 survivors.
    have hlo5_ne : ((lo % 5 : ℕ) : ZMod 5) ≠ 0 := by
      intro h0
      have hdvd : 5 ∣ lo % 5 := by
        simpa using (ZMod.natCast_zmod_eq_zero_iff_dvd (lo % 5) 5).1 h0
      have : lo % 5 = 0 := by
        have hlt : lo % 5 < 5 := Nat.mod_lt lo (by decide)
        exact Nat.eq_zero_of_dvd_of_lt hdvd hlt
      exact hlo0 this

    haveI : Fact (Nat.Prime 5) := ⟨by decide⟩

    let step5 : ZMod 5 := ((lo % 5 : ℕ) : ZMod 5) * (3 : ZMod 5)
    have hstep_ne : step5 ≠ 0 := by
      -- 3 ≠ 0 in ZMod 5, and lo%5 ≠ 0 by assumption
      have h3 : (3 : ZMod 5) ≠ 0 := by
          intro h
          have : 5 ∣ (3 : ℕ) := by
            have := (ZMod.natCast_zmod_eq_zero_iff_dvd 3 5).mp
            exact this (by exact_mod_cast h)
          omega
      exact mul_ne_zero hlo5_ne h3

    -- Unique root j0 of digit j = 0 is j0 = -(hi)/step5.
    let hi5 : ZMod 5 := (hi : ZMod 5)
    let j0z : ZMod 5 := (-hi5) * step5⁻¹
    let j0 : Fin 5 := ⟨j0z.val, j0z.val_lt⟩

    have hj0z_cast : (j0.val : ZMod 5) = j0z := by
      simpa [j0] using (ZMod.natCast_val j0z)

    have hj0_zero : digit j0 = 0 := by
      show (hi : ZMod 5) + ((lo % 5 : ℕ) : ZMod 5) * 3 * (j0.val : ZMod 5) = 0
      rw [hj0z_cast]
      -- goal: ↑hi + ↑(lo%5) * 3 * ((-↑hi) * (↑(lo%5) * 3)⁻¹) = 0
      -- Rearrange: a * (b * a⁻¹) = b * (a * a⁻¹) = b
      have hinv : step5 * step5⁻¹ = 1 := mul_inv_cancel₀ hstep_ne
      calc (hi : ZMod 5) + ((lo % 5 : ℕ) : ZMod 5) * 3 * ((-(hi : ZMod 5)) * step5⁻¹)
          = (hi : ZMod 5) + (-(hi : ZMod 5)) * (step5 * step5⁻¹) := by ring
        _ = (hi : ZMod 5) + (-(hi : ZMod 5)) * 1 := by rw [hinv]
        _ = 0 := by ring

    have hj0_unique : ∀ j : Fin 5, digit j = 0 → j = j0 := by
      intro j hj
      have hzmod_eq : (j.val : ZMod 5) = j0z := by
        have hj' : step5 * (j.val : ZMod 5) = -(hi : ZMod 5) := by
          -- From digit j = 0: (hi : ZMod 5) + step5 * (j.val : ZMod 5) = 0
          -- Hence step5 * j = -(hi : ZMod 5)
          have h0 : (hi : ZMod 5) + step5 * (j.val : ZMod 5) = 0 := hj
          linear_combination h0
        have hinv : step5⁻¹ * step5 = 1 := inv_mul_cancel₀ hstep_ne
        calc (j.val : ZMod 5)
            = step5⁻¹ * (step5 * (j.val : ZMod 5)) := by
                rw [← mul_assoc, hinv, one_mul]
          _ = step5⁻¹ * (-(hi : ZMod 5)) := by rw [hj']
          _ = (-(hi : ZMod 5)) * step5⁻¹ := by ring
          _ = j0z := rfl
      apply Fin.ext
      have hzmod_eq2 : (j.val : ZMod 5) = (j0.val : ZMod 5) := by
        rw [hzmod_eq, ← hj0z_cast]
      have hj_lt : j.val < 5 := j.isLt
      have hj0_lt : j0.val < 5 := j0.isLt
      calc j.val = (j.val : ZMod 5).val := by
              rw [ZMod.val_natCast]; exact (Nat.mod_eq_of_lt hj_lt).symm
        _ = (j0.val : ZMod 5).val := by rw [hzmod_eq2]
        _ = j0.val := by
              rw [ZMod.val_natCast]; exact Nat.mod_eq_of_lt hj0_lt

    -- Count the *non*-survivors: exactly {j0}.
    have hdead_eq_singleton :
        Finset.filter (fun j : Fin 5 => ¬ P j) Finset.univ = {j0} := by
      ext j
      constructor
      · intro hj
        have hj' : ¬ P j := by
          simpa [Finset.mem_filter] using hj
        have : digit j = 0 := by
          have : ¬ digit j ≠ 0 := by
            intro hd
            exact hj' ((hdigit_iff j).2 hd)
          simpa using not_ne_iff.mp this
        have : j = j0 := hj0_unique j this
        simpa [this]
      · intro hj
        have hj' : j = j0 := by
          simpa using (by
            simpa using hj)
        subst hj'
        have : digit j0 = 0 := hj0_zero
        have : ¬ digit j0 ≠ 0 := by simpa [this]
        have : ¬ P j0 := by
          intro hP
          have : digit j0 ≠ 0 := (hdigit_iff j0).1 hP
          exact this.elim (by simpa [hj0_zero])
        simp [Finset.mem_filter, this]

    have hdead_card : (Finset.filter (fun j : Fin 5 => ¬ P j) Finset.univ).card = 1 := by
      simp [hdead_eq_singleton]

    have hsum :
        (Finset.filter P Finset.univ).card +
        (Finset.filter (fun j : Fin 5 => ¬ P j) Finset.univ).card = 5 := by
      simpa using
        (Finset.filter_card_add_filter_neg_card_eq_card (s := (Finset.univ : Finset (Fin 5))) (p := P))

    have hsurv_card : (Finset.filter P Finset.univ).card = 4 := by
      omega

    rw [hsurv_card]; left; rfl

end Zeroless
