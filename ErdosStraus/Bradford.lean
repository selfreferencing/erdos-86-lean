import ErdosStraus.Basic
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Nat.Cast.Field
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic

namespace ErdosStraus

open scoped BigOperators

/-- A small helper: given `p < 4*x`, the Nat subtraction `4*x - p` is positive. -/
lemma m_pos_of_lt (p x : ℕ) (h : p < 4*x) : 0 < 4*x - p := by
  exact Nat.sub_pos_of_lt h

/-- Key coprimality fact used to cancel congruences.

If `p` is prime, `x < p`, and `p < 4*x` (so `m = 4*x - p > 0`), then
`gcd x m = 1`.

Intuition: any common divisor of `x` and `4*x-p` also divides `p`, hence is `1` or `p`.
But `p ∤ x` because `x < p` and `x>0`.
-/
theorem gcd_x_m_eq_one (p x : ℕ)
    (hp : Nat.Prime p) (hx : x < p) (hm : p < 4*x) :
    Nat.gcd x (4*x - p) = 1 := by
  -- Let g := gcd(x, 4*x-p). Show g ∣ p.
  have hg4x : Nat.gcd x (4*x - p) ∣ 4*x := by
    -- gcd divides x, hence divides 4*x
    exact Nat.dvd_mul_left_of_dvd (Nat.gcd_dvd_left x (4*x - p)) 4
  have hgm : Nat.gcd x (4*x - p) ∣ (4*x - p) :=
    Nat.gcd_dvd_right x (4*x - p)

  have hp_le : p ≤ 4*x := Nat.le_of_lt hm
  have hdiff : 4*x - (4*x - p) = p := Nat.sub_sub_self hp_le

  have hgp : Nat.gcd x (4*x - p) ∣ p := by
    -- g | 4*x and g | (4*x-p) => g | 4*x - (4*x-p) = p
    have hsub := Nat.dvd_sub hg4x hgm
    simp only [hdiff] at hsub
    exact hsub

  -- Since p is prime, g = 1 or g = p.
  have hcases : Nat.gcd x (4*x - p) = 1 ∨ Nat.gcd x (4*x - p) = p := by
    exact (Nat.dvd_prime hp).1 hgp

  -- Show x > 0 (needed for `Nat.le_of_dvd`).
  have hx0 : x ≠ 0 := by
    intro hx0
    simp only [hx0, mul_zero] at hm
    exact (Nat.not_lt_zero p) hm
  have hxpos : 0 < x := Nat.pos_of_ne_zero hx0

  cases hcases with
  | inl h1 =>
      exact h1
  | inr hpEq =>
      -- If gcd = p, then p | x, contradicting x < p.
      have hpdvx : p ∣ x := by
        -- p = gcd divides x
        rw [← hpEq]
        exact Nat.gcd_dvd_left x (4*x - p)
      have hp_le_x : p ≤ x := Nat.le_of_dvd hxpos hpdvx
      exact False.elim ((not_lt_of_ge hp_le_x) hx)

/-- Bradford Type II construction.

Given:
* a prime `p`
* a choice of `x` with `p < 4*x` (so `m := 4*x - p > 0`)
* a divisor `d ∣ x^2` with `d ≤ x`
* the congruence `x + d ≡ 0 (mod m)` (equivalently `d ≡ -x (mod m)`)

then the explicit formulas

* `y = p*(x+d)/m`
* `z = p*(x + x^2/d)/m`

produce a solution of the Erdős–Straus equation.

This file contains the *number-theoretic* part (getting integrality via congruence cancellation)
fully formalized. The last algebraic identity `EscEq` is left as a TODO: it is pure ring / field
manipulation once `he : d*(x^2/d)=x^2` is available.
-/
theorem bradford_type_ii_valid
    (p x d : ℕ)
    (hp : Nat.Prime p)
    (hx : x < p)
    (hm : p < 4*x)
    (hd : d ∣ x^2)
    (_hdle : d ≤ x)
    (hcong : Nat.ModEq (4*x - p) (x + d) 0) :
    ∃ y z : ℕ, 0 < y ∧ 0 < z ∧ EscEq p x y z := by
  classical
  -- Abbreviations
  let m : ℕ := 4*x - p
  have hmpos : 0 < m := Nat.sub_pos_of_lt hm

  -- x > 0 (since otherwise 4*x = 0 cannot exceed p)
  have hx0 : x ≠ 0 := by
    intro hx0
    simp only [hx0, mul_zero] at hm
    exact (Nat.not_lt_zero p) hm
  have hxpos : 0 < x := Nat.pos_of_ne_zero hx0

  -- From the congruence, extract divisibility `m ∣ x+d`.
  have hmd : m ∣ (x + d) := by
    have : (x + d) % m = 0 := by
      -- `Nat.ModEq m (x+d) 0` is the same as equality of remainders.
      simp only [Nat.ModEq] at hcong
      exact hcong
    exact Nat.dvd_of_mod_eq_zero this

  -- Define `e = x^2/d`.
  let e : ℕ := x^2 / d
  have he : d * e = x^2 := by
    simp only [e]
    exact Nat.mul_div_cancel' hd

  -- Multiply the congruence by `e`:
  -- (x+d)*e ≡ 0  (mod m)
  have hmul : Nat.ModEq m ((x + d) * e) 0 := by
    have h1 : Nat.ModEq (4*x - p) ((x + d) * e) (0 * e) := hcong.mul_right e
    simp only [zero_mul] at h1
    exact h1

  -- Rewrite (x+d)*e = x*(x+e) using d*e=x^2.
  have hmul' : Nat.ModEq m (x * (x + e)) 0 := by
    have hxde : (x + d) * e = x * (x + e) := by
      calc
        (x + d) * e = x*e + d*e := by ring
        _ = x*e + x^2 := by rw [he]
        _ = x*e + x*x := by ring
        _ = x*(e + x) := by ring
        _ = x*(x + e) := by ring
    rw [← hxde]
    exact hmul

  -- Cancel `x` using `gcd_x_m_eq_one`.
  have hcop : Nat.Coprime x m := by
    have hg : Nat.gcd x m = 1 := by
      simp only [m]
      exact gcd_x_m_eq_one (p:=p) (x:=x) hp hx hm
    exact Nat.coprime_iff_gcd_eq_one.2 hg

  have hxplus : Nat.ModEq m (x + e) 0 := by
    -- Convert hmul' into a cancellable congruence `x*(x+e) ≡ x*0`.
    have hmul'' : Nat.ModEq m (x*(x+e)) (x*0) := by
      simp only [Nat.mul_zero]
      exact hmul'
    -- Cancel left factor.
    have := Nat.ModEq.cancel_left_of_coprime (m:=m) (a:=x+e) (b:=0) (c:=x)
      (Nat.Coprime.symm hcop) hmul''
    exact this

  have hme : m ∣ (x + e) := by
    have : (x + e) % m = 0 := by
      simp only [Nat.ModEq] at hxplus
      exact hxplus
    exact Nat.dvd_of_mod_eq_zero this

  -- Define the Bradford y and z.
  let y : ℕ := p * (x + d) / m
  let z : ℕ := p * (x + e) / m

  -- Show y,z > 0 using exactness of division + positivity of numerator.
  have hppos : 0 < p := hp.pos

  have hypos : 0 < y := by
    have hdiv : m ∣ p * (x + d) := Nat.dvd_mul_left_of_dvd hmd p
    rcases hdiv with ⟨t, ht⟩
    have hxdpos : 0 < x + d := Nat.add_pos_left hxpos d
    have hnumpos : 0 < p * (x + d) := Nat.mul_pos hppos hxdpos
    have ht0 : t ≠ 0 := by
      intro ht0
      rw [ht0, mul_zero] at ht
      exact Nat.ne_of_gt hnumpos ht
    have hy_eq : y = t := by
      simp only [y]
      rw [ht]
      exact Nat.mul_div_cancel_left t hmpos
    rw [hy_eq]
    exact Nat.pos_of_ne_zero ht0

  have hzpos : 0 < z := by
    have hdiv : m ∣ p * (x + e) := Nat.dvd_mul_left_of_dvd hme p
    rcases hdiv with ⟨t, ht⟩
    have hepos : 0 ≤ e := Nat.zero_le e
    have hxepos : 0 < x + e := Nat.add_pos_left hxpos e
    have hnumpos : 0 < p * (x + e) := Nat.mul_pos hppos hxepos
    have ht0 : t ≠ 0 := by
      intro ht0
      rw [ht0, mul_zero] at ht
      exact Nat.ne_of_gt hnumpos ht
    have hz_eq : z = t := by
      simp only [z]
      rw [ht]
      exact Nat.mul_div_cancel_left t hmpos
    rw [hz_eq]
    exact Nat.pos_of_ne_zero ht0

  -- Final step: prove the cross-multiplied equation.
  --
  -- A clean approach is to work in ℚ and use `field_simp`, leveraging the identity
  --   1/x = 1/(x+d) + 1/(x+e)  when d*e=x^2.
  --
  -- Key algebraic identity: (x+d)*(x+e) = x*(2x+d+e) when d*e = x^2
  have hprod : (x + d) * (x + e) = x * (2*x + d + e) := by
    calc (x + d) * (x + e)
        = x*x + x*e + d*x + d*e := by ring
      _ = x*x + x*e + d*x + x^2 := by rw [he]
      _ = x * (2*x + d + e) := by ring

  -- Extract exact quotients from divisibility
  rcases hmd with ⟨qd, hqd_eq⟩
  rcases hme with ⟨qe, hqe_eq⟩

  -- y and z as exact quotients
  have hy_eq : y = p * qd := by
    simp only [y]
    rw [hqd_eq]
    have h1 : m * qd / m = qd := Nat.mul_div_cancel_left qd hmpos
    have h2 : p * (m * qd) / m = p * (m * qd / m) := Nat.mul_div_assoc p (Nat.dvd_mul_right m qd)
    rw [h2, h1]
  have hz_eq : z = p * qe := by
    simp only [z]
    rw [hqe_eq]
    have h1 : m * qe / m = qe := Nat.mul_div_cancel_left qe hmpos
    have h2 : p * (m * qe) / m = p * (m * qe / m) := Nat.mul_div_assoc p (Nat.dvd_mul_right m qe)
    rw [h2, h1]

  -- Now prove EscEq by algebraic manipulation
  have hEsc : EscEq p x y z := by
    unfold EscEq
    -- Substitute y = p*qd, z = p*qe
    rw [hy_eq, hz_eq]
    -- Also use (x+d) = m*qd and (x+e) = m*qe
    have hxd : x + d = m * qd := hqd_eq
    have hxe : x + e = m * qe := hqe_eq
    -- Key identity: m * qd * qe = x * (qd + qe)
    have hkey : m * (qd * qe) = x * (qd + qe) := by
      have h1 : m * (qd + qe) = 2*x + d + e := by
        calc m * (qd + qe)
            = m * qd + m * qe := by ring
          _ = (x + d) + (x + e) := by rw [← hxd, ← hxe]
          _ = 2*x + d + e := by ring
      have hprod' : m^2 * (qd * qe) = x * (2*x + d + e) := by
        calc m^2 * (qd * qe)
            = (m * qd) * (m * qe) := by ring
          _ = (x + d) * (x + e) := by rw [← hxd, ← hxe]
          _ = x * (2*x + d + e) := hprod
      have h3 : m^2 * (qd * qe) = x * (m * (qd + qe)) := by
        calc m^2 * (qd * qe) = x * (2*x + d + e) := hprod'
          _ = x * (m * (qd + qe)) := by rw [← h1]
      have h4 : m * (m * (qd * qe)) = m * (x * (qd + qe)) := by
        calc m * (m * (qd * qe)) = m^2 * (qd * qe) := by ring
          _ = x * (m * (qd + qe)) := h3
          _ = m * (x * (qd + qe)) := by ring
      exact Nat.eq_of_mul_eq_mul_left hmpos h4
    -- 4x * qd * qe = m * qd * qe + p * qd * qe = x * (qd + qe) + p * qd * qe
    have hfinal : 4 * x * (qd * qe) = x * (qd + qe) + p * (qd * qe) := by
      have hsub : (4 * x - p) * (qd * qe) = x * (qd + qe) := by
        calc (4 * x - p) * (qd * qe)
            = m * (qd * qe) := by rfl
          _ = x * (qd + qe) := hkey
      calc 4 * x * (qd * qe)
          = (4 * x - p + p) * (qd * qe) := by
              have : 4 * x - p + p = 4 * x := Nat.sub_add_cancel (le_of_lt hm)
              rw [this]
        _ = (4 * x - p) * (qd * qe) + p * (qd * qe) := by ring
        _ = x * (qd + qe) + p * (qd * qe) := by rw [hsub]
    -- Final ring equality
    have hlhs : 4 * x * (p * qd) * (p * qe) = p^2 * (4 * x * (qd * qe)) := by ring
    have hrhs : p * (x * (p * qd) + x * (p * qe) + (p * qd) * (p * qe))
              = p^2 * (x * (qd + qe) + p * (qd * qe)) := by ring
    rw [hlhs, hrhs, hfinal]

  exact ⟨y, z, hypos, hzpos, hEsc⟩

end ErdosStraus
