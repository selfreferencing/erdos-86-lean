/-
  ErdosStraus/ED2/ExistsGoodDivisor.lean

  The "hard number theory" input for the Dyachenko formalization:
  for every prime p ≡ 1 (mod 4), there exists A in the window
  [(p+3)/4, (3p-3)/4] and a divisor d of A² such that (4A-p) | (d+A).

  This file provides:
  1. `exists_good_A_and_divisor` — the core existence claim (sorry, for GPT)
  2. `coprime_A_delta` — gcd(A, 4A-p) = 1 when A < p and p prime
  3. `complementary_divisor_cong` — δ | (d+A) implies δ | (e+A) for e = A²/d
  4. `divisor_gives_type2` — bridge from (A,d) to ed2_of_good_divisor
  5. `ed2_from_good_divisor` — assembly combining 1 + 4

  ## Architecture

  The key insight is that we can bypass the (α, d', b', c') parameterization
  entirely. Given A and d satisfying the divisor condition, we set:
    δ = 4A - p
    e = A²/d       (well-defined since d | A²)
    b_val = (d+A)/δ (well-defined since δ | (d+A))
    c_val = (e+A)/δ (follows from coprimality: gcd(A,δ) = 1)

  Then ed2_of_good_divisor (Phase3.lean) produces the Type II solution.

  ## Sorry status

  - `exists_good_A_and_divisor`: THE core sorry (needs Thue/Fermat argument)
  - `coprime_A_delta`: PROVEN (by Aristotle/Harmonic)
  - `complementary_divisor_cong`: PROVEN (by Aristotle/Harmonic)

  Source: GPT Parts 6+7 (January 2026), adapted to Phase3.lean signatures
-/

import Mathlib.Tactic
import ErdosStraus.ED2.Phase3

namespace ED2

/-! ## The hard number-theory input -/

/-- For every prime p ≡ 1 (mod 4), there exists A in the window and d | A²
    with (4A-p) | (d+A).

    This is the core existence claim that requires Thue's lemma or
    Fermat's two-square theorem to prove. See the GPT prompt for the
    mathematical argument.

    Equivalent to: setting δ = 4A - p, we need d | A² with d ≡ -A (mod δ). -/
theorem exists_good_A_and_divisor (p : ℕ) (hp : Nat.Prime p) (hp4 : p % 4 = 1) :
    ∃ A d : ℕ,
      (p + 3) / 4 ≤ A ∧
      A ≤ (3 * p - 3) / 4 ∧
      0 < d ∧
      d ∣ A ^ 2 ∧
      (4 * A - p) ∣ (d + A) := by
  sorry

/-! ## Coprimality lemma

gcd(A, 4A - p) = gcd(A, p) = 1 when 0 < A < p and p is prime. -/

/-- A and δ = 4A - p are coprime when A < p, p is prime, and p < 4A.
    Proof by Aristotle (Harmonic). -/
theorem coprime_A_delta (p A : ℕ) (hp : Nat.Prime p)
    (hA_pos : 0 < A) (hA_lt : A < p) (hA_win : p < 4 * A) :
    Nat.Coprime A (4 * A - p) := by
  -- Since gcd(A, p) = 1 and p is prime, gcd(A, 4A - p) = 1.
  have h_coprime : Nat.gcd A p = 1 := by
    apply Nat.Coprime.symm
    exact hp.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt hA_pos hA_lt)
  have h_div_p : ∀ d, d ∣ A → d ∣ (4 * A - p) → d ∣ p := by
    intros d hdA hd4A_minus_p
    have hd4A : d ∣ 4 * A := hdA.mul_left _
    convert Nat.dvd_sub' hd4A hd4A_minus_p using 1
    rw [Nat.sub_sub_self (by linarith)]
  refine' Nat.coprime_of_dvd' _
  exact fun k hk hkA hk' => h_coprime ▸ Nat.dvd_gcd hkA (h_div_p k hkA hk') |>
    fun h => by have := Nat.le_of_dvd (by linarith) h; interval_cases k <;> trivial

/-! ## Complementary divisor congruence

If d | A² and δ | (d + A) and gcd(A, δ) = 1, then δ | (e + A)
where e = A²/d.

Proof: From d·e = A² and d ≡ -A (mod δ), we get -A·e ≡ A² (mod δ),
so A·(e + A) ≡ 0 (mod δ). Since gcd(A, δ) = 1, we get δ | (e + A). -/

/-- The complementary divisor e = A²/d also satisfies δ | (e + A).
    Proof by Aristotle (Harmonic). -/
theorem complementary_divisor_cong (A d e δ : ℕ)
    (hde : d * e = A * A)
    (hmod : δ ∣ (d + A))
    (hcop : Nat.Coprime A δ) :
    δ ∣ (e + A) := by
  have h_cong : A * (e + A) ≡ 0 [MOD δ] := by
    have h_cong : (-A : ℤ) * e ≡ A * A [ZMOD δ] := by
      rw [Int.modEq_iff_dvd]
      obtain ⟨k, hk⟩ := hmod; use k * e; nlinarith
    have h_rearrange : A * (e + A) ≡ 0 [ZMOD δ] := by
      convert h_cong.neg.add_right (A * A) using 1 <;> ring
    exact Int.natCast_modEq_iff.mp h_rearrange
  exact hcop.symm.dvd_of_dvd_mul_left <| Nat.dvd_of_mod_eq_zero h_cong

/-! ## Bridge: (A, d) existence data → Type II solution

This theorem takes the output of `exists_good_A_and_divisor` and produces
the inputs needed by `ed2_of_good_divisor` from Phase3.lean.

Phase3.lean's `ed2_of_good_divisor` signature:
  (p δ : ℕ) (hδ_pos : 0 < δ)
  (A : ℤ) (hA : (↑p : ℤ) + ↑δ = 4 * A)
  (d e : ℤ) (hd_pos : 0 < d) (he_pos : 0 < e)
  (hde : d * e = A ^ 2)
  (b_val c_val : ℤ)
  (hb_def : (↑δ : ℤ) * b_val = d + A)
  (hc_def : (↑δ : ℤ) * c_val = e + A)
  →
  ∃ b c : ℕ, b > 0 ∧ c > 0 ∧ (↑p + ↑δ : ℤ) * (↑b + ↑c) = 4 * ↑δ * ↑b * ↑c
-/

/-- Bridge from (A, d) with window bounds and divisibility to a Type II solution.
    Constructs δ, e, b_val, c_val and delegates to `ed2_of_good_divisor`. -/
theorem divisor_gives_type2
    (p : ℕ) (hp : Nat.Prime p) (hp4 : p % 4 = 1)
    (A : ℕ) (hA_lo : (p + 3) / 4 ≤ A) (hA_hi : A ≤ (3 * p - 3) / 4)
    (d : ℕ) (hd_pos : 0 < d) (hd_dvd : d ∣ A ^ 2)
    (hmod : (4 * A - p) ∣ (d + A)) :
    ∃ (offset : ℕ) (b c : ℕ),
      offset % 4 = 3 ∧ b > 0 ∧ c > 0 ∧
      (↑p + ↑offset : ℤ) * (↑b + ↑c) = 4 * ↑offset * ↑b * ↑c := by
  -- Basic bounds
  have hp5 : p ≥ 5 := by
    have := hp.two_le; omega
  have hA_pos : 0 < A := by omega
  have hA_lt_p : A < p := by omega

  -- Define δ = 4A - p
  set δ := 4 * A - p with hδ_def
  have hδ_pos : 0 < δ := by omega
  have h_sum : p + δ = 4 * A := by omega

  -- δ ≡ 3 (mod 4) since p ≡ 1 (mod 4) and 4A ≡ 0 (mod 4)
  have hδ_mod : δ % 4 = 3 := by omega

  -- d | A * A (from d | A²)
  have hd_dvdAA : d ∣ A * A := by rwa [← sq] at hd_dvd

  -- Define e = A * A / d (well-defined since d | A * A)
  obtain ⟨e, he_def⟩ := hd_dvdAA -- he_def : A * A = d * e

  -- e > 0 (since A > 0 and d > 0 imply A * A > 0 = d * 0)
  have he_pos : 0 < e := by
    by_contra h; push_neg at h
    interval_cases e <;> omega

  -- Coprimality: gcd(A, δ) = 1
  have hcop : Nat.Coprime A δ := coprime_A_delta p A hp hA_pos hA_lt_p (by omega)

  -- Complementary divisor congruence: δ | (e + A)
  have hmod_e : δ ∣ (e + A) :=
    complementary_divisor_cong A d e δ he_def hmod hcop

  -- Define b_val = (d + A) / δ and c_val = (e + A) / δ
  obtain ⟨b_val, hb_eq⟩ := hmod     -- hb_eq : d + A = δ * b_val
  obtain ⟨c_val, hc_eq⟩ := hmod_e   -- hc_eq : e + A = δ * c_val

  -- Apply ed2_of_good_divisor from Phase3.lean
  -- Need to cast everything from ℕ to ℤ
  have h_sum_int : (↑p : ℤ) + ↑δ = 4 * (↑A : ℤ) := by exact_mod_cast h_sum
  have hde_int : (↑d : ℤ) * (↑e : ℤ) = (↑A : ℤ) ^ 2 := by
    push_cast; rw [sq]; exact_mod_cast he_def
  have hb_int : (↑δ : ℤ) * (↑b_val : ℤ) = (↑d : ℤ) + (↑A : ℤ) := by
    exact_mod_cast hb_eq
  have hc_int : (↑δ : ℤ) * (↑c_val : ℤ) = (↑e : ℤ) + (↑A : ℤ) := by
    exact_mod_cast hc_eq

  obtain ⟨b, c, hb_pos, hc_pos, hEq⟩ :=
    ed2_of_good_divisor p δ hδ_pos
      (↑A) h_sum_int
      (↑d) (↑e) (by exact_mod_cast hd_pos) (by exact_mod_cast he_pos)
      hde_int
      (↑b_val) (↑c_val)
      hb_int hc_int

  exact ⟨δ, b, c, hδ_mod, hb_pos, hc_pos, hEq⟩

/-! ## Assembly: combine existence + bridge -/

/-- For every prime p ≡ 1 (mod 4), the Type II equation has a solution.
    Combines `exists_good_A_and_divisor` with `divisor_gives_type2`. -/
theorem ed2_from_good_divisor
    (p : ℕ) (hp : Nat.Prime p) (hp4 : p % 4 = 1) :
    ∃ (offset : ℕ) (b c : ℕ),
      offset % 4 = 3 ∧ b > 0 ∧ c > 0 ∧
      (↑p + ↑offset : ℤ) * (↑b + ↑c) = 4 * ↑offset * ↑b * ↑c := by
  obtain ⟨A, d, hA_lo, hA_hi, hd_pos, hd_dvd, hmod⟩ :=
    exists_good_A_and_divisor p hp hp4
  exact divisor_gives_type2 p hp hp4 A hA_lo hA_hi d hd_pos hd_dvd hmod

end ED2
