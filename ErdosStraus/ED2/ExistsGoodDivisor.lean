/-
  ErdosStraus/ED2/ExistsGoodDivisor.lean

  The "hard number theory" input for the Dyachenko formalization:
  for every prime p ≡ 1 (mod 4), there exists A in the window
  [(p+3)/4, (3p-3)/4] and a divisor d of A² such that (4A-p) | (d+A).

  This file provides:
  1. `exists_good_A_and_divisor` — the core existence claim
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

  ## Proof structure for exists_good_A_and_divisor

  We split p ≡ 1 (mod 4) into three cases:

  **Case 1 (p ≡ 5 mod 8)**: PROVEN.
    A = (p+3)/4, δ = 3. Since p ≡ 5 (mod 8), A is even.
    - If A ≡ 1 (mod 3): d = 2 works (2 | A² since A even, 3 | 2+A)
    - If A ≡ 2 (mod 3): d = 1 works (1 | A², 3 | 1+A)
    (A ≢ 0 mod 3 by coprimality: gcd(A, δ) = gcd(A, 3) = 1)

  **Case 2 (p ≡ 17 mod 24)**: PROVEN.
    A = (p+3)/4, δ = 3. Since p ≡ 2 (mod 3), A ≡ 2 (mod 3).
    d = 1 works: 1 | A², 3 | 1+A.

  **Case 3 (p ≡ 1 mod 24)**: SORRY.
    A = (p+3)/4 gives δ = 3 and A ≡ 1 (mod 3). We need d | A² with
    d ≡ 2 (mod 3), but A may be an odd prime power with all factors ≡ 1 (mod 3)
    (e.g., p = 73, A = 19), making this impossible for fixed A and δ = 3.

    The Dyachenko paper handles this via a lattice density argument showing
    that SOME A in the window [(p+3)/4, (3p-3)/4] must work with some δ.
    Completing this case requires one of:
    (a) Formalizing Lemma 9.22 (lattice = solution set) + window lemma
    (b) Thue's lemma + a bridge from small congruence solutions to divisors
    (c) Fermat two-squares (Nat.Prime.sq_add_sq in Mathlib) + a custom bridge

  ## Sorry status

  - `exists_good_A_and_divisor`: ONE sorry remains (Case 3: p ≡ 1 mod 24)
  - `coprime_A_delta`: PROVEN (by Aristotle/Harmonic)
  - `complementary_divisor_cong`: PROVEN (by Aristotle/Harmonic)
  - `divisor_gives_type2`: PROVEN
  - `ed2_from_good_divisor`: PROVEN (modulo exists_good_A_and_divisor)

  Source: GPT Parts 6+7 (January 2026), adapted by Claude Opus
-/

import Mathlib.Tactic
import ErdosStraus.ED2.Phase3

namespace ED2

/-! ## The hard number-theory input -/

/-- For every prime p ≡ 1 (mod 4), there exists A in the window and d | A²
    with (4A-p) | (d+A).

    This is the core existence claim. We split into three cases:
    - Case 1: p ≡ 5 (mod 8) — choose A = (p+3)/4, giving δ = 3
    - Case 2: p ≡ 17 (mod 24) — direct construction
    - Case 3: p ≡ 1 (mod 24) — requires lattice argument (Dyachenko)

    Equivalent to: setting δ = 4A - p, we need d | A² with d ≡ -A (mod δ). -/
theorem exists_good_A_and_divisor (p : ℕ) (hp : Nat.Prime p) (hp4 : p % 4 = 1) :
    ∃ A d : ℕ,
      (p + 3) / 4 ≤ A ∧
      A ≤ (3 * p - 3) / 4 ∧
      0 < d ∧
      d ∣ A ^ 2 ∧
      (4 * A - p) ∣ (d + A) := by
  -- p ≡ 1 (mod 4) and p prime implies p ≥ 5
  have hp5 : p ≥ 5 := by
    have hp2' : p ≠ 2 := by intro heq; rw [heq] at hp4; omega
    have hp3' : p ≠ 3 := by intro heq; rw [heq] at hp4; omega
    have hp2le := hp.two_le
    omega
  -- Case split on p mod 8
  by_cases hp8_5 : p % 8 = 5
  · -- Case 1: p ≡ 5 (mod 8)
    -- Choose A = (p+3)/4, which gives δ = 4A - p = 3
    use (p + 3) / 4
    have hA_even : 2 ∣ (p + 3) / 4 := by
      -- p ≡ 5 (mod 8) implies p + 3 ≡ 0 (mod 8), so (p+3)/4 is even
      have h8 : (p + 3) % 8 = 0 := by omega
      exact ⟨(p + 3) / 8, by omega⟩
    have hδ_eq_3 : 4 * ((p + 3) / 4) - p = 3 := by omega
    -- Split on A mod 3 to choose d
    by_cases hA_mod3_1 : (p + 3) / 4 % 3 = 1
    · -- A ≡ 1 (mod 3): choose d = 2
      use 2
      refine ⟨le_refl _, ?_, by omega, ?_, ?_⟩
      · -- A ≤ (3p-3)/4
        omega
      · -- 2 | A² (since A is even)
        have h2A : 2 ∣ ((p + 3) / 4) ^ 2 := by
          rw [sq]; exact dvd_mul_of_dvd_left hA_even _
        exact h2A
      · -- 3 | (2 + A), i.e., 3 | (2 + A) where A ≡ 1 (mod 3)
        rw [hδ_eq_3]
        have : (2 + (p + 3) / 4) % 3 = 0 := by omega
        exact Nat.dvd_of_mod_eq_zero this
    · -- A ≢ 1 (mod 3)
      -- First show A ≢ 0 (mod 3): if 3 | A, then 3 | (p+3), so 3 | p, contradiction
      have hA_not_div3 : (p + 3) / 4 % 3 ≠ 0 := by
        intro h3A
        -- 3 | A and 4 | (p+3), so need to show 3 | (p+3)
        -- A = (p+3)/4, so p+3 = 4A, so if 3 | A then 3 | (p+3)
        have hdiv : 3 ∣ (p + 3) := by
          have h4div : 4 ∣ (p + 3) := by omega
          have hA_eq : (p + 3) = 4 * ((p + 3) / 4) := by omega
          rw [hA_eq]
          exact dvd_mul_of_dvd_right (Nat.dvd_of_mod_eq_zero h3A) 4
        -- If 3 | (p+3) then 3 | p (since 3 | 3)
        have hp3_div : 3 ∣ p := by omega
        -- But p is prime and p ≥ 5, so p ≠ 3, contradiction
        have hp_eq_3 : p = 3 := (hp.eq_one_or_self_of_dvd 3 hp3_div).resolve_left (by omega) |>.symm
        omega
      -- So A ≡ 2 (mod 3). Choose d = 1.
      use 1
      refine ⟨le_refl _, ?_, by omega, ?_, ?_⟩
      · omega
      · exact one_dvd _
      · rw [hδ_eq_3]
        -- A ≢ 0 and A ≢ 1, so A ≡ 2 (mod 3), hence 1 + A ≡ 0 (mod 3)
        have hA_mod3_2 : (p + 3) / 4 % 3 = 2 := by omega
        have : (1 + (p + 3) / 4) % 3 = 0 := by omega
        exact Nat.dvd_of_mod_eq_zero this
  · -- p ≢ 5 (mod 8), so p ≡ 1 (mod 8) (since p ≡ 1 mod 4)
    have hp8_1 : p % 8 = 1 := by omega
    -- Further split on p mod 24
    by_cases hp24_17 : p % 24 = 17
    · -- Case 2: p ≡ 17 (mod 24)
      -- Use A = (p+3)/4, giving δ = 3 (same as Case 1)
      -- Key: p ≡ 17 (mod 24) implies p ≡ 2 (mod 3), so A ≡ 2 (mod 3), and d = 1 works
      use (p + 3) / 4
      have hδ_eq_3 : 4 * ((p + 3) / 4) - p = 3 := by omega
      -- Show A ≡ 2 (mod 3): since p ≡ 2 (mod 3), (p+3) ≡ 2 (mod 3), and 4 ≡ 1 (mod 3)
      have hA_mod3_2 : (p + 3) / 4 % 3 = 2 := by omega
      use 1
      refine ⟨le_refl _, ?_, by omega, ?_, ?_⟩
      · omega
      · exact one_dvd _
      · rw [hδ_eq_3]
        have : (1 + (p + 3) / 4) % 3 = 0 := by omega
        exact Nat.dvd_of_mod_eq_zero this
    · -- Case 3: p ≡ 1 (mod 24)
      -- (p ≡ 9 mod 24 is impossible for primes p > 3 since 9 ≡ 0 mod 3)
      --
      -- This is the hard case. With A = (p+3)/4 and δ = 3, we have A ≡ 1 (mod 3)
      -- and need d | A² with d ≡ 2 (mod 3). This fails when all prime factors of
      -- A are ≡ 1 (mod 3) (e.g., p = 73, A = 19).
      --
      -- Using δ = 7 (A = (p+7)/4) also fails for some p because the divisors of
      -- A² may only generate the QR subgroup {1,2,4} ⊂ (ℤ/7ℤ)*.
      --
      -- The correct approach requires either:
      -- (a) Dyachenko's lattice density argument (Lemma 9.22 + window lemma)
      -- (b) Thue's lemma applied to varying δ values
      -- (c) Fermat two-squares + a bridge showing some A in the window works
      --
      -- Mathlib provides `Nat.Prime.sq_add_sq` (Fermat's Christmas theorem) and
      -- the pigeonhole principle, which together could close this gap.
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
    have := Nat.dvd_sub hd4A hd4A_minus_p
    rwa [Nat.sub_sub_self (by linarith)] at this
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
  have hd_dvdAA : d ∣ A * A := by rwa [sq] at hd_dvd

  -- Define e = A * A / d (well-defined since d | A * A)
  obtain ⟨e, he_def⟩ := hd_dvdAA -- he_def : A * A = d * e

  -- e > 0 (since A > 0 and d > 0 imply A * A > 0 = d * 0)
  have he_pos : 0 < e := by
    rcases Nat.eq_zero_or_pos e with rfl | h
    · simp at he_def; omega
    · exact h

  -- Coprimality: gcd(A, δ) = 1
  have hcop : Nat.Coprime A δ := coprime_A_delta p A hp hA_pos hA_lt_p (by omega)

  -- Complementary divisor congruence: δ | (e + A)
  have hmod_e : δ ∣ (e + A) :=
    complementary_divisor_cong A d e δ he_def.symm hmod hcop

  -- Define b_val = (d + A) / δ and c_val = (e + A) / δ
  obtain ⟨b_val, hb_eq⟩ := hmod     -- hb_eq : d + A = δ * b_val
  obtain ⟨c_val, hc_eq⟩ := hmod_e   -- hc_eq : e + A = δ * c_val

  -- Apply ed2_of_good_divisor from Phase3.lean
  -- Need to cast everything from ℕ to ℤ
  have h_sum_int : (↑p : ℤ) + ↑δ = 4 * (↑A : ℤ) := by exact_mod_cast h_sum
  have hde_int : (↑d : ℤ) * (↑e : ℤ) = (↑A : ℤ) ^ 2 := by
    rw [sq]; exact_mod_cast he_def.symm
  have hb_int : (↑δ : ℤ) * (↑b_val : ℤ) = (↑d : ℤ) + (↑A : ℤ) := by
    exact_mod_cast hb_eq.symm
  have hc_int : (↑δ : ℤ) * (↑c_val : ℤ) = (↑e : ℤ) + (↑A : ℤ) := by
    exact_mod_cast hc_eq.symm

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
