/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 248cba31-660a-4b5e-a9e5-28f181da1130

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem coprime_A_delta (p A : ℕ) (hp : Nat.Prime p)
    (hA_pos : 0 < A) (hA_lt : A < p) (hA_win : p < 4 * A) :
    Nat.Coprime A (4 * A - p)
-/

import Mathlib


/-!
# Coprimality and Complementary Divisor Lemmas

Two lemmas needed for the ED2 Dyachenko bridge:

1. `coprime_A_delta`: gcd(A, 4A-p) = 1 when p is prime, 0 < A < p, and p < 4*A.
   The hypothesis p < 4*A ensures 4A - p > 0 in ℕ (no underflow).
   Route: gcd(A, 4A-p) = gcd(A, p) (since 4A ≡ 0 mod A), and gcd(A, p) = 1
   since p is prime and A < p implies p ∤ A.

2. `complementary_divisor_cong`: If d*e = A*A, δ ∣ (d+A), and gcd(A,δ) = 1,
   then δ ∣ (e+A).
   Route: From d ≡ -A (mod δ) and d*e = A², get -A*e ≡ A² (mod δ),
   so A*(e+A) ≡ 0 (mod δ). Coprimality gives δ ∣ (e+A).

There is 1 sorry to fill.
-/

theorem coprime_A_delta (p A : ℕ) (hp : Nat.Prime p)
    (hA_pos : 0 < A) (hA_lt : A < p) (hA_win : p < 4 * A) :
    Nat.Coprime A (4 * A - p) := by
  -- Since $\gcd(A, p) = 1$ and $p$ is prime, it follows that $\gcd(A, 4A - p) = 1$.
  have h_coprime : Nat.gcd A p = 1 := by
    -- Since $p$ is prime and $A < p$, it follows that $\gcd(A, p) = 1$.
    apply Nat.Coprime.symm; exact hp.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt hA_pos hA_lt);
  -- Since $\gcd(A, p) = 1$, any common divisor of $A$ and $4A - p$ must also divide $p$.
  have h_div_p : ∀ d, d ∣ A → d ∣ (4 * A - p) → d ∣ p := by
    -- If $d$ divides both $A$ and $4A - p$, then $d$ divides $4A$ (since $d$ divides $A$), and thus $d$ divides $(4A) - (4A - p) = p$.
    intros d hdA hd4A_minus_p
    have hd4A : d ∣ 4 * A := by
      exact hdA.mul_left _;
    convert Nat.dvd_sub' hd4A hd4A_minus_p using 1 ; rw [ Nat.sub_sub_self ( by linarith ) ];
  refine' Nat.coprime_of_dvd' _;
  exact fun k hk hkA hk' => h_coprime ▸ Nat.dvd_gcd hkA ( h_div_p k hkA hk' ) |> fun h => by have := Nat.le_of_dvd ( by linarith ) h; interval_cases k <;> trivial;

theorem complementary_divisor_cong (A d e δ : ℕ)
    (hde : d * e = A * A)
    (hmod : δ ∣ (d + A))
    (hcop : Nat.Coprime A δ) :
    δ ∣ (e + A) := by
  -- From $d * e = A * A$, we get that $A * (e + A) \equiv 0 \pmod{\delta}$.
  have h_cong : A * (e + A) ≡ 0 [MOD δ] := by
    -- Since $δ$ divides $d + A$, we have $d ≡ -A \pmod{δ}$. Substituting this into $d * e = A * A$, we get $(-A) * e ≡ A * A \pmod{δ}$.
    have h_cong : (-A : ℤ) * e ≡ A * A [ZMOD δ] := by
      rw [ Int.modEq_iff_dvd ];
      obtain ⟨ k, hk ⟩ := hmod; use k * e; nlinarith;
    -- Rearrange h_cong to get A * (e + A) ≡ 0 [ZMOD δ].
    have h_rearrange : A * (e + A) ≡ 0 [ZMOD δ] := by
      convert h_cong.neg.add_right ( A * A ) using 1 <;> ring;
    exact Int.natCast_modEq_iff.mp h_rearrange;
  exact hcop.symm.dvd_of_dvd_mul_left <| Nat.dvd_of_mod_eq_zero h_cong