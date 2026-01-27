/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 4439838b-6f3b-4146-b9e5-614c7ed12cce

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

Aristotle encountered an error processing this file.
Lean errors:
At line 182, column 22:
  failed to synthesize
  Norm (Matrix (Fin 5) (Fin 5) ℂ)

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.

At line 202, column 5:
  unexpected token 'λ'; expected '(', '[', '_', '{', '⦃' or identifier

At line 209, column 15:
  Unknown constant `Matrix.spectrum`

At line 216, column 4:
  Unknown constant `Matrix.spectrum`

At line 223, column 4:
  Unknown constant `Matrix.spectralRadius`

At line 229, column 4:
  Unknown constant `Matrix.spectralRadius`
-/

/-
  Zeroless/TransferOperator.lean
  Twisted Transfer Operator Algebra for the 86 Conjecture

  Key results:
  - ω is a primitive 5th root of unity
  - B^(5)_ℓ: 5-child block has eigenvalue 0 (perfect cancellation)
  - B^(4)_ℓ: 4-child block has eigenvalue -1
  - Both blocks are rank-1, hence no Jordan blocks
  - Powers are uniformly bounded: ‖B^n‖ ≤ C

  This is the algebraic core that proves ρ(M_ℓ) = 1.
-/

import Mathlib

namespace Zeroless

open scoped BigOperators

noncomputable section

/-! ## Fifth Root of Unity -/

/-- A fixed primitive 5th root of unity -/
noncomputable def ω : ℂ := Complex.exp (2 * Real.pi * Complex.I / 5)

/-- The 5×5 "5-child" twisted matrix: all rows equal (1, ω^ℓ, ω^{2ℓ}, ω^{3ℓ}, ω^{4ℓ}) -/
def B5 (ℓ : ZMod 5) : Matrix (Fin 5) (Fin 5) ℂ :=
  Matrix.of fun _ j => ω ^ (ℓ.val * j.val)

/-- The 5×5 "4-child" twisted matrix: all rows equal (0, ω^ℓ, ω^{2ℓ}, ω^{3ℓ}, ω^{4ℓ}) -/
def B4 (ℓ : ZMod 5) : Matrix (Fin 5) (Fin 5) ℂ :=
  Matrix.of fun _ j => if j.val = 0 then 0 else ω ^ (ℓ.val * j.val)

/-! ## 1. Fifth Roots of Unity -/

/-- ω is a primitive 5th root of unity -/
lemma omega_isPrimitiveRoot : IsPrimitiveRoot ω 5 := by
  simpa [ω] using Complex.isPrimitiveRoot_exp 5 (by norm_num : (5 : ℕ) ≠ 0)

/-- ω^5 = 1 -/
theorem omega_pow_five : ω ^ 5 = 1 := by
  exact omega_isPrimitiveRoot.pow_eq_one

/-- Sum of all 5th roots: 1 + ω + ω^2 + ω^3 + ω^4 = 0 -/
theorem fifth_roots_sum : (∑ j : Fin 5, ω ^ j.val) = 0 := by
  have h := omega_isPrimitiveRoot.sum_pow_unit_rootsOfUnity
  simp only [Finset.sum_fin_eq_sum_range] at h
  sorry -- Needs careful handling of the sum format

/-- For ℓ ≢ 0 (mod 5): ∑_{j=0}^4 ω^{ℓj} = 0 -/
theorem twisted_sum_zero (ℓ : ZMod 5) (hℓ : ℓ ≠ 0) :
    (∑ j : Fin 5, ω ^ (ℓ.val * j.val)) = 0 := by
  classical
  -- First show Nat.Coprime ℓ.val 5 (since ℓ.val ∈ {1,2,3,4} for ℓ≠0)
  have hval : (ℓ.val : ℕ) ≠ 0 := by
    intro h0
    apply hℓ
    exact ZMod.val_eq_zero.mp h0
  have hlt : ℓ.val < 5 := ℓ.val_lt
  have hndiv : ¬ (5 ∣ ℓ.val) := by
    intro hdiv
    have : ℓ.val = 0 := Nat.eq_zero_of_dvd_of_lt hdiv hlt
    exact hval this
  have hprime : Nat.Prime 5 := by decide
  have hcop : Nat.Coprime ℓ.val 5 := (hprime.coprime_iff_not_dvd).2 hndiv

  -- Powers of a primitive root by a coprime exponent are still primitive
  have hprim' : IsPrimitiveRoot (ω ^ ℓ.val) 5 :=
    omega_isPrimitiveRoot.pow_of_coprime ℓ.val hcop

  -- Now sum the powers of (ω^ℓ)
  have hsum : (∑ j : Fin 5, (ω ^ ℓ.val) ^ j.val) = 0 := by
    sorry -- Use hprim'.sum_eq_zero with correct format

  -- Rewrite (ω^ℓ)^j as ω^(ℓ*j)
  simp only [← pow_mul] at hsum
  convert hsum using 2
  ext j
  ring

/-- Sum over j=1..4: ∑_{j=1}^4 ω^{ℓj} = -1 for ℓ ≢ 0 -/
theorem twisted_partial_sum (ℓ : ZMod 5) (hℓ : ℓ ≠ 0) :
    (∑ j : Fin 4, ω ^ (ℓ.val * (j.val + 1))) = -1 := by
  classical
  -- Split the full sum over Fin 5 into the 0 term and the successor terms
  have hsplit :
      (∑ j : Fin 5, ω ^ (ℓ.val * j.val))
        = ω ^ (ℓ.val * 0) + (∑ j : Fin 4, ω ^ (ℓ.val * (j.val + 1))) := by
    rw [Fin.sum_univ_succ]
    simp only [Fin.val_zero, mul_zero, pow_zero, Fin.val_succ]
    ring_nf

  -- Use twisted_sum_zero and ω^0 = 1
  have hfull : (∑ j : Fin 5, ω ^ (ℓ.val * j.val)) = 0 := twisted_sum_zero ℓ hℓ

  -- From: 0 = 1 + partial, so partial = -1
  simp only [mul_zero, pow_zero] at hsplit
  linarith [hsplit, hfull]

/-! ## 2. Rank-1 Structure -/

/-- B5 has rank ≤ 1 (all rows identical) -/
theorem B5_rank_one (ℓ : ZMod 5) : Matrix.rank (B5 ℓ) ≤ 1 := by
  classical
  -- All rows are identical, so row space is 1-dimensional
  sorry

/-- B4 has rank ≤ 1 (all rows identical) -/
theorem B4_rank_one (ℓ : ZMod 5) : Matrix.rank (B4 ℓ) ≤ 1 := by
  classical
  sorry

/-! ## 3. Power Identities (The "No Jordan Growth" Core) -/

/-- For ℓ≢0, (B5 ℓ)^2 = 0 (nilpotent) -/
theorem B5_squared_zero (ℓ : ZMod 5) (hℓ : ℓ ≠ 0) :
    B5 ℓ * B5 ℓ = 0 := by
  classical
  ext i k
  simp only [B5, Matrix.mul_apply, Matrix.of_apply, Matrix.zero_apply]
  -- Entry (i,k) = ∑_j ω^{ℓ·j} · ω^{ℓ·k} = ω^{ℓ·k} · (∑_j ω^{ℓ·j}) = ω^{ℓ·k} · 0 = 0
  have h : (∑ j : Fin 5, ω ^ (ℓ.val * j.val)) = 0 := twisted_sum_zero ℓ hℓ
  simp only [← Finset.sum_mul]
  convert mul_zero (ω ^ (ℓ.val * k.val))
  convert h using 1
  ext j
  ring

/-- For ℓ≢0, (B4 ℓ)^2 = -(B4 ℓ) -/
theorem B4_squared (ℓ : ZMod 5) (hℓ : ℓ ≠ 0) :
    B4 ℓ * B4 ℓ = -(B4 ℓ) := by
  classical
  ext i k
  simp only [B4, Matrix.mul_apply, Matrix.of_apply, Matrix.neg_apply]
  -- The row sum (excluding j=0) is -1
  have hrow : (∑ j : Fin 5, (if j.val = 0 then (0 : ℂ) else ω ^ (ℓ.val * j.val))) = -1 := by
    have h1 : (∑ j : Fin 5, (if j.val = 0 then (0 : ℂ) else ω ^ (ℓ.val * j.val)))
            = 0 + (∑ j : Fin 4, ω ^ (ℓ.val * (j.val + 1))) := by
      rw [Fin.sum_univ_succ]
      simp only [Fin.val_zero, ↓reduceIte, Fin.val_succ]
      congr 1
      apply Finset.sum_congr rfl
      intro j _
      simp only [Nat.succ_eq_add_one, Nat.add_eq, Nat.add_zero]
      split_ifs with h
      · omega
      · rfl
    rw [h1, zero_add]
    exact twisted_partial_sum ℓ hℓ
  -- Expand the product
  sorry -- Complete using hrow and the structure

/-- For ℓ≢0 and n≥1: (B4 ℓ)^n = (-1)^{n-1} • B4 ℓ -/
theorem B4_power (ℓ : ZMod 5) (hℓ : ℓ ≠ 0) (n : ℕ) (hn : n ≥ 1) :
    B4 ℓ ^ n = (-1 : ℂ)^(n-1) • B4 ℓ := by
  classical
  induction n with
  | zero => omega
  | succ m ih =>
    cases m with
    | zero =>
      -- n = 1: B4^1 = (-1)^0 • B4 = B4
      simp
    | succ m' =>
      -- n = m'+2: Use B4^2 = -B4
      have hm : m'.succ ≥ 1 := Nat.succ_le_succ (Nat.zero_le _)
      have ih' : B4 ℓ ^ m'.succ = (-1 : ℂ)^m' • B4 ℓ := ih hm
      calc B4 ℓ ^ (m'.succ.succ)
          = B4 ℓ ^ m'.succ * B4 ℓ := by ring
        _ = ((-1 : ℂ)^m' • B4 ℓ) * B4 ℓ := by rw [ih']
        _ = (-1 : ℂ)^m' • (B4 ℓ * B4 ℓ) := by
            simp only [Matrix.smul_mul]
        _ = (-1 : ℂ)^m' • (-(B4 ℓ)) := by rw [B4_squared ℓ hℓ]
        _ = (-1 : ℂ)^(m'.succ) • B4 ℓ := by
            simp [pow_succ, neg_mul, mul_neg]

/-- The powers of B4 ℓ are uniformly bounded in operator norm -/
theorem B4_power_bounded (ℓ : ZMod 5) (hℓ : ℓ ≠ 0) :
    ∃ C : ℝ, ∀ n : ℕ, ‖B4 ℓ ^ n‖ ≤ C := by
  /-
  ERROR 1:
  failed to synthesize
    Norm (Matrix (Fin 5) (Fin 5) ℂ)

  Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
  -/
  classical
  refine ⟨‖(1 : Matrix (Fin 5) (Fin 5) ℂ)‖ + ‖B4 ℓ‖, ?_⟩
  intro n
  cases n with
  | zero =>
    simp [le_add_of_nonneg_right, norm_nonneg]
  | succ n =>
    have hn : n.succ ≥ 1 := Nat.succ_le_succ (Nat.zero_le _)
    have hpow : B4 ℓ ^ n.succ = (-1 : ℂ)^(n.succ - 1) • B4 ℓ := B4_power ℓ hℓ n.succ hn
    calc ‖B4 ℓ ^ n.succ‖
        = ‖(-1 : ℂ)^(n.succ - 1) • B4 ℓ‖ := by rw [hpow]
      _ ≤ ‖(-1 : ℂ)^(n.succ - 1)‖ * ‖B4 ℓ‖ := norm_smul_le _ _
      _ = ‖B4 ℓ‖ := by simp [Complex.norm_eq_abs]
      _ ≤ ‖(1 : Matrix (Fin 5) (Fin 5) ℂ)‖ + ‖B4 ℓ‖ := le_add_of_nonneg_left (norm_nonneg _)

/-! ## 4. Spectrum and Spectral Radius -/

/-- B5 eigenvalues are all 0 for ℓ ≢ 0 (nilpotent) -/
theorem B5_eigenvalue_zero (ℓ : ZMod 5) (hℓ : ℓ ≠ 0) :
    ∀ λ ∈ Matrix.spectrum ℂ (B5 ℓ), λ = 0 := by
  /-
  ERROR 1:
  unexpected token 'λ'; expected '(', '[', '_', '{', '⦃' or identifier
  -/
  classical
  -- B5^2 = 0 means B5 is nilpotent, so all eigenvalues are 0
  sorry

/-- -1 is an eigenvalue of B4 for ℓ ≢ 0 -/
theorem B4_eigenvalue_neg_one (ℓ : ZMod 5) (hℓ : ℓ ≠ 0) :
    (-1 : ℂ) ∈ Matrix.spectrum ℂ (B4 ℓ) := by
  /-
  ERROR 1:
  Unknown constant `Matrix.spectrum`
  -/
  classical
  -- The all-ones vector is an eigenvector with eigenvalue = row sum = -1
  sorry

/-- Spectrum of B4 is contained in {0, -1} -/
theorem B4_spectrum (ℓ : ZMod 5) (hℓ : ℓ ≠ 0) :
    Matrix.spectrum ℂ (B4 ℓ) ⊆ {0, -1} := by
  /-
  ERROR 1:
  Unknown constant `Matrix.spectrum`
  -/
  classical
  -- B4(B4 + 1) = 0 means minimal polynomial divides X(X+1)
  sorry

/-- Spectral radius of B5 is 0 -/
theorem B5_spectral_radius (ℓ : ZMod 5) (hℓ : ℓ ≠ 0) :
    Matrix.spectralRadius (B5 ℓ) = 0 := by
  /-
  ERROR 1:
  Unknown constant `Matrix.spectralRadius`
  -/
  classical
  sorry

/-- Spectral radius of B4 is 1 -/
theorem B4_spectral_radius (ℓ : ZMod 5) (hℓ : ℓ ≠ 0) :
    Matrix.spectralRadius (B4 ℓ) = 1 := by
  /-
  ERROR 1:
  Unknown constant `Matrix.spectralRadius`
  -/
  classical
  sorry

end

end Zeroless
