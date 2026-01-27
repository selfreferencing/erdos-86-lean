# Lean Formalization Prompt 3: Transfer Operator Algebra

## Task
Create Lean 4 code formalizing the twisted transfer operator and its spectral properties.

## Context
The proof uses transfer operators on survivor sets. The key is that twisted operators have spectral radius 1.

## Required Definitions

```lean
import Mathlib.LinearAlgebra.Matrix.Spectrum
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Tactic

namespace Zeroless

-- Fifth root of unity
noncomputable def ω : ℂ := Complex.exp (2 * Real.pi * Complex.I / 5)

-- The 5×5 twisted matrices for 5-child and 4-child cases
-- B^(5)_ℓ : all rows are (1, ω^ℓ, ω^{2ℓ}, ω^{3ℓ}, ω^{4ℓ})
-- B^(4)_ℓ : all rows are (0, ω^ℓ, ω^{2ℓ}, ω^{3ℓ}, ω^{4ℓ})

def B5 (ℓ : ZMod 5) : Matrix (Fin 5) (Fin 5) ℂ :=
  Matrix.of fun _ j => ω ^ (ℓ.val * j.val)

def B4 (ℓ : ZMod 5) : Matrix (Fin 5) (Fin 5) ℂ :=
  Matrix.of fun _ j => if j.val = 0 then 0 else ω ^ (ℓ.val * j.val)
```

## Required Theorems

### 1. Fifth Roots of Unity
```lean
-- ω^5 = 1
theorem omega_pow_five : ω ^ 5 = 1 := sorry

-- Sum of all fifth roots is 0
theorem fifth_roots_sum : ∑ j : Fin 5, ω ^ j.val = 0 := sorry

-- For ℓ ≢ 0 (mod 5): ∑_{j=0}^4 ω^{ℓj} = 0
theorem twisted_sum_zero (ℓ : ZMod 5) (hℓ : ℓ ≠ 0) :
  ∑ j : Fin 5, ω ^ (ℓ.val * j.val) = 0 := sorry

-- Sum over j=1..4: ∑_{j=1}^4 ω^{ℓj} = -1
theorem twisted_partial_sum (ℓ : ZMod 5) (hℓ : ℓ ≠ 0) :
  ∑ j : Fin 4, ω ^ (ℓ.val * (j.val + 1)) = -1 := sorry
```

### 2. Rank-1 Structure
```lean
-- B^(5)_ℓ is rank 1 (all rows identical)
theorem B5_rank_one (ℓ : ZMod 5) : Matrix.rank (B5 ℓ) ≤ 1 := sorry

-- B^(4)_ℓ is rank 1
theorem B4_rank_one (ℓ : ZMod 5) : Matrix.rank (B4 ℓ) ≤ 1 := sorry

-- B^(5)_ℓ = 1 · v^T where v = (1, ω^ℓ, ω^{2ℓ}, ω^{3ℓ}, ω^{4ℓ})
-- B^(4)_ℓ = 1 · w^T where w = (0, ω^ℓ, ω^{2ℓ}, ω^{3ℓ}, ω^{4ℓ})
```

### 3. Eigenvalue Computation (THE KEY RESULT)
```lean
-- B^(5)_ℓ has eigenvalue 0 for ℓ ≠ 0 (mod 5)
-- Because: eigenvalue = ∑_{j=0}^4 ω^{ℓj} = 0
theorem B5_eigenvalue_zero (ℓ : ZMod 5) (hℓ : ℓ ≠ 0) :
  ∀ λ ∈ Matrix.spectrum ℂ (B5 ℓ), λ = 0 := sorry

-- B^(4)_ℓ has eigenvalue -1 for ℓ ≠ 0 (mod 5)
-- Because: eigenvalue = ∑_{j=1}^4 ω^{ℓj} = -1
theorem B4_eigenvalue_neg_one (ℓ : ZMod 5) (hℓ : ℓ ≠ 0) :
  -1 ∈ Matrix.spectrum ℂ (B4 ℓ) := sorry

-- All other eigenvalues of B^(4)_ℓ are 0
theorem B4_spectrum (ℓ : ZMod 5) (hℓ : ℓ ≠ 0) :
  Matrix.spectrum ℂ (B4 ℓ) ⊆ {0, -1} := sorry
```

### 4. Spectral Radius
```lean
-- Spectral radius of B^(5)_ℓ is 0
theorem B5_spectral_radius (ℓ : ZMod 5) (hℓ : ℓ ≠ 0) :
  Matrix.spectralRadius (B5 ℓ) = 0 := sorry

-- Spectral radius of B^(4)_ℓ is 1
theorem B4_spectral_radius (ℓ : ZMod 5) (hℓ : ℓ ≠ 0) :
  Matrix.spectralRadius (B4 ℓ) = 1 := sorry
```

### 5. Power Boundedness (No Jordan Growth)
```lean
-- (B^(5)_ℓ)^2 = 0 (nilpotent)
theorem B5_squared_zero (ℓ : ZMod 5) (hℓ : ℓ ≠ 0) :
  B5 ℓ * B5 ℓ = 0 := sorry

-- (B^(4)_ℓ)^2 = -B^(4)_ℓ
theorem B4_squared (ℓ : ZMod 5) (hℓ : ℓ ≠ 0) :
  B4 ℓ * B4 ℓ = -(B4 ℓ) := sorry

-- Hence (B^(4)_ℓ)^n = (-1)^{n-1} B^(4)_ℓ for n ≥ 1
theorem B4_power (ℓ : ZMod 5) (hℓ : ℓ ≠ 0) (n : ℕ) (hn : n ≥ 1) :
  B4 ℓ ^ n = (-1 : ℂ)^(n-1) • B4 ℓ := sorry

-- Powers are uniformly bounded
theorem B4_power_bounded (ℓ : ZMod 5) (hℓ : ℓ ≠ 0) :
  ∃ C : ℝ, ∀ n : ℕ, ‖B4 ℓ ^ n‖ ≤ C := sorry
```

## Computational Verification
```lean
-- ω computation
example : ω ^ 5 = 1 := by norm_num [ω, Complex.exp_nat_mul]

-- Sum verification (may need native_decide or norm_num)
example : (1 : ℂ) + ω + ω^2 + ω^3 + ω^4 = 0 := by
  -- This follows from ω being a primitive 5th root of unity
  sorry
```

## Notes
- Use Mathlib's `Matrix.spectrum` for eigenvalues
- The rank-1 structure means eigenvalue = trace = row sum
- Key insight: rank-1 matrices are automatically semisimple (no Jordan blocks)
- This explains why ρ = 1 gives O(1) bounds, not polynomial growth
