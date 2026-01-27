# Lean Formalization Prompt 4: Fourier Analysis and Character Sums

## Task
Create Lean 4 code formalizing the Fourier analysis connecting spectral bounds to killed-index uniformity.

## Context
The spectral radius ρ(M_ℓ) = 1 implies character sums are bounded, which implies killed-index uniformity via Fourier inversion.

## Required Definitions

```lean
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Tactic

namespace Zeroless

-- Character sum F_k(ℓ) = ∑_{r ∈ S_k} e(ℓ · u_{k+1}(r) / 5^{k+1})
-- For our purposes, this is the twisted sum over survivors

-- Survivor count (given, not proved here)
axiom survivor_count (k : ℕ) (hk : k ≥ 1) : ℕ
axiom survivor_count_formula (k : ℕ) (hk : k ≥ 1) :
  survivor_count k hk = 4 * (9/2)^(k-1)  -- Approximately 4 × 4.5^{k-1}

-- Character sum (abstract, connected to transfer operator)
axiom F (k : ℕ) (ℓ : ZMod 5) : ℂ
```

## Required Theorems

### 1. Character Sum Bound
```lean
-- Main theorem: |F_k(ℓ)| is bounded for ℓ ≠ 0
-- This follows from ρ(M_ℓ) = 1 and power boundedness
theorem F_bounded (k : ℕ) (hk : k ≥ 1) (ℓ : ZMod 5) (hℓ : ℓ ≠ 0) :
  ∃ C : ℝ, C > 0 ∧ Complex.abs (F k ℓ) ≤ C := sorry

-- Explicit bound: |F_k(ℓ)| ≤ C for absolute constant C
-- (The GPT responses gave C ∈ {4, 5, 16} depending on normalization)
axiom F_explicit_bound : ∃ C : ℝ, C > 0 ∧ ∀ k ℓ, k ≥ 1 → ℓ ≠ (0 : ZMod 5) →
  Complex.abs (F k ℓ) ≤ C
```

### 2. Fourier Inversion Setup
```lean
-- The "good" set A_k (child-0 survives) has size approximately 0.9 |S_k|
-- We prove this via Fourier inversion

-- Indicator of "killed" set (digit = 0) in ZMod (5^{k+1})
def killed_indicator (k : ℕ) : ZMod (5^(k+1)) → ℂ := sorry

-- Fourier transform of killed indicator
def killed_fourier (k : ℕ) (ℓ : ZMod (5^(k+1))) : ℂ :=
  ∑ x : ZMod (5^(k+1)), killed_indicator k x * Complex.exp (2 * Real.pi * Complex.I * (ℓ.val * x.val) / 5^(k+1))

-- The killed set has size 5^k/2 = |ZMod (5^{k+1})| / 10
theorem killed_size (k : ℕ) :
  (Finset.filter (fun x => killed_indicator k x ≠ 0) Finset.univ).card = 5^k / 2 := sorry
```

### 3. Discrepancy Bound (THE KEY CONNECTION)
```lean
-- |A_k|/|S_k| - 9/10 is controlled by character sums
-- Via Fourier inversion: discrepancy ≤ (1/|S_k|) × ∑_{ℓ≠0} |F_k(ℓ)| × |ĝ(ℓ)|

theorem discrepancy_bound (k : ℕ) (hk : k ≥ 1) :
  ∃ D : ℝ, D > 0 ∧
  |((good_count k : ℝ) / survivor_count k hk) - 9/10| ≤ D / survivor_count k hk := sorry

-- Since |S_k| ~ 4.5^k grows exponentially, discrepancy → 0
theorem discrepancy_decay (k : ℕ) (hk : k ≥ 1) :
  ∃ C D : ℝ, C > 0 ∧ D > 0 ∧
  |((good_count k : ℝ) / survivor_count k hk) - 9/10| ≤ C * D / (4.5)^k := sorry
```

### 4. Explicit k_0 for 1% Accuracy
```lean
-- For k ≥ k_0, discrepancy ≤ 0.01
-- GPT responses gave k_0 ∈ {5, 8, 15} depending on constants

theorem k0_bound : ∃ k₀ : ℕ, ∀ k ≥ k₀,
  |((good_count k : ℝ) / survivor_count k (by omega)) - 9/10| ≤ 0.01 := sorry

-- Explicit: k_0 = 15 suffices (most conservative bound)
theorem k0_explicit : ∀ k ≥ 15,
  |((good_count k : ℝ) / survivor_count k (by omega)) - 9/10| ≤ 0.01 := sorry
```

### 5. Killed-Index Uniformity
```lean
-- Each of the 5 killed indices (j = 0,1,2,3,4) appears with probability 1/5
-- among 4-child survivors

-- Distribution of killed index among 4-child parents
def killed_index_dist (k : ℕ) (j : Fin 5) : ℝ := sorry

-- Uniformity theorem
theorem killed_index_uniform (k : ℕ) (hk : k ≥ 1) :
  ∀ j : Fin 5, |killed_index_dist k j - 1/5| ≤ (1/10) * (1/4.5)^k := sorry

-- Specifically: |A_k|/|S_k| - 9/10| → 0 exponentially
-- (A_k = survivors whose child-0 survives = complement of killed_index = 0)
```

### 6. Rel-0C (Cylinder Version)
```lean
-- The same bounds hold within any cylinder (conditioning on history)
-- This is because the spectral gap is uniform over initial states

-- Cylinder: fixing forced-tail history at levels 1, ..., d
def cylinder (k d : ℕ) (history : Fin d → Fin 5) : Set ℕ := sorry

-- Conditional discrepancy bound
theorem cylinder_discrepancy (k d : ℕ) (hk : k ≥ d) (history : Fin d → Fin 5) :
  ∃ C : ℝ, C > 0 ∧
  |(conditional_good_ratio k (cylinder k d history)) - 9/10| ≤ C / (4.5)^(k-d) := sorry
```

## Connection to Main Theorem
```lean
-- Combining all pieces:
-- 1. Character sums bounded (from spectral analysis)
-- 2. Discrepancy → 0 exponentially (from Fourier inversion)
-- 3. Same within cylinders (uniform spectral gap)
-- 4. Digit Squeeze constrains candidates to [2, 3.32k)
-- 5. Direct verification for k ≤ 27

-- Therefore: no zeroless 2^n for n > 86
```

## Notes
- This module depends on the transfer operator spectral analysis (Prompt 3)
- The Fourier analysis is standard; the key is connecting it to the spectral bound
- Mathlib has good support for Fourier analysis on finite groups
- The "Rel-0C" (relative/cylinder) version is crucial for the forced-tail decay argument
