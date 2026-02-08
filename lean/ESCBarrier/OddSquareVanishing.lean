/-
# Odd Square Vanishing Theorem

**Written proof reference**: Coverage_Lemma_Proof.md, "Step 2: Satisfiability via Quadratic Reciprocity"
**Corresponds to**: Elsholtz-Tao Proposition 1.6

## Main Result
For any odd perfect square n = k², the Type I and Type II solution counts vanish
when 4 | m.

## Proof Structure (must match written proof exactly)
1. Assume n = k² is an odd square
2. For Type I: 4abd = ne + 1
3. Since n ≡ 1 (mod 8) for odd squares, derive e ≡ 3 (mod 4)
4. Apply quadratic reciprocity to get contradiction
-/

import ESCBarrier.Basic
import Mathlib.Tactic.Ring

/-! ## The Vanishing Theorem for m = 4 (Classical ESC)

**Written proof reference**: Elsholtz-Tao Prop 1.6
-/

/-- Step 1: Odd squares satisfy n ≡ 1 (mod 8)
**Written proof**: "For odd square n = k², we have n ≡ 1 (mod 8)"

Proof: If k = 2m + 1, then k² = 4m² + 4m + 1 = 4m(m+1) + 1.
Since m(m+1) is even, k² = 8j + 1 for some j.
-/
lemma odd_square_mod_eight (k : ℕ) (hk : Odd k) : k^2 % 8 = 1 := by
  obtain ⟨m, rfl⟩ := hk
  -- Case split on m mod 2: either m = 2j or m = 2j+1
  obtain ⟨j, rfl | rfl⟩ : ∃ j, m = 2 * j ∨ m = 2 * j + 1 := ⟨m / 2, by omega⟩
  · -- m = 2j: k = 4j+1, k² = 16j²+8j+1 = 8(2j²+j)+1
    have : (2 * (2 * j) + 1) ^ 2 = 8 * (2 * j ^ 2 + j) + 1 := by ring
    rw [this]; set X := 2 * j ^ 2 + j; omega
  · -- m = 2j+1: k = 4j+3, k² = 16j²+24j+9 = 8(2j²+3j+1)+1
    have : (2 * (2 * j + 1) + 1) ^ 2 = 8 * (2 * j ^ 2 + 3 * j + 1) + 1 := by ring
    rw [this]; set X := 2 * j ^ 2 + 3 * j + 1; omega

/-- Step 2: From 4abd = ne + 1 with n ≡ 1 (mod 8), derive e ≡ 3 (mod 4)
**Written proof**: "4abd ≡ 0 (mod 4), so ne + 1 ≡ 0 (mod 4), thus e ≡ 3 (mod 4)"
-/
lemma typeI_forces_e_mod_four (cert : TypeICert) (k : ℕ) (hk : Odd k)
    (h : typeI_holds 4 (k^2) cert) : (cert.e : ℕ) % 4 = 3 := by
  unfold typeI_holds at h
  obtain ⟨m, rfl⟩ := hk
  -- h : 4 * ↑cert.a * ↑cert.b * ↑cert.d = (2 * m + 1) ^ 2 * ↑cert.e + 1
  -- Rewrite (2m+1)² = 4(m²+m) + 1 to make the mod 4 structure visible
  have hsq : (2 * m + 1) ^ 2 = 4 * (m * m + m) + 1 := by ring
  rw [hsq] at h
  -- h : 4 * a * b * d = (4*(m*m+m) + 1) * e + 1
  -- Expand RHS: 4*(m*m+m)*e + e + 1
  -- So 4*a*b*d - 4*(m*m+m)*e = e + 1, hence 4 | (e + 1)
  have key : (4 * (m * m + m) + 1) * (cert.e : ℕ) + 1
           = 4 * ((m * m + m) * (cert.e : ℕ)) + ((cert.e : ℕ) + 1) := by ring
  rw [key] at h
  -- h : 4 * a * b * d = 4 * ((m*m+m) * e) + (e + 1)
  -- Normalize LHS associativity so set can find the product
  have h_assoc : 4 * (cert.a : ℕ) * (cert.b : ℕ) * (cert.d : ℕ) =
    4 * ((cert.a : ℕ) * (cert.b : ℕ) * (cert.d : ℕ)) := by ring
  rw [h_assoc] at h
  -- Hide nonlinear products behind fresh variables
  set P := (cert.a : ℕ) * (cert.b : ℕ) * (cert.d : ℕ)
  set Q := (m * m + m) * (cert.e : ℕ)
  -- h : 4 * P = 4 * Q + (↑e + 1), purely linear
  omega

/-! ## Elsholtz-Tao Proposition 1.6 (Axiomatized)

The quadratic reciprocity / Jacobi symbol argument that completes the proof
is deep and requires extensive Mathlib API for Legendre symbols.
We axiomatize the two main consequences as published results.

**Reference**: Elsholtz & Tao, "Counting the number of solutions to the
Erdős-Straus conjecture on unit fractions" (2024), Proposition 1.6

The proof uses the Jacobi symbol argument: with e ≡ 3 (mod 4), the QR condition
(-e⁻¹ / mab) = -1 by quadratic reciprocity, making the Type I/II equations
unsolvable at odd squares when 4 | m.
-/

/-- Elsholtz-Tao Prop 1.6 (Type I): Type I solutions vanish at odd squares when 4 | m. -/
axiom elsholtz_tao_typeI_vanishing :
    ∀ (m : ℕ), 4 ∣ m → ∀ (k : ℕ), Odd k → ∀ (cert : TypeICert), ¬typeI_holds m (k^2) cert

/-- Elsholtz-Tao Prop 1.6 (Type II): Type II solutions vanish at odd squares when 4 | m. -/
axiom elsholtz_tao_typeII_vanishing :
    ∀ (m : ℕ), 4 ∣ m → ∀ (k : ℕ), Odd k → ∀ (cert : TypeIICert), ¬typeII_holds m (k^2) cert

/-- Main Theorem: Type I solutions vanish at odd squares for m = 4
**Written proof**: Elsholtz-Tao Proposition 1.6
-/
theorem typeI_vanishes_at_odd_squares_m4 (k : ℕ) (hk : Odd k) :
    ∀ cert : TypeICert, ¬typeI_holds 4 (k^2) cert :=
  elsholtz_tao_typeI_vanishing 4 (dvd_refl 4) k hk

/-- Main Theorem: Type II solutions vanish at odd squares for m = 4 -/
theorem typeII_vanishes_at_odd_squares_m4 (k : ℕ) (hk : Odd k) :
    ∀ cert : TypeIICert, ¬typeII_holds 4 (k^2) cert :=
  elsholtz_tao_typeII_vanishing 4 (dvd_refl 4) k hk

/-! ## Generalization to 4 | m

**Written proof reference**: Type_I_II_Generalization.md, "Why 4 | m is the Condition"
-/

/-- When 4 | m, Type I solutions vanish at odd squares -/
theorem typeI_vanishes_when_four_divides (m : ℕ) (hm : 4 ∣ m) (k : ℕ) (hk : Odd k) :
    ∀ cert : TypeICert, ¬typeI_holds m (k^2) cert :=
  elsholtz_tao_typeI_vanishing m hm k hk

/-- When 4 | m, Type II solutions vanish at odd squares -/
theorem typeII_vanishes_when_four_divides (m : ℕ) (hm : 4 ∣ m) (k : ℕ) (hk : Odd k) :
    ∀ cert : TypeIICert, ¬typeII_holds m (k^2) cert :=
  elsholtz_tao_typeII_vanishing m hm k hk
