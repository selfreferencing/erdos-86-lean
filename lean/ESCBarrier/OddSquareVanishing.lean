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

/-! ## The Vanishing Theorem for m = 4 (Classical ESC)

**Written proof reference**: Elsholtz-Tao Prop 1.6
-/

/-- Step 1: Odd squares satisfy n ≡ 1 (mod 8)
**Written proof**: "For odd square n = k², we have n ≡ 1 (mod 8)"

Proof: If k = 2m + 1, then k² = 4m² + 4m + 1 = 4m(m+1) + 1.
Since m(m+1) is even, k² = 8j + 1 for some j.
-/
lemma odd_square_mod_eight (k : ℕ) (hk : Odd k) : k^2 % 8 = 1 := by
  -- k is odd means k = 2m + 1 for some m
  obtain ⟨m, rfl⟩ := hk
  -- k² = (2m+1)²
  ring_nf
  -- (2*m + 1)^2 = 4*m^2 + 4*m + 1 = 4*m*(m+1) + 1
  -- Since m*(m+1) is even, we have 4*m*(m+1) ≡ 0 (mod 8)
  -- Key insight: m and m+1 are consecutive, so one is even
  have h_even : Even (m * (m + 1)) := by
    cases' Nat.even_or_odd m with hm_even hm_odd
    · -- m is even
      exact Even.mul_of_left hm_even
    · -- m is odd, so m+1 is even
      have : Even (m + 1) := Nat.odd_iff_not_even.mp hm_odd ▸ Nat.even_add_one
      exact Even.mul_of_right this
  -- Since m*(m+1) is even, 4*m*(m+1) ≡ 0 (mod 8)
  obtain ⟨j, hj⟩ := h_even
  -- Compute the modulo
  calc (2 * m + 1) ^ 2 % 8
      = (4 * m * m + 4 * m + 1) % 8 := by ring_nf; rfl
    _ = (4 * (m * (m + 1)) + 1) % 8 := by ring_nf
    _ = (4 * (2 * j) + 1) % 8 := by rw [hj]
    _ = (8 * j + 1) % 8 := by ring_nf
    _ = 1 := by omega

/-- Step 2: From 4abd = ne + 1 with n ≡ 1 (mod 8), derive e ≡ 3 (mod 4)
**Written proof**: "4abd ≡ 0 (mod 4), so ne + 1 ≡ 0 (mod 4), thus e ≡ 3 (mod 4)"
-/
lemma typeI_forces_e_mod_four (cert : TypeICert) (k : ℕ) (hk : Odd k)
    (h : typeI_holds 4 (k^2) cert) : (cert.e : ℕ) % 4 = 3 := by
  -- From typeI_holds: 4 * a * b * d = k^2 * e + 1
  unfold typeI_holds at h
  -- k^2 ≡ 1 (mod 4) for odd k
  have k2_mod : k^2 % 4 = 1 := by
    obtain ⟨m, rfl⟩ := hk
    calc (2 * m + 1) ^ 2 % 4
        = (4 * m * m + 4 * m + 1) % 4 := by ring_nf; rfl
      _ = 1 := by omega
  -- From h: 4*a*b*d = k^2*e + 1, taking mod 4 on both sides
  -- LHS ≡ 0 (mod 4), so k^2*e + 1 ≡ 0 (mod 4)
  have h_mod : (k^2 * (cert.e : ℕ) + 1) % 4 = 0 := by
    have : 4 * cert.a * cert.b * cert.d = k^2 * cert.e + 1 := h
    calc (k^2 * (cert.e : ℕ) + 1) % 4
        = (4 * cert.a * cert.b * cert.d) % 4 := by rw [← this]
      _ = 0 := by omega
  -- Since k^2 ≡ 1 (mod 4), we have e + 1 ≡ 0 (mod 4)
  have : ((cert.e : ℕ) + 1) % 4 = 0 := by
    have : (k^2 % 4 * (cert.e : ℕ) + 1) % 4 = (k^2 * (cert.e : ℕ) + 1) % 4 := by
      rw [Nat.mul_mod, Nat.add_mod]
    rw [k2_mod] at this
    simpa using h_mod
  -- Therefore e ≡ 3 (mod 4)
  omega

/-- Step 3: The quadratic reciprocity contradiction
**Written proof**: "With e ≡ 3 (mod 4), reciprocity gives (q/e) = 1 but (ab/e) = -1"

This requires:
1. Decomposing e = a + b into prime factors
2. Applying quadratic reciprocity law for each prime p | e
3. Showing the Legendre symbol computation yields (-1) for at least one p
4. Deriving contradiction from 4abd = ne + 1
-/
lemma reciprocity_contradiction (cert : TypeICert) (k : ℕ) (hk : Odd k)
    (h_e : (cert.e : ℕ) % 4 = 3) : False := by
  -- Would use: legendreSymQuadraticReciprocity from Mathlib
  sorry

/-- Main Theorem: Type I solutions vanish at odd squares for m = 4
**Written proof**: Elsholtz-Tao Proposition 1.6
-/
theorem typeI_vanishes_at_odd_squares_m4 (k : ℕ) (hk : Odd k) :
    ∀ cert : TypeICert, ¬typeI_holds 4 (k^2) cert := by
  intro cert h
  -- Step 2: Derive e ≡ 3 (mod 4)
  have h_e := typeI_forces_e_mod_four cert k hk h
  -- Step 3: Get contradiction from reciprocity
  exact reciprocity_contradiction cert k hk h_e

/-- Main Theorem: Type II solutions vanish at odd squares for m = 4 -/
theorem typeII_vanishes_at_odd_squares_m4 (k : ℕ) (hk : Odd k) :
    ∀ cert : TypeIICert, ¬typeII_holds 4 (k^2) cert := by
  sorry

/-! ## Generalization to 4 | m

**Written proof reference**: Type_I_II_Generalization.md, "Why 4 | m is the Condition"
-/

/-- When 4 | m, the same argument applies -/
theorem typeI_vanishes_when_four_divides (m : ℕ) (hm : 4 ∣ m) (k : ℕ) (hk : Odd k) :
    ∀ cert : TypeICert, ¬typeI_holds m (k^2) cert := by
  intro cert h
  -- Since 4 | m, write m = 4 * q for some q
  obtain ⟨q, rfl⟩ := hm
  -- From typeI_holds: (4*q) * a * b * d = k^2 * e + 1
  unfold typeI_holds at h
  -- Rearrange: 4 * (q*a*b*d) = k^2 * e + 1
  -- This has the same form as the m = 4 case with d' = q*a*b*d
  -- k^2 ≡ 1 (mod 4), so we get e ≡ 3 (mod 4) by the same argument
  have h_e : (cert.e : ℕ) % 4 = 3 := by
    have k2_mod : k^2 % 4 = 1 := by
      obtain ⟨j, rfl⟩ := hk
      calc (2 * j + 1) ^ 2 % 4
          = (4 * j * j + 4 * j + 1) % 4 := by ring_nf; rfl
        _ = 1 := by omega
    have : 4 * q * cert.a * cert.b * cert.d = k^2 * cert.e + 1 := h
    have h_mod : (k^2 * (cert.e : ℕ) + 1) % 4 = 0 := by
      calc (k^2 * (cert.e : ℕ) + 1) % 4
          = (4 * q * cert.a * cert.b * cert.d) % 4 := by rw [← this]
        _ = 0 := by omega
    omega
  -- Apply the reciprocity contradiction (same as m = 4 case)
  exact reciprocity_contradiction cert k hk h_e

theorem typeII_vanishes_when_four_divides (m : ℕ) (hm : 4 ∣ m) (k : ℕ) (hk : Odd k) :
    ∀ cert : TypeIICert, ¬typeII_holds m (k^2) cert := by
  intro cert h
  -- Since 4 | m, write m = 4 * q for some q
  obtain ⟨q, rfl⟩ := hm
  -- From typeII_holds: (4*q) * a * b * d = k^2 + e
  unfold typeII_holds at h
  -- This is 4 * (q*a*b*d) = k^2 + e
  -- Similar to Type I, this forces e ≡ 3 (mod 4)
  -- The reciprocity argument would then apply
  -- For now, reduce to the m = 4 case
  have : 4 * (q * cert.a * cert.b * cert.d) = k^2 + cert.e := by
    calc 4 * (q * cert.a * cert.b * cert.d)
        = 4 * q * cert.a * cert.b * cert.d := by ring
      _ = k^2 + cert.e := h
  -- Apply typeII_vanishes_at_odd_squares_m4 to the cert' with d' = q*a*b*d
  -- This requires constructing a TypeIICert for m = 4, which has the same e
  -- The contradiction comes from the same e ≡ 3 (mod 4) argument
  sorry
