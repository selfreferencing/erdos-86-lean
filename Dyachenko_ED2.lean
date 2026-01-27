/-
Dyachenko ED2 Method - Corrected Implementation

Based on: E. Dyachenko, "Constructive Proofs of the Erdős–Straus Conjecture
for Prime Numbers of the Form P ≡ 1 (mod 4)", arXiv:2511.07465 (2025).

The key insight from the paper:
- ED2 uses the identity: (4b - 1)(4c - 1) = 4Pδ + 1
- NOT a lattice rectangle intersection, but a FACTORIZATION search
- For squarefree α and d' ∈ ℕ: factor N = 4αPd'² + 1 into X·Y
- Recover b, c from X, Y via: b' = (X+1)/(4αd'), c' = (Y+1)/(4αd')
-/

import Mathlib

namespace DyachenkoED2

/-! ## Part 1: ED2 Algebraic Identity -/

/-- The ED2 identity: if (4b-1)(4c-1) = 4Pδ + 1 and δ | bc, then
    4/P = 1/A + 1/(bP) + 1/(cP) where A = bc/δ -/
theorem ED2_identity_rational {P b c δ : ℕ} (hP : P > 0) (hb : b > 0) (hc : c > 0) (hδ : δ > 0)
    (h_id : (4 * b - 1) * (4 * c - 1) = 4 * P * δ + 1)
    (h_div : δ ∣ b * c) :
    (4 : ℚ) / P = 1 / (b * c / δ) + 1 / (b * P) + 1 / (c * P) := by
  have hbc : b * c > 0 := Nat.mul_pos hb hc
  have hA : (b * c / δ : ℚ) > 0 := by positivity
  have hbP : (b * P : ℚ) > 0 := by positivity
  have hcP : (c * P : ℚ) > 0 := by positivity
  -- The algebraic identity follows from expanding and simplifying
  -- (4b-1)(4c-1) = 16bc - 4b - 4c + 1 = 4Pδ + 1
  -- => 16bc - 4b - 4c = 4Pδ
  -- => 4bc - b - c = Pδ
  -- => A(4bc - b - c) = Pbc  [where A = bc/δ]
  -- => 4Abc - Ab - Ac = Pbc
  -- => 4/P = (b+c)/(Pbc) + 1/A = 1/(cP) + 1/(bP) + 1/A
  field_simp
  -- After field_simp, we need to show the numerator equality
  have key : 4 * b * c - b - c = P * δ := by
    have expand : (4 * b - 1) * (4 * c - 1) = 16 * b * c - 4 * b - 4 * c + 1 := by ring
    omega
  -- Use the divisibility to express bc/δ
  obtain ⟨A, hA_eq⟩ := h_div
  -- A = bc/δ means bc = A * δ
  have hbc_eq : b * c = A * δ := hA_eq
  -- Now the algebra follows
  calc 4 * (↑A * ↑b * ↑P * (↑c * ↑P))
      = 4 * A * b * c * P * P := by ring
    _ = 4 * (A * δ) * P * P := by rw [← hbc_eq]; ring
    _ = 4 * b * c * P * P := by rw [hbc_eq]
    _ = (b + c + 4 * b * c - b - c) * P * P := by ring
    _ = (b + c) * P * P + (4 * b * c - b - c) * P * P := by ring
    _ = (b + c) * P * P + P * δ * P * P := by rw [key]
    _ = _ := by ring

/-- Type III x formula (for compatibility with existing code) -/
def type3_x (p offset : ℕ) : ℕ := (p + offset) / 4

/-! ## Part 2: ED2 Parameter Construction -/

/-- ED2 parameters are valid if they satisfy the identity and divisibility -/
structure ED2Params (P : ℕ) where
  δ : ℕ
  b : ℕ
  c : ℕ
  δ_pos : δ > 0
  b_pos : b > 0
  c_pos : c > 0
  identity : (4 * b - 1) * (4 * c - 1) = 4 * P * δ + 1
  divisibility : δ ∣ b * c

/-- Convert ED2 parameters to the Type III format used in the main ESC proof -/
def ED2Params.toType3 {P : ℕ} (params : ED2Params P) :
    ∃ offset c : ℕ,
      offset % 4 = 3 ∧
      c > 0 ∧
      (4 * c - 1) * offset > P ∧
      ((4 * c - 1) * offset - P) ∣ (4 * type3_x P offset * c * P) := by
  -- The ED2 solution gives: A = bc/δ, B = bP, C = cP
  -- We need to express this in Type III format
  -- Type III has: offset ≡ 3 (mod 4), and uses formulas from the main file
  sorry -- This requires careful translation between the two formats

/-! ## Part 3: Factorization-Based Construction -/

/-- For squarefree α and d' ∈ ℕ, the target number to factor -/
def targetN (P α d' : ℕ) : ℕ := 4 * α * P * d' * d' + 1

/-- Check if a factorization X * Y = N gives valid ED2 parameters -/
def isValidFactorization (P α d' X Y : ℕ) : Prop :=
  X * Y = targetN P α d' ∧
  X % (4 * α * d') = 4 * α * d' - 1 ∧  -- X ≡ -1 (mod 4αd')
  Y % (4 * α * d') = 4 * α * d' - 1 ∧  -- Y ≡ -1 (mod 4αd')
  (X + 1) % (4 * α * d') = 0 ∧         -- 4αd' | (X + 1)
  (Y + 1) % (4 * α * d') = 0           -- 4αd' | (Y + 1)

/-- Recover b' from X -/
def recoverB' (α d' X : ℕ) : ℕ := (X + 1) / (4 * α * d')

/-- Recover c' from Y -/
def recoverC' (α d' Y : ℕ) : ℕ := (Y + 1) / (4 * α * d')

/-- The full b parameter: b = g * b' where g = α * d' -/
def fullB (α d' X : ℕ) : ℕ := α * d' * recoverB' α d' X

/-- The full c parameter: c = g * c' where g = α * d' -/
def fullC (α d' Y : ℕ) : ℕ := α * d' * recoverC' α d' Y

/-- The δ parameter: δ = α * d'^2 -/
def deltaParam (α d' : ℕ) : ℕ := α * d' * d'

/-- If we have a valid factorization, we get valid ED2 parameters -/
theorem factorization_gives_ED2 (P α d' X Y : ℕ)
    (hP : Nat.Prime P) (hα : α > 0) (hd' : d' > 0)
    (hX : X > 0) (hY : Y > 0)
    (hvalid : isValidFactorization P α d' X Y) :
    ∃ params : ED2Params P,
      params.b = fullB α d' X ∧
      params.c = fullC α d' Y ∧
      params.δ = deltaParam α d' := by
  sorry

/-! ## Part 4: Existence Theorem -/

/-- Search for valid ED2 parameters by trying factorizations -/
def findED2Params (P : ℕ) (fuel : ℕ) : Option (ℕ × ℕ × ℕ) :=
  -- Try α = 1, then α = 2, 3, 5, 6, 7, ... (squarefree)
  -- For each α, try d' = 1, 2, 3, ...
  -- For each (α, d'), compute N and try factorizations
  match fuel with
  | 0 => none
  | fuel' + 1 =>
    -- Simple search: try small (α, d') pairs
    let candidates := [(1, 1), (1, 2), (1, 3), (2, 1), (1, 4), (3, 1), (2, 2), (1, 5)]
    candidates.findSome? fun (α, d') =>
      let N := targetN P α d'
      let g := 4 * α * d'
      -- Try divisors of N
      (List.range (Nat.sqrt N + 1)).findSome? fun i =>
        let X := i + 1
        if X > 0 && N % X = 0 then
          let Y := N / X
          if X ≤ Y && (X + 1) % g = 0 && (Y + 1) % g = 0 then
            let b := α * d' * ((X + 1) / g)
            let c := α * d' * ((Y + 1) / g)
            let δ := α * d' * d'
            -- Verify the construction
            if (4 * b - 1) * (4 * c - 1) = 4 * P * δ + 1 && b * c % δ = 0 then
              some (δ, b, c)
            else none
          else none
        else none

#eval findED2Params 5 100   -- Should find (1, 1, 2) giving A=2, B=5, C=10
#eval findED2Params 13 100  -- Should find something
#eval findED2Params 29 100  -- Paper example: (4, 4, 8) giving A=8, B=116, C=232
#eval findED2Params 53 100  -- Paper example: (9, 6, 21)
#eval findED2Params 73 100
#eval findED2Params 97 100

/-- Main existence theorem: For every prime P ≡ 1 (mod 4) with P ≥ 5,
    there exist valid ED2 parameters -/
theorem ED2_params_exist (P : ℕ) (hP : Nat.Prime P) (hmod : P % 4 = 1) (hge : P ≥ 5) :
    ∃ δ b c : ℕ,
      δ > 0 ∧ b > 0 ∧ c > 0 ∧
      (4 * b - 1) * (4 * c - 1) = 4 * P * δ + 1 ∧
      δ ∣ b * c := by
  -- The proof follows Dyachenko's Theorem 9.21/10.21
  -- For any P ≡ 1 (mod 4), there exists (α, d') such that
  -- N = 4αPd'² + 1 factors as X·Y with X ≡ Y ≡ -1 (mod 4αd')
  --
  -- The existence is guaranteed by:
  -- 1. Density of lattice points in the parametric box
  -- 2. Logarithmic convergence of the enumeration algorithm
  --
  -- For a constructive proof, we can use decide/native_decide for small P
  -- and appeal to the density argument for large P
  sorry

/-! ## Part 5: Connection to Type III (Main ESC Format) -/

/-- The ED2 solution gives a valid Egyptian fraction decomposition -/
theorem ED2_gives_egyptian_fraction (P : ℕ) (hP : Nat.Prime P) (hP_pos : P > 0)
    (δ b c : ℕ) (hδ : δ > 0) (hb : b > 0) (hc : c > 0)
    (h_id : (4 * b - 1) * (4 * c - 1) = 4 * P * δ + 1)
    (h_div : δ ∣ b * c) :
    ∃ A B C : ℕ, A > 0 ∧ B > 0 ∧ C > 0 ∧
      (4 : ℚ) / P = 1 / A + 1 / B + 1 / C := by
  use b * c / δ, b * P, c * P
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- A > 0
    exact Nat.div_pos (Nat.mul_pos hb hc) hδ
  · -- B > 0
    exact Nat.mul_pos hb hP_pos
  · -- C > 0
    exact Nat.mul_pos hc hP_pos
  · -- The Egyptian fraction identity
    have hbc := Nat.mul_pos hb hc
    obtain ⟨k, hk⟩ := h_div
    -- bc = k * δ, so bc/δ = k
    have hA : b * c / δ = k := by
      rw [hk]
      exact Nat.mul_div_cancel_left k hδ
    -- Now apply the ED2 identity
    simp only [hA]
    -- Need: 4/P = 1/k + 1/(bP) + 1/(cP)
    have key : 4 * b * c - b - c = P * δ := by
      have expand : (4 * b - 1) * (4 * c - 1) = 16 * b * c - 4 * b - 4 * c + 1 := by ring
      rw [expand] at h_id
      omega
    field_simp
    -- After clearing denominators, need algebraic identity
    calc 4 * (↑k * (↑b * ↑P) * (↑c * ↑P))
        = 4 * k * b * c * P * P := by ring
      _ = 4 * (k * δ) * P * P := by ring
      _ = 4 * b * c * P * P := by rw [← hk]
      _ = (4 * b * c) * P * P := by ring
      _ = (b + c + (4 * b * c - b - c)) * P * P := by ring
      _ = (b + c) * P * P + (P * δ) * P * P := by rw [key]; ring
      _ = ↑b * ↑P * (↑c * ↑P) + ↑c * ↑P * (↑k * (↑b * ↑P)) + ↑b * ↑P * (↑k * (↑c * ↑P)) := by
          rw [hk]; ring

/-! ## Part 6: The Main Theorem (Dyachenko's Theorem 10.21) -/

/-- Dyachenko's Theorem 10.21: For every prime P ≡ 1 (mod 4), the Erdős-Straus
    conjecture holds via the ED2 construction -/
theorem dyachenko_theorem_10_21 (P : ℕ) (hP : Nat.Prime P) (hmod : P % 4 = 1) (hge : P ≥ 5) :
    ∃ A B C : ℕ, A > 0 ∧ B > 0 ∧ C > 0 ∧
      (4 : ℚ) / P = 1 / A + 1 / B + 1 / C := by
  obtain ⟨δ, b, c, hδ, hb, hc, h_id, h_div⟩ := ED2_params_exist P hP hmod hge
  exact ED2_gives_egyptian_fraction P hP (Nat.Prime.pos hP) δ b c hδ hb hc h_id h_div

/-! ## Part 7: Conversion to Type III Format (for main ESC file) -/

/-- The statement expected by the main ESC file -/
theorem dyachenko_type3_existence (p : ℕ) (hp : Nat.Prime p)
    (hp_mod : p % 4 = 1) (hp_ge : p ≥ 5) :
    ∃ offset c : ℕ,
      offset % 4 = 3 ∧
      c > 0 ∧
      (4 * c - 1) * offset > p ∧
      ((4 * c - 1) * offset - p) ∣ (4 * type3_x p offset * c * p) := by
  -- This requires translating between ED2 format and Type III format
  -- The ED2 gives: A = bc/δ, B = bP, C = cP with (4b-1)(4c-1) = 4Pδ+1
  -- Type III uses: offset ≡ 3 (mod 4), and specific formulas
  --
  -- The translation is non-trivial and requires matching the algebraic structures
  -- For now, we prove this via the ED2 existence + format conversion
  sorry

end DyachenkoED2
