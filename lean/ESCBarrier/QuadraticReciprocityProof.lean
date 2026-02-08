/-
# Quadratic Reciprocity Proof for Construction (1,1,2)

Prove that construction (1,1,2) covers m ≡ 1,3 (mod 8) using quadratic reciprocity.

**Goal**: ∀ m with m % 8 ∈ {1,3} and 4∤m, ∃ odd k with k²·2+1 ≡ 0 (mod m)

**Strategy**:
1. Show -1/2 is a quadratic residue mod m
2. Find k with k² ≡ -1/2 (mod m)
3. Ensure k can be chosen odd
-/

import Mathlib.NumberTheory.Legendre.JacobiSymbol
import Mathlib.NumberTheory.Legendre.QuadraticReciprocity
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-! ## Setup -/

/-- A construction (a, b, e) works for m if the QR condition is satisfiable -/
def constructionWorks (a b e m : ℕ) : Prop :=
  ∃ k : ℕ, Odd k ∧ (k^2 * e + 1) % (m * a * b) = 0

/-! ## Prime Case -/

/-- For odd prime p ≡ 1 (mod 8), show 2 is a QR -/
lemma two_is_QR_mod8_is_1 (p : ℕ) (hp : p.Prime) (h_mod : p % 8 = 1) :
    ∃ x : ZMod p, x^2 = 2 := by
  -- By quadratic reciprocity: (2/p) = 1 iff p ≡ ±1 (mod 8)
  -- Since p % 8 = 1, we have (2/p) = 1
  sorry

/-- For odd prime p ≡ 1 (mod 8), construction (1,1,2) works -/
lemma prime_mod8_is_1_works (p : ℕ) (hp : p.Prime) (hp_odd : Odd p) (h_mod : p % 8 = 1) :
    constructionWorks 1 1 2 p := by
  unfold constructionWorks
  -- Need: k²·2 + 1 ≡ 0 (mod p), i.e., k² ≡ -1/2 (mod p)

  -- Step 1: Show 2 is a QR mod p
  obtain ⟨x, hx⟩ := two_is_QR_mod8_is_1 p hp h_mod

  -- Step 2: Show -1 is a QR mod p (since p ≡ 1 (mod 4))
  have h_neg1_qr : ∃ y : ZMod p, y^2 = -1 := by
    sorry -- Use (−1/p) = (−1)^((p−1)/2) = 1 when p ≡ 1 (mod 4)

  -- Step 3: Multiply to get (y/x)² = -1/2
  obtain ⟨y, hy⟩ := h_neg1_qr
  have h_div : (2 : ZMod p) ≠ 0 := by
    sorry -- 2 ≠ 0 mod p since p is odd prime

  have : ∃ z : ZMod p, z^2 = -1/2 := by
    use y / x
    field_simp
    sorry

  -- Step 4: Convert ZMod p solution to natural number
  obtain ⟨z, hz⟩ := this
  use z.val
  constructor
  · sorry -- Show z.val is odd (or replace with p - z.val if even)
  · sorry -- Show (z.val)²·2 + 1 ≡ 0 (mod p)

/-- For prime p ≡ 3 (mod 8), direct computational witnesses exist -/
lemma prime_mod8_is_3_works (p : ℕ) (hp : p.Prime) (hp_odd : Odd p) (h_mod : p % 8 = 3) :
    constructionWorks 1 1 2 p := by
  unfold constructionWorks
  -- For small primes p ≡ 3 (mod 8), we have explicit witnesses:
  -- p=3: k=1, p=11: k=7, p=19: k=3, p=43: k=35, etc.

  -- The general proof requires showing that -1/2 is a QR mod p
  -- even when (2/p) = -1 (which happens for p ≡ 3 (mod 8))

  -- Key insight: k²·2 ≡ -1 (mod p) is solvable when certain conditions hold
  sorry

/-! ## Composite Case via CRT -/

/-- For m with multiple prime factors, use CRT -/
lemma composite_mod8_works (m : ℕ)
    (hm_pos : 0 < m)
    (hm_mod : m % 8 = 1 ∨ m % 8 = 3)
    (hm_not4 : ¬ 4 ∣ m) :
    constructionWorks 1 1 2 m := by
  -- Decompose m into prime powers
  -- For each prime power p^k dividing m:
  --   1. Solve k²·2 + 1 ≡ 0 (mod p) using prime case
  --   2. Lift to k²·2 + 1 ≡ 0 (mod p^k) using Hensel
  -- Use CRT to combine solutions
  -- Ensure final k is odd (if not, adjust by adding m)
  sorry

/-! ## Main Theorem -/

/-- Construction (1,1,2) covers all m ≡ 1,3 (mod 8) with 4∤m -/
theorem construction_112_covers_mod8_classes (m : ℕ)
    (hm_pos : 0 < m)
    (hm_mod : m % 8 = 1 ∨ m % 8 = 3)
    (hm_not4 : ¬ 4 ∣ m) :
    constructionWorks 1 1 2 m := by
  -- Split by whether m is prime or composite
  by_cases h_prime : m.Prime
  · -- Prime case
    have h_odd : Odd m := by
      by_contra h_even
      have : m = 2 := Nat.Prime.eq_two_or_odd h_prime |>.resolve_right h_even
      subst this
      omega  -- 2 % 8 = 2 ≠ 1,3
    rcases hm_mod with h1 | h3
    · exact prime_mod8_is_1_works m h_prime h_odd h1
    · exact prime_mod8_is_3_works m h_prime h_odd h3
  · -- Composite case
    exact composite_mod8_works m hm_pos hm_mod hm_not4

/-! ## Explicit Certificates -/

/-- Certificate: m=17 with k=5 -/
example : constructionWorks 1 1 2 17 := by
  use 5
  decide

/-- Certificate: m=41 with k=15 -/
example : constructionWorks 1 1 2 41 := by
  use 15
  decide

/-- Certificate: m=3 with k=1 -/
example : constructionWorks 1 1 2 3 := by
  use 1
  decide

/-- Certificate: m=11 with k=7 -/
example : constructionWorks 1 1 2 11 := by
  use 7
  decide

/-- Certificate: m=19 with k=3 -/
example : constructionWorks 1 1 2 19 := by
  use 3
  decide

/-- Certificate: m=27 with k=11 -/
example : constructionWorks 1 1 2 27 := by
  use 11
  decide

/-- Certificate: m=43 with k=35 -/
example : constructionWorks 1 1 2 43 := by
  use 35
  decide

/-! ## Summary

**Sorries remaining**: 5
1. two_is_QR_mod8_is_1 — Use legendreSymQuadraticReciprocity
2. h_neg1_qr in prime_mod8_is_1_works — Use Legendre symbol for -1
3-4. Conversion from ZMod to ℕ with odd constraint
5. prime_mod8_is_3_works — Trickier case, may need special argument
6. composite_mod8_works — CRT + Hensel lifting

**Key dependencies from Mathlib:**
- ZMod.isSquare_neg_one_iff : (-1 is a square) ↔ (p ≡ 1 (mod 4))
- legendreSymQuadraticReciprocity : Relates (a/p) and (p/a)
- ZMod.exists_sq_eq_two_iff : (2 is a square) ↔ (p ≡ ±1 (mod 8))

**Next steps:**
1. Use Mathlib quadratic reciprocity lemmas
2. Handle odd constraint via "if k even, use -k or k+m"
3. Submit to Aristotle for automated completion
-/
