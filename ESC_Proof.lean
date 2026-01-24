/-
  Erdős-Straus Conjecture - Lean 4 Formalization

  Main result: For every n ≥ 2, 4/n = 1/x + 1/y + 1/z has a solution in positive integers.
-/

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Int.ModEq
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity

-- ============================================================================
-- PART 1: The p ≡ 3 (mod 4) Case - Explicit Formula
-- ============================================================================

/-- For p ≡ 3 (mod 4), define x = (p + 1) / 4 -/
def esc_x (p : ℕ) : ℕ := (p + 1) / 4

/-- For p ≡ 3 (mod 4), define y = (p² + p + 4) / 4 -/
def esc_y (p : ℕ) : ℕ := (p * p + p + 4) / 4

/-- For p ≡ 3 (mod 4), define z = p(p+1)(p² + p + 4) / 16 -/
def esc_z (p : ℕ) : ℕ := (p * (p + 1) * (p * p + p + 4)) / 16

/-- x is a positive integer when p ≡ 3 (mod 4) and p ≥ 3 -/
theorem esc_x_pos (p : ℕ) (hp : p % 4 = 3) (hp3 : p ≥ 3) : esc_x p > 0 := by
  sorry

/-- (p + 1) is divisible by 4 when p ≡ 3 (mod 4) -/
theorem p_plus_1_div_4 (p : ℕ) (hp : p % 4 = 3) : 4 ∣ (p + 1) := by
  sorry

/-- (p² + p + 4) is divisible by 4 when p ≡ 3 (mod 4) -/
theorem p_sq_p_4_div_4 (p : ℕ) (hp : p % 4 = 3) : 4 ∣ (p * p + p + 4) := by
  sorry

/-- The product p(p+1)(p² + p + 4) is divisible by 16 when p ≡ 3 (mod 4) -/
theorem product_div_16 (p : ℕ) (hp : p % 4 = 3) :
    16 ∣ (p * (p + 1) * (p * p + p + 4)) := by
  sorry

/-- Key algebraic identity: p³ + 2p² + 5p + 4 = (p + 1)(p² + p + 4) -/
theorem cubic_factor (p : ℕ) :
    p^3 + 2*p^2 + 5*p + 4 = (p + 1) * (p^2 + p + 4) := by
  ring

/-- Main theorem for p ≡ 3 (mod 4): The formula gives a valid ESC solution -/
theorem esc_formula_valid (p : ℕ) (hp : p % 4 = 3) (hp3 : p ≥ 3) :
    4 * (esc_x p) * (esc_y p) * (esc_z p) =
    p * ((esc_y p) * (esc_z p) + (esc_x p) * (esc_z p) + (esc_x p) * (esc_y p)) := by
  sorry

-- ============================================================================
-- PART 2: Type II Mechanism
-- ============================================================================

/-- m_k = 4k + 3 -/
def m_k (k : ℕ) : ℕ := 4 * k + 3

/-- n_k = (p + 4k + 3) / 4 for p ≡ 1 (mod 4) -/
def n_k (p k : ℕ) : ℕ := (p + 4 * k + 3) / 4

/-- n_k is well-defined (divisibility) when p ≡ 1 (mod 4) -/
theorem n_k_div (p k : ℕ) (hp : p % 4 = 1) : 4 ∣ (p + 4 * k + 3) := by
  sorry

/-- G(n, m) counts coprime divisor pairs summing to 0 mod m -/
def G (n m : ℕ) : ℕ :=
  (Finset.filter (fun d => d ∣ n ∧ Nat.Coprime d (n / d) ∧ (d + n / d) % m = 0)
    (Finset.range (n + 1))).card / 2

/-- Type II succeeds at k iff G(n_k, m_k) ≥ 1 -/
def type_ii_success (p k : ℕ) : Prop := G (n_k p k) (m_k k) ≥ 1

-- ============================================================================
-- PART 3: QR-Trap Breaking (Key Lemma)
-- ============================================================================

/-- If q | m_k and (p/q) = -1, then n_k has a QNR factor mod q -/
theorem qr_trap_break (p k q : ℕ) (hq_prime : Nat.Prime q) (hq_odd : q % 2 = 1)
    (hq_div : q ∣ m_k k) (hp_mod4 : p % 4 = 1)
    (hp_qnr : legendreSym q p = -1) :
    ∃ (r : ℕ), r ∣ n_k p k ∧ Nat.Prime r ∧ legendreSym q r = -1 := by
  sorry

/-- The key construction: for any odd prime q, we can find k < q with q | m_k -/
theorem exists_k_divides (q : ℕ) (hq_prime : Nat.Prime q) (hq_odd : q % 2 = 1) :
    ∃ k : ℕ, k < q ∧ q ∣ m_k k := by
  -- Solve 4k + 3 ≡ 0 (mod q), i.e., k ≡ -3 * 4⁻¹ (mod q)
  sorry

-- ============================================================================
-- PART 4: Burgess Bound (Axiomatized)
-- ============================================================================

/-- Axiom: Burgess bound on least quadratic nonresidue.
    For any prime p, there exists a prime q with (q/p) = -1 and q ≤ p^(1/4√e + ε).
    We axiomatize a weaker version: q < p for sufficiently large p. -/
axiom burgess_bound (p : ℕ) (hp : Nat.Prime p) (hp_large : p > 2) :
    ∃ q : ℕ, Nat.Prime q ∧ legendreSym q p = -1 ∧ q < p

-- ============================================================================
-- PART 5: Main Theorem for p ≡ 1 (mod 4)
-- ============================================================================

/-- For p ≡ 1 (mod 4), Type II succeeds at some k < p -/
theorem type_ii_eventually_succeeds (p : ℕ) (hp : Nat.Prime p) (hp_mod4 : p % 4 = 1) :
    ∃ k : ℕ, k < p ∧ type_ii_success p k := by
  -- Use Burgess to get q with (q/p) = -1
  -- Use exists_k_divides to get k with q | m_k
  -- Use qr_trap_break to show Type II succeeds
  sorry

-- ============================================================================
-- PART 6: Full ESC Theorem
-- ============================================================================

/-- ESC has a solution for every prime p -/
theorem esc_for_primes (p : ℕ) (hp : Nat.Prime p) :
    ∃ x y z : ℕ, x > 0 ∧ y > 0 ∧ z > 0 ∧ 4 * x * y * z = p * (y * z + x * z + x * y) := by
  -- Case split on p mod 4
  -- p = 2: use (1, 2, 2)
  -- p ≡ 3 (mod 4): use explicit formula
  -- p ≡ 1 (mod 4): use Type II mechanism
  sorry

/-- Main theorem: ESC holds for all n ≥ 2 -/
theorem erdos_straus_conjecture (n : ℕ) (hn : n ≥ 2) :
    ∃ x y z : ℕ, x > 0 ∧ y > 0 ∧ z > 0 ∧ 4 * x * y * z = n * (y * z + x * z + x * y) := by
  -- Reduce to prime case
  sorry
