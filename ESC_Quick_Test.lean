/-
  Quick test of ESC core lemmas - minimal imports
-/

-- Test 1: Basic divisibility (pure omega)
theorem test_p_plus_1_div_4 (p : Nat) (hp : p % 4 = 3) : 4 ∣ (p + 1) := by
  have h2 : p + 1 = 4 * (p / 4 + 1) := by omega
  exact ⟨p / 4 + 1, h2⟩

-- Test 2: Explicit ESC solution for p = 2
theorem test_esc_p2 : ∃ x y z : Nat, x > 0 ∧ y > 0 ∧ z > 0 ∧
    4 * x * y * z = 2 * (y * z + x * z + x * y) :=
  ⟨1, 2, 2, by native_decide⟩

-- Test 3: Explicit ESC solution for p = 3
theorem test_esc_p3 : ∃ x y z : Nat, x > 0 ∧ y > 0 ∧ z > 0 ∧
    4 * x * y * z = 3 * (y * z + x * z + x * y) :=
  ⟨1, 4, 12, by native_decide⟩

-- Test 4: Explicit ESC solution for p = 5
theorem test_esc_p5 : ∃ x y z : Nat, x > 0 ∧ y > 0 ∧ z > 0 ∧
    4 * x * y * z = 5 * (y * z + x * z + x * y) :=
  ⟨2, 4, 20, by native_decide⟩

-- Test 5: Explicit ESC solution for p = 7
theorem test_esc_p7 : ∃ x y z : Nat, x > 0 ∧ y > 0 ∧ z > 0 ∧
    4 * x * y * z = 7 * (y * z + x * z + x * y) :=
  ⟨2, 15, 210, by native_decide⟩

-- Test 6: m_k definition and properties
def m_k (k : Nat) : Nat := 4 * k + 3

theorem test_m_k_odd (k : Nat) : m_k k % 2 = 1 := by
  unfold m_k
  omega

theorem test_m_k_ge_3 (k : Nat) : m_k k ≥ 3 := by
  unfold m_k
  omega

-- Test 7: Cubic factorization (if ring works)
-- theorem test_cubic (p : Nat) : p^3 + 2*p^2 + 5*p + 4 = (p + 1) * (p^2 + p + 4) := by ring

#print axioms test_p_plus_1_div_4
#print axioms test_esc_p2
#print axioms test_m_k_odd
