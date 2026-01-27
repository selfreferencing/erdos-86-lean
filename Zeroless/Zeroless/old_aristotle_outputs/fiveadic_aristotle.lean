/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: c23ac6e1-6ef5-4953-8003-5293dc9e48fb

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The version of Mathlib expected in this file appears to be incompatible with Aristotle's.
Please either switch your project to use the same version, or try again with `import Mathlib` only.
Details:
object file '/code/harmonic-lean/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib/Data/Nat/Digits.olean' of module Mathlib.Data.Nat.Digits does not exist
-/

/-
  Zeroless/FiveAdic.lean
  5-adic Infrastructure for the 86 Conjecture

  Key definitions:
  - T k: Period for k trailing zeroless digits = 4 * 5^(k-1)
  - u k n: 5-adic state = 2^(n-k-1) mod 5^(k+1)
  - m k: Multiplier = 2^(T k) mod 5^(k+1)

  Key theorems:
  - 2 is a primitive root mod 5^k
  - Multiplier m_k has order 5
  - Shifting n by T_k multiplies state by m_k
-/

import Mathlib.Data.Nat.Digits
import Mathlib.Data.ZMod.Basic
import Mathlib.NumberTheory.Padics.PadicVal
import Mathlib.Tactic

namespace Zeroless

open scoped BigOperators

/-! ## Basic Definitions -/

/-- Period for k trailing zeroless digits: T_k = 4 · 5^(k-1) -/
def T (k : ℕ) : ℕ := 4 * 5^(k-1)

/-- The 5-adic state: u_{k+1}(n) = 2^{n-k-1} mod 5^{k+1} -/
noncomputable def u (k : ℕ) (n : ℕ) : ZMod (5^(k+1)) :=
  (2 : ZMod (5^(k+1)))^(n-k-1)

/-- The multiplier: m_k = 2^{T_k} mod 5^{k+1} -/
noncomputable def m (k : ℕ) : ZMod (5^(k+1)) :=
  (2 : ZMod (5^(k+1)))^(T k)

/-! ## Verification Tests -/

-- T_k computations
example : T 1 = 4 := by native_decide
example : T 2 = 20 := by native_decide
example : T 3 = 100 := by native_decide

/-! ## Primitive Root Property -/

/-- 2 is a primitive root mod 5^k for all k ≥ 1.
    This means ord_{5^k}(2) = φ(5^k) = 4 · 5^{k-1} = T_k -/
theorem two_primitive_root (k : ℕ) (hk : k ≥ 1) :
    orderOf (2 : ZMod (5^k)) = 4 * 5^(k-1) := by
  -- Standard number theory fact: 2 is a primitive root mod 5,
  -- and primitive roots mod p lift to primitive roots mod p^k
  sorry

/-- Equivalently: ord_{5^k}(2) = T_k -/
theorem ord_two_eq_T (k : ℕ) (hk : k ≥ 1) :
    orderOf (2 : ZMod (5^k)) = T k := by
  simp only [T]
  exact two_primitive_root k hk

/-! ## Multiplier Structure -/

/-- m_k has order exactly 5 in (Z/5^{k+1}Z)× -/
theorem m_order_five (k : ℕ) (hk : k ≥ 1) :
    orderOf (m k : ZMod (5^(k+1))) = 5 := by
  -- m_k = 2^{T_k} where T_k = 4·5^{k-1}
  -- Order of 2 mod 5^{k+1} is T_{k+1} = 4·5^k
  -- So order of m_k = T_{k+1} / gcd(T_k, T_{k+1}) = 4·5^k / 4·5^{k-1} = 5
  sorry

/-- m_k ≡ 1 + s_k · 5^k (mod 5^{k+1}) where s_k ≡ 3 (mod 5) -/
theorem m_expansion (k : ℕ) (hk : k ≥ 1) :
    ∃ s : ℕ, s % 5 = 3 ∧ (m k : ZMod (5^(k+1))) = 1 + s * 5^k := by
  -- This follows from Hensel lifting: 2^4 ≡ 16 ≡ 1 + 3·5 (mod 25)
  sorry

/-- Specifically: s_k = 3 for all k (the expansion coefficient is constant) -/
theorem s_eq_three (k : ℕ) (hk : k ≥ 1) :
    (m k : ZMod (5^(k+1))) = 1 + 3 * 5^k := by
  sorry

/-! ## Child Relation (The Key Dynamics) -/

/-- Shifting n by T_k multiplies the 5-adic state by m_k.
    This is the fundamental recurrence for the survivor dynamics. -/
theorem u_shift (k n : ℕ) (hn : k + 1 ≤ n) :
    u k (n + T k) = u k n * m k := by
  simp only [u, m, T]
  -- 2^{(n + T_k) - k - 1} = 2^{n - k - 1} · 2^{T_k}
  have h1 : n + T k - (k + 1) = (n - (k + 1)) + T k := by omega
  rw [h1, pow_add]

/-- The 5 children of a survivor correspond to multiplying by m^j for j = 0,1,2,3,4.
    These are the "siblings" in the 5-adic tree structure. -/
theorem children_orbit (k n : ℕ) (hn : k + 1 ≤ n) (j : Fin 5) :
    u k (n + j.val * T k) = u k n * (m k)^(j.val) := by
  induction j.val with
  | zero => simp [m]
  | succ j' ih =>
    have h1 : n + (j' + 1) * T k = (n + j' * T k) + T k := by ring
    rw [h1]
    have hn' : k + 1 ≤ n + j' * T k := by omega
    rw [u_shift k (n + j' * T k) hn']
    -- Need to handle the induction properly
    sorry

/-! ## Decomposition of 5-adic States -/

/-- The lower k digits of u (mod 5^k) -/
def lower_part (k : ℕ) (u : ZMod (5^(k+1))) : ZMod (5^k) :=
  (u.val : ZMod (5^k))

/-- The top digit of u: the coefficient of 5^k in the 5-adic expansion -/
def top_digit (k : ℕ) (u : ZMod (5^(k+1))) : Fin 5 :=
  ⟨u.val / 5^k, by
    have h : u.val < 5^(k+1) := u.val_lt
    have h2 : 5^(k+1) = 5 * 5^k := by ring
    omega⟩

/-- The decomposition is valid: u = lower_part + 5^k · top_digit -/
theorem decomposition (k : ℕ) (u : ZMod (5^(k+1))) :
    u.val = (lower_part k u).val + 5^k * (top_digit k u).val := by
  simp only [lower_part, top_digit]
  have h1 : (u.val : ZMod (5^k)).val = u.val % 5^k := ZMod.val_natCast u.val
  rw [h1]
  exact Nat.div_add_mod' u.val (5^k)

/-! ## Connection to Zeroless Property -/

/-- A state u survives at level k if its top digit is nonzero.
    This is the "zeroless" condition at position k. -/
def survives (k : ℕ) (u : ZMod (5^(k+1))) : Prop :=
  (top_digit k u).val ≠ 0

/-- A survivor has exactly 4 or 5 children that also survive.
    This is the "4-or-5 Children Theorem". -/
theorem four_or_five_children (k : ℕ) (hk : k ≥ 1) (u : ZMod (5^(k+1)))
    (hu : survives k u) :
    (Finset.filter (fun j : Fin 5 => survives k (u * (m k)^j.val)) Finset.univ).card ∈ ({4, 5} : Set ℕ) := by
  -- The top digit cycles through 5 values as j varies from 0 to 4.
  -- Exactly one of these is 0 (killed) unless we're in a special case.
  sorry

end Zeroless
