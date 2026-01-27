/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 7d58358f-cf4f-4616-affe-ac6e6455e8af

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem two_primitive_root (k : ℕ) (hk : k ≥ 1) :
    orderOf (2 : ZMod (5^k)) = 4 * 5^(k-1)

- theorem m_order_five (k : ℕ) (hk : k ≥ 1) :
    orderOf (m k : ZMod (5^(k+1))) = 5

- theorem m_expansion (k : ℕ) (hk : k ≥ 1) :
    ∃ s : ℕ, s % 5 = 3 ∧ (m k : ZMod (5^(k+1))) = 1 + s * 5^k

- theorem s_eq_three (k : ℕ) (hk : k ≥ 1) :
    (m k : ZMod (5^(k+1))) = 1 + 3 * 5^k

- theorem children_orbit (k n : ℕ) (hn : k + 1 ≤ n) (j : Fin 5) :
    u k (n + j.val * T k) = u k n * (m k)^(j.val)
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

import Mathlib


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
  -- We'll use that $2$ is a primitive root modulo $5^k$ for $k \geq 1$.
  have h_prim_root : ∀ k ≥ 1, orderOf (2 : ZMod (5 ^ k)) = 4 * 5 ^ (k - 1) := by
    intro k hk_1
    have h_order : orderOf (2 : ZMod (5 ^ k)) = 4 * 5 ^ (k - 1) := by
      have h_order_eq : 2 ^ (4 * 5 ^ (k - 1)) ≡ 1 [MOD 5 ^ k] := by
        have h_euler : 2 ^ Nat.totient (5 ^ k) ≡ 1 [MOD 5 ^ k] := by
          exact Nat.ModEq.pow_totient <| by cases k <;> norm_num at *;
        rwa [ Nat.totient_prime_pow ( by decide ) hk_1, mul_comm ] at h_euler
      have h_order_min : ∀ m < 4 * 5 ^ (k - 1), m > 0 → ¬(2 ^ m ≡ 1 [MOD 5 ^ k]) := by
        -- We'll use that $2^m \equiv 1 \pmod{5^k}$ implies $m$ is a multiple of $4 \cdot 5^{k-1}$.
        intros m hm_lt hm_pos hm_mod
        have h_div : 4 * 5 ^ (k - 1) ∣ m := by
          -- We'll use that $2^m \equiv 1 \pmod{5^k}$ implies $m$ is a multiple of $4 \cdot 5^{k-1}$ by induction on $k$.
          have h_ind : ∀ k ≥ 1, ∀ m, 2 ^ m ≡ 1 [MOD 5 ^ k] → 4 * 5 ^ (k - 1) ∣ m := by
            intros k hk m hm_mod
            induction' k, Nat.succ_le.mpr hk using Nat.le_induction with k hk ih generalizing m;
            · rw [ ← Nat.mod_add_div m 4 ] at *; norm_num [ Nat.ModEq, Nat.pow_add, Nat.pow_mul, Nat.mul_mod, Nat.pow_mod ] at *; have := Nat.mod_lt m four_pos; interval_cases m % 4 <;> norm_num at *;
            · -- If $2^m \equiv 1 \pmod{5^{k+1}}$, then $2^m \equiv 1 \pmod{5^k}$, so by the induction hypothesis, $4 \cdot 5^{k-1} \mid m$.
              have h_ind_step : 4 * 5 ^ (k - 1) ∣ m := by
                exact ih ‹_› m <| hm_mod.of_dvd <| pow_dvd_pow _ <| Nat.le_succ _;
              -- Let $m = 4 \cdot 5^{k-1} \cdot t$ for some integer $t$.
              obtain ⟨t, rfl⟩ : ∃ t, m = 4 * 5 ^ (k - 1) * t := h_ind_step;
              -- We'll use that $2^{4 \cdot 5^{k-1}} \equiv 1 + 5^k \cdot c_k \pmod{5^{k+1}}$ for some integer $c_k$ not divisible by 5.
              have h_exp : ∃ c_k : ℕ, 2 ^ (4 * 5 ^ (k - 1)) = 1 + 5 ^ k * c_k ∧ ¬(5 ∣ c_k) := by
                have h_exp : ∀ k ≥ 1, ∃ c_k : ℕ, 2 ^ (4 * 5 ^ (k - 1)) = 1 + 5 ^ k * c_k ∧ ¬(5 ∣ c_k) := by
                  intro k hk
                  induction' hk with k hk ih;
                  · exists ( 2 ^ ( 4 * 5 ^ ( 1 - 1 ) ) - 1 ) / 5 ^ 1;
                  · rcases k with ( _ | k ) <;> simp_all +decide [ Nat.pow_succ', Nat.pow_mul ];
                    obtain ⟨ c_k, hc_k₁, hc_k₂ ⟩ := ih;
                    -- We'll use that $1048576^{5^k} = (16^{5^k})^5 = (1 + 5 \cdot 5^k \cdot c_k)^5$.
                    have h_expand : 1048576 ^ 5 ^ k = (1 + 5 * 5 ^ k * c_k) ^ 5 := by
                      rw [ ← hc_k₁, show 1048576 = 16 ^ 5 by norm_num, pow_right_comm ];
                    rw [ h_expand ];
                    refine' ⟨ c_k + 5 ^ k * c_k ^ 2 * 10 + 5 ^ ( 2 * k ) * c_k ^ 3 * 50 + 5 ^ ( 3 * k ) * c_k ^ 4 * 125 + 5 ^ ( 4 * k ) * c_k ^ 5 * 125, _, _ ⟩ <;> ring;
                    norm_num [ Nat.dvd_iff_mod_eq_zero, Nat.add_mod, Nat.mul_mod, Nat.pow_mod ] at * ; aesop;
                exact h_exp k ‹_›;
              -- Then $2^{4 \cdot 5^{k-1} \cdot t} \equiv (1 + 5^k \cdot c_k)^t \equiv 1 + t \cdot 5^k \cdot c_k \pmod{5^{k+1}}$.
              obtain ⟨c_k, hc_k⟩ := h_exp;
              have h_exp_t : 2 ^ (4 * 5 ^ (k - 1) * t) ≡ 1 + t * 5 ^ k * c_k [MOD 5 ^ (k + 1)] := by
                have h_exp_t : (1 + 5 ^ k * c_k) ^ t ≡ 1 + t * 5 ^ k * c_k [MOD 5 ^ (k + 1)] := by
                  have h_exp_t : ∀ t : ℕ, (1 + 5 ^ k * c_k) ^ t ≡ 1 + t * 5 ^ k * c_k [MOD 5 ^ (k + 1)] := by
                    intro t; induction t <;> simp_all +decide [ ← ZMod.natCast_eq_natCast_iff, pow_succ, mul_assoc ] ;
                    ring;
                    norm_cast;
                    erw [ ZMod.natCast_eq_natCast_iff ] ; norm_num [ Nat.modEq_iff_dvd ];
                    exact ⟨ ( ‹ℕ› : ℤ ) * c_k ^ 2 * 5 ^ ( k - 1 ), by cases k <;> simp_all +decide [ pow_succ, pow_mul ] ; linarith ⟩;
                  apply h_exp_t;
                simp_all +decide [ pow_mul ];
              -- Since $2^{4 \cdot 5^{k-1} \cdot t} \equiv 1 \pmod{5^{k+1}}$, we have $1 + t \cdot 5^k \cdot c_k \equiv 1 \pmod{5^{k+1}}$, which simplifies to $t \cdot 5^k \cdot c_k \equiv 0 \pmod{5^{k+1}}$.
              have h_cong : t * 5 ^ k * c_k ≡ 0 [MOD 5 ^ (k + 1)] := by
                simp_all +decide [ ← ZMod.natCast_eq_natCast_iff ];
              -- Since $5^{k+1} \mid t \cdot 5^k \cdot c_k$, we can divide both sides by $5^k$ to get $5 \mid t \cdot c_k$.
              have h_div : 5 ∣ t * c_k := by
                rw [ Nat.modEq_zero_iff_dvd ] at h_cong;
                exact Exists.elim h_cong fun x hx => ⟨ x, by ring_nf at hx ⊢; nlinarith [ pow_pos ( show 0 < 5 by decide ) k ] ⟩;
              rcases k with ( _ | k ) <;> simp_all +decide [ Nat.Prime.dvd_mul ];
              obtain ⟨ d, rfl ⟩ := h_div; exact ⟨ d, by ring ⟩ ;
          exact h_ind k hk_1 m hm_mod;
        linarith [ Nat.le_of_dvd hm_pos h_div ]
      rw [ orderOf_eq_of_pow_and_pow_div_prime ];
      · positivity;
      · simpa [ ← ZMod.natCast_eq_natCast_iff ] using h_order_eq;
      · intro p pp dp; specialize h_order_min ( 4 * 5 ^ ( k - 1 ) / p ) ( Nat.div_lt_self ( by positivity ) ( pp.one_lt ) ) ( Nat.div_pos ( Nat.le_of_dvd ( by positivity ) dp ) pp.pos ) ; simp_all +decide [ ← ZMod.natCast_eq_natCast_iff ] ;
    exact h_order;
  exact h_prim_root k hk

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
  -- Since $m_k = 2^{T_k}$, we know that $m_k^5 = 2^{5T_k} \equiv 1 \pmod{5^{k+1}}$ by definition of $T_k$.
  have h_mk_pow_5 : (Zeroless.m k) ^ 5 = 1 := by
    -- Since $2$ is a primitive root modulo $5^{k+1}$, we know that $2^{φ(5^{k+1})} ≡ 1 \pmod{5^{k+1}}$.
    have h_order : (2 : ZMod (5^(k+1))) ^ Nat.totient (5^(k+1)) = 1 := by
      have h_order : Nat.gcd 2 (5^(k+1)) = 1 := by
        exact?;
      simpa [ ← ZMod.natCast_eq_natCast_iff ] using Nat.ModEq.pow_totient h_order;
    convert h_order using 1 ; norm_num [ Nat.totient_prime_pow ] ; ring;
    unfold Zeroless.m; ring;
    unfold Zeroless.T; ring;
    cases k <;> simp_all +decide [ pow_succ' ] ; ring;
  refine' orderOf_eq_of_pow_and_pow_div_prime _ _ _ <;> norm_num [ h_mk_pow_5 ];
  intro p pp dp; have := Nat.le_of_dvd ( by decide ) dp; interval_cases p <;> norm_num at *;
  -- By definition of $m_k$, we know that $m_k = 2^{4 \cdot 5^{k-1}}$.
  have h_mk_def : (2 : ZMod (5^(k+1)))^(4 * 5^(k-1)) ≠ 1 := by
    have h_order : orderOf (2 : ZMod (5^(k+1))) = 4 * 5^k := by
      convert two_primitive_root ( k + 1 ) ( by linarith ) using 1
    intro h; have := orderOf_dvd_iff_pow_eq_one.mpr h; simp_all +decide [ Nat.mul_dvd_mul_iff_left ] ;
    exact Nat.not_dvd_of_pos_of_lt ( pow_pos ( by decide ) _ ) ( pow_lt_pow_right₀ ( by decide ) ( Nat.pred_lt ( ne_bot_of_gt hk ) ) ) this;
  aesop

/-- m_k ≡ 1 + s_k · 5^k (mod 5^{k+1}) where s_k ≡ 3 (mod 5) -/
theorem m_expansion (k : ℕ) (hk : k ≥ 1) :
    ∃ s : ℕ, s % 5 = 3 ∧ (m k : ZMod (5^(k+1))) = 1 + s * 5^k := by
  -- This follows from Hensel lifting: 2^4 ≡ 16 ≡ 1 + 3·5 (mod 25)
  -- We need to show that $2^{T_k} \equiv 1 + 3 \cdot 5^k \pmod{5^{k+1}}$.
  have h_cong : 2 ^ (T k) ≡ 1 + 3 * 5 ^ k [ZMOD 5 ^ (k + 1)] := by
    -- By definition of $T$, we know that $T k = 4 \cdot 5^{k-1}$.
    have hT_def : T k = 4 * 5 ^ (k - 1) := by
      rfl;
    -- We'll use induction to prove that $2^{4 \cdot 5^{k-1}} \equiv 1 + 3 \cdot 5^k \pmod{5^{k+1}}$.
    have h_ind : ∀ k ≥ 1, 2 ^ (4 * 5 ^ (k - 1)) ≡ 1 + 3 * 5 ^ k [ZMOD 5 ^ (k + 1)] := by
      intro k hk
      induction' hk with k ih;
      · decide;
      · -- We can rewrite $2^{4 \cdot 5^k}$ as $(2^{4 \cdot 5^{k-1}})^5$.
        have h_exp : 2 ^ (4 * 5 ^ k) = (2 ^ (4 * 5 ^ (k - 1))) ^ 5 := by
          cases k <;> simp_all +decide [ pow_succ, pow_mul ];
        -- Substitute the induction hypothesis into the expression.
        have h_subst : (2 ^ (4 * 5 ^ (k - 1))) ^ 5 ≡ (1 + 3 * 5 ^ k) ^ 5 [ZMOD 5 ^ (k + 2)] := by
          rw [ Int.modEq_iff_dvd ] at *;
          rename_i h; convert mul_dvd_mul h ( show 5 ∣ ( 1 + 3 * 5 ^ k ) ^ 4 + ( 1 + 3 * 5 ^ k ) ^ 3 * 2 ^ ( 4 * 5 ^ ( k - 1 ) ) + ( 1 + 3 * 5 ^ k ) ^ 2 * ( 2 ^ ( 4 * 5 ^ ( k - 1 ) ) ) ^ 2 + ( 1 + 3 * 5 ^ k ) * ( 2 ^ ( 4 * 5 ^ ( k - 1 ) ) ) ^ 3 + ( 2 ^ ( 4 * 5 ^ ( k - 1 ) ) ) ^ 4 from ?_ ) using 1 ; ring;
          norm_cast ; norm_num [ Nat.dvd_iff_mod_eq_zero, Nat.add_mod, Nat.mul_mod, Nat.pow_mod ];
          rcases k with ( _ | _ | k ) <;> norm_num [ Nat.pow_succ', Nat.pow_mul, Nat.mul_mod, Nat.pow_mod ] at *;
        convert h_subst.trans _ using 1;
        · exact_mod_cast h_exp;
        · rw [ Int.modEq_iff_dvd ] ; ring ; norm_num [ Int.ModEq, Int.add_emod, Int.mul_emod ] ;
          rcases k with ( _ | _ | k ) <;> norm_num [ pow_succ, pow_mul ] at * ; ring_nf at *;
          exact ⟨ -5 ^ k * 90 - 5 ^ ( k * 2 ) * 6750 - 5 ^ ( k * 3 ) * 253125 - 5 ^ ( k * 4 ) * 3796875, by ring ⟩;
    exact hT_def ▸ h_ind k hk;
  refine' ⟨ 3, _, _ ⟩ <;> norm_num;
  convert h_cong using 1;
  norm_cast;
  erw [ ← ZMod.natCast_eq_natCast_iff ] ; aesop

/-- Specifically: s_k = 3 for all k (the expansion coefficient is constant) -/
theorem s_eq_three (k : ℕ) (hk : k ≥ 1) :
    (m k : ZMod (5^(k+1))) = 1 + 3 * 5^k := by
  -- By Lemma `m_expansion`, there exists an integer `s` such that `s % 5 = 3` and `m k = 1 + s * 5^(k)`.
  obtain ⟨s, hs_mod, hs_eq⟩ : ∃ s : ℕ, s % 5 = 3 ∧ (m k : ZMod (5^(k+1))) = 1 + s * 5^k := by
    convert m_expansion k hk;
  -- Since $s \equiv 3 \pmod{5}$, we can write $s = 5m + 3$ for some integer $m$.
  obtain ⟨m, hm⟩ : ∃ m : ℕ, s = 5 * m + 3 := by
    exact ⟨ s / 5, by rw [ ← hs_mod, Nat.div_add_mod ] ⟩;
  simp_all +decide [ mul_pow, add_mul ];
  norm_cast;
  erw [ ZMod.natCast_eq_zero_iff ] ; exact ⟨ m, by ring ⟩

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
    -- By multiplying both sides of the induction hypothesis by $m_k$, we get the desired result.
    rw [ih]
    ring

/-! ## Decomposition of 5-adic States -/

/-- The lower k digits of u (mod 5^k) -/
def lower_part (k : ℕ) (u : ZMod (5^(k+1))) : ZMod (5^k) :=
  (u.val : ZMod (5^k))

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

omega could not prove the goal:
a possible counterexample may satisfy the constraints
  c ≥ 5
  b ≥ 0
  a ≥ 0
  5*a - b ≥ 1
where
 a := (↑5 : ℤ) ^ k
 b := (↑u.val : ℤ)
 c := (↑u.val : ℤ) / (↑(5 ^ k) : ℤ)-/
/-- The top digit of u: the coefficient of 5^k in the 5-adic expansion -/
def top_digit (k : ℕ) (u : ZMod (5^(k+1))) : Fin 5 :=
  ⟨u.val / 5^k, by
    have h : u.val < 5^(k+1) := u.val_lt
    have h2 : 5^(k+1) = 5 * 5^k := by ring
    omega⟩

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

Function expected at
  top_digit
but this term has type
  ?m.1

Note: Expected a function because this term is being applied to the argument
  k-/
/-- The decomposition is valid: u = lower_part + 5^k · top_digit -/
theorem decomposition (k : ℕ) (u : ZMod (5^(k+1))) :
    u.val = (lower_part k u).val + 5^k * (top_digit k u).val := by
  simp only [lower_part, top_digit]
  have h1 : (u.val : ZMod (5^k)).val = u.val % 5^k := ZMod.val_natCast u.val
  rw [h1]
  exact Nat.div_add_mod' u.val (5^k)

/-! ## Connection to Zeroless Property -/

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

Unknown identifier `top_digit`-/
/-- A state u survives at level k if its top digit is nonzero.
    This is the "zeroless" condition at position k. -/
def survives (k : ℕ) (u : ZMod (5^(k+1))) : Prop :=
  (top_digit k u).val ≠ 0

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

Function expected at
  survives
but this term has type
  ?m.1

Note: Expected a function because this term is being applied to the argument
  k
Function expected at
  survives
but this term has type
  ?m.1

Note: Expected a function because this term is being applied to the argument
  k-/
/-- A survivor has exactly 4 or 5 children that also survive.
    This is the "4-or-5 Children Theorem". -/
theorem four_or_five_children (k : ℕ) (hk : k ≥ 1) (u : ZMod (5^(k+1)))
    (hu : survives k u) :
    (Finset.filter (fun j : Fin 5 => survives k (u * (m k)^j.val)) Finset.univ).card ∈ ({4, 5} : Set ℕ) := by
  -- The top digit cycles through 5 values as j varies from 0 to 4.
  -- Exactly one of these is 0 (killed) unless we're in a special case.
  sorry

end Zeroless