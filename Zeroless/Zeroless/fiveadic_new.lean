/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: b1db0548-0898-4d41-8cc6-1fc94e8b0b45

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
  rw [ orderOf_eq_of_pow_and_pow_div_prime ] <;> norm_num;
  · -- We'll use that $2^{4 \cdot 5^{k-1}} \equiv 1 \pmod{5^k}$.
    have h_cong : 2 ^ (4 * 5 ^ (k - 1)) ≡ 1 [MOD 5 ^ k] := by
      -- By Euler's theorem, since $2$ and $5^k$ are coprime, we have $2^{\phi(5^k)} \equiv 1 \pmod{5^k}$.
      have h_euler : 2 ^ Nat.totient (5 ^ k) ≡ 1 [MOD 5 ^ k] := by
        exact Nat.ModEq.pow_totient <| by cases k <;> norm_num at *;
      cases k <;> simp_all +decide [ Nat.totient_prime_pow ];
      rwa [ Nat.mul_comm ];
    simpa [ ← ZMod.natCast_eq_natCast_iff ] using h_cong;
  · intro p pp dp; have := Nat.Prime.dvd_mul pp |>.1 dp; rcases this with ( h | h ) <;> simp_all +decide [ Nat.Prime.dvd_iff_not_coprime ] ;
    · have := Nat.le_of_dvd ( by norm_num ) ( Nat.Prime.dvd_iff_not_coprime pp |>.2 h ) ; interval_cases p <;> norm_num at *;
      -- By contradiction, assume $2^{4 \cdot 5^{k-1} / 2} \equiv 1 \pmod{5^k}$.
      by_contra h_contra;
      -- Then $2^{2 \cdot 5^{k-1}} \equiv 1 \pmod{5^k}$.
      have h_exp : 2 ^ (2 * 5 ^ (k - 1)) ≡ 1 [MOD 5 ^ k] := by
        simp_all +decide [ ← ZMod.natCast_eq_natCast_iff ];
        convert h_contra using 1 ; rw [ show 4 * 5 ^ ( k - 1 ) / 2 = 2 * 5 ^ ( k - 1 ) by rw [ Nat.div_eq_of_eq_mul_left zero_lt_two ] ; ring ];
      -- Then $2^{2 \cdot 5^{k-1}} \equiv 1 \pmod{5}$.
      have h_mod_5 : 2 ^ (2 * 5 ^ (k - 1)) ≡ 1 [MOD 5] := by
        exact h_exp.of_dvd <| dvd_pow_self _ <| by linarith;
      rw [ ← Nat.mod_add_div ( 5 ^ ( k - 1 ) ) 4 ] at h_mod_5; norm_num [ Nat.ModEq, Nat.pow_add, Nat.pow_mul, Nat.mul_mod, Nat.pow_mod ] at h_mod_5;
    · -- If $p$ divides $5^{k-1}$, then $p = 5$.
      have hp : p = 5 := by
        exact ( Nat.prime_dvd_prime_iff_eq pp ( by norm_num : Nat.Prime 5 ) ) |>.1 ( pp.dvd_of_dvd_pow ( Nat.Prime.dvd_iff_not_coprime pp |>.2 h ) ) ▸ rfl;
      -- By contradiction, assume $2^{4 \cdot 5^{k-2}} \equiv 1 \pmod{5^k}$.
      by_contra h_contra;
      -- Then $2^{4 \cdot 5^{k-2}} \equiv 1 \pmod{5^k}$ implies $2^{4 \cdot 5^{k-2}} - 1 \equiv 0 \pmod{5^k}$.
      have h_div : 5 ^ k ∣ (2 ^ (4 * 5 ^ (k - 2)) - 1) := by
        simp_all +decide [ ← ZMod.natCast_eq_zero_iff ];
        rcases k with ( _ | _ | k ) <;> simp_all +decide [ pow_succ', Nat.mul_div_assoc ];
      -- Using the Lifting The Exponent Lemma, we have $v_5(2^{4 \cdot 5^{k-2}} - 1) = v_5(2^4 - 1) + v_5(5^{k-2}) = 1 + (k-2) = k-1$.
      have h_lifting : Nat.factorization (2 ^ (4 * 5 ^ (k - 2)) - 1) 5 = k - 1 := by
        have h_lifting : ∀ {x : ℕ}, x > 0 → Nat.factorization (2 ^ (4 * 5 ^ x) - 1) 5 = x + 1 := by
          intros x hx_pos
          induction' hx_pos with x hx ih;
          · native_decide +revert;
          · -- Using the identity $2^{4 \cdot 5^{x+1}} - 1 = (2^{4 \cdot 5^x} - 1)(2^{16 \cdot 5^x} + 2^{12 \cdot 5^x} + 2^{8 \cdot 5^x} + 2^{4 \cdot 5^x} + 1)$, we can apply the inductive hypothesis.
            have h_factor : 2 ^ (4 * 5 ^ (x + 1)) - 1 = (2 ^ (4 * 5 ^ x) - 1) * (2 ^ (16 * 5 ^ x) + 2 ^ (12 * 5 ^ x) + 2 ^ (8 * 5 ^ x) + 2 ^ (4 * 5 ^ x) + 1) := by
              zify ; norm_num ; ring;
            rw [ h_factor, Nat.factorization_mul ] <;> simp_all +decide;
            · -- We need to show that $2^{16 \cdot 5^x} + 2^{12 \cdot 5^x} + 2^{8 \cdot 5^x} + 2^{4 \cdot 5^x} + 1$ is divisible by $5$ but not by $25$.
              have h_div : 5 ∣ (2 ^ (16 * 5 ^ x) + 2 ^ (12 * 5 ^ x) + 2 ^ (8 * 5 ^ x) + 2 ^ (4 * 5 ^ x) + 1) ∧ ¬(25 ∣ (2 ^ (16 * 5 ^ x) + 2 ^ (12 * 5 ^ x) + 2 ^ (8 * 5 ^ x) + 2 ^ (4 * 5 ^ x) + 1)) := by
                norm_num [ Nat.dvd_iff_mod_eq_zero, Nat.add_mod, Nat.pow_mod ];
                rw [ ← Nat.mod_add_div ( 5 ^ x ) 4 ] ; norm_num [ Nat.pow_add, Nat.pow_mul, Nat.mul_mod, Nat.pow_mod ] ;
                rw [ ← Nat.mod_add_div ( 5 ^ x / 4 ) 20 ] ; norm_num [ Nat.pow_add, Nat.pow_mul, Nat.mul_mod, Nat.pow_mod ] ; have := Nat.mod_lt ( 5 ^ x / 4 ) ( by decide : 0 < 20 ) ; interval_cases ( 5 ^ x / 4 ) % 20 <;> trivial;
              rw [ ← Nat.factorization_le_iff_dvd ] at h_div <;> norm_num at *;
              exact le_antisymm ( Nat.le_of_not_lt fun h => h_div.2 <| Nat.dvd_trans ( pow_dvd_pow _ h ) <| Nat.ordProj_dvd _ _ ) h_div.1;
            · exact ne_of_gt ( Nat.sub_pos_of_lt ( one_lt_pow₀ ( by decide ) ( by positivity ) ) );
        rcases k with ( _ | _ | k ) <;> simp_all +decide;
        by_cases hk : 0 < k <;> aesop;
      have := Nat.factorization_le_iff_dvd ( by positivity ) ( Nat.sub_ne_zero_of_lt ( one_lt_pow₀ ( by decide ) ( by aesop ) ) ) |>.2 h_div ; simp_all +decide;
      exact Nat.not_le_of_gt ( Nat.pred_lt ( ne_bot_of_gt hk ) ) this

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
  -- Since $2^{T_k}$ has order $5$ modulo $5^{k+1}$, it follows that $m_k = 2^{T_k}$ also has order $5$ modulo $5^{k+1}$.
  have hm_order : (2 ^ (T k) : ZMod (5 ^ (k + 1))) ^ 5 = 1 := by
    -- By definition of $T_k$, we know that $2^{T_k}$ is congruent to $1 \mod 5^{k+1}$.
    have h_cong : (2 ^ (T k)) ^ 5 ≡ 1 [MOD 5 ^ (k + 1)] := by
      -- By Euler's theorem, since $2$ and $5^{k+1}$ are coprime, we have $2^{\phi(5^{k+1})} \equiv 1 \pmod{5^{k+1}}$.
      have h_euler : 2 ^ Nat.totient (5 ^ (k + 1)) ≡ 1 [MOD 5 ^ (k + 1)] := by
        exact Nat.ModEq.pow_totient <| by norm_num;
      convert h_euler using 1 ; norm_num [ Nat.totient_prime_pow ] ; ring;
      exact congr_arg _ ( by rw [ show Zeroless.T k = 4 * 5 ^ ( k - 1 ) by rfl ] ; cases k <;> simp_all +decide [ pow_succ' ] ; linarith );
    simpa [ ← ZMod.natCast_eq_natCast_iff ] using h_cong;
  have hm_order_ge_5 : ¬((2 ^ (T k) : ZMod (5 ^ (k + 1))) ^ 1 = 1) := by
    -- By definition of $T$, we know that $2^{T_k}$ has order $5$ modulo $5^{k+1}$.
    have h_order : orderOf (2 : ZMod (5 ^ (k + 1))) = 4 * 5 ^ k := by
      convert two_primitive_root ( k + 1 ) ( by linarith ) using 1;
    intro h; have := orderOf_dvd_iff_pow_eq_one.mpr ( show ( 2 : ZMod ( 5 ^ ( k + 1 ) ) ) ^ ( 4 * 5 ^ ( k - 1 ) ) = 1 from by simpa [ ← ZMod.natCast_eq_natCast_iff ] using h ) ; simp_all +decide [ Nat.pow_succ' ] ;
    exact Nat.not_dvd_of_pos_of_lt ( by positivity ) ( by gcongr <;> omega ) this;
  have hm_order_div : orderOf (2 ^ (T k) : ZMod (5 ^ (k + 1))) ∣ 5 := by
    exact orderOf_dvd_iff_pow_eq_one.mpr hm_order;
  simp_all +decide [ Nat.dvd_prime ];
  convert hm_order_div using 1

/-- m_k ≡ 1 + s_k · 5^k (mod 5^{k+1}) where s_k ≡ 3 (mod 5) -/
theorem m_expansion (k : ℕ) (hk : k ≥ 1) :
    ∃ s : ℕ, s % 5 = 3 ∧ (m k : ZMod (5^(k+1))) = 1 + s * 5^k := by
  -- This follows from Hensel lifting: 2^4 ≡ 16 ≡ 1 + 3·5 (mod 25)
  -- By definition of $m_k$, we know that $m_k = 1 + 5^k \cdot s$ where $s$ is an integer such that $s \equiv 3 \pmod{5}$.
  have hm_def : ∃ s : ℤ, s % 5 = 3 ∧ (m k : ZMod (5 ^ (k + 1))) = 1 + s * 5 ^ k := by
    -- By definition of $m_k$, we know that $m_k = 1 + 5^k \cdot s$ where $s$ is an integer such that $s \equiv 3 \pmod{5}$. Use this fact.
    obtain ⟨s, hs⟩ : ∃ s : ℤ, (2 : ℤ) ^ (4 * 5 ^ (k - 1)) = 1 + s * 5 ^ k ∧ s % 5 = 3 := by
      -- We'll use induction to prove that the formula holds.
      have h_ind : ∀ k ≥ 1, ∃ s : ℤ, 2 ^ (4 * 5 ^ (k - 1)) = 1 + s * 5 ^ k ∧ s % 5 = 3 := by
        intro k hk
        induction' hk with k hk ih;
        · exists ( 2 ^ ( 4 * 5 ^ ( 1 - 1 ) ) - 1 ) / 5 ^ 1;
        · rcases ih with ⟨ s, hs₁, hs₂ ⟩ ; rcases k with ( _ | k ) <;> simp_all +decide [ pow_succ, pow_mul ];
          refine' ⟨ s + s ^ 2 * 5 ^ k * 10 + s ^ 3 * 5 ^ ( k * 2 ) * 50 + s ^ 4 * 5 ^ ( k * 3 ) * 125 + s ^ 5 * 5 ^ ( k * 4 ) * 125, _, _ ⟩ <;> ring;
          norm_num [ pow_mul', Int.add_emod, Int.mul_emod, hs₂ ];
      exact h_ind k hk;
    refine' ⟨ s, hs.2, _ ⟩;
    convert congr_arg ( ( ↑ ) : ℤ → ZMod ( 5 ^ ( k + 1 ) ) ) hs.1 using 1 ; norm_cast ; aesop;
    norm_num [ ZMod.intCast_zmod_eq_zero_iff_dvd ];
  cases' hm_def with s hs;
  refine' ⟨ Int.toNat ( s % ( 5 ^ ( k + 1 ) ) ), _, _ ⟩;
  · rw [ ← Int.ofNat_inj ] ; norm_num [ Int.toNat_of_nonneg ( Int.emod_nonneg _ ( by positivity : ( 5 : ℤ ) ^ ( k + 1 ) ≠ 0 ) ), Int.emod_emod_of_dvd _ ( dvd_pow_self _ ( Nat.succ_ne_zero _ ) ), hs ];
  · simp_all +decide [ ← ZMod.intCast_eq_intCast_iff ];
    erw [ ← Int.emod_add_mul_ediv s ( 5 ^ ( k + 1 ) ) ] ; norm_num [ Int.emod_nonneg, Int.emod_lt_of_pos ];
    norm_cast ; ring;
    erw [ ZMod.intCast_eq_intCast_iff ] ; norm_num [ Int.emod_eq_zero_of_dvd, dvd_mul_of_dvd_right ];
    norm_num [ Int.ModEq, Int.add_emod, Int.mul_emod ];
    norm_num [ pow_succ, mul_assoc, Int.mul_emod ];
    norm_num [ ← Int.mul_emod ]

/-- Specifically: s_k = 3 for all k (the expansion coefficient is constant) -/
theorem s_eq_three (k : ℕ) (hk : k ≥ 1) :
    (m k : ZMod (5^(k+1))) = 1 + 3 * 5^k := by
  -- Let's prove that m_k can be written in the form 1 + s_k * 5^k where s_k ≡ 3 (mod 5).
  have h_mk_form : ∃ s : ℕ, s % 5 = 3 ∧ (m k : ZMod (5^(k+1))) = 1 + s * 5^k := by
    exact?;
  obtain ⟨ s, hs₁, hs₂ ⟩ := h_mk_form; (
  -- Since $s$ is a multiple of $5$ plus $3$, we have $s = 5t + 3$ for some integer $t$.
  obtain ⟨ t, ht ⟩ : ∃ t : ℕ, s = 5 * t + 3 := by
    exact ⟨ s / 5, by rw [ ← hs₁, Nat.div_add_mod ] ⟩;
  replace hs₂ := congr_arg ( fun x : ZMod ( 5 ^ ( k + 1 ) ) => ( x : ZMod ( 5 ^ ( k + 1 ) ) ) ) hs₂ ; norm_num [ ht, pow_succ, mul_assoc ] at hs₂ ⊢;
  convert hs₂ using 1 ; ring;
  norm_cast ; norm_num [ pow_succ, mul_assoc ]);

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
    grind

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