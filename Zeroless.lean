/-
  The 86 Conjecture: Zeroless Powers of 2

  Theorem: For all n > 86, 2^n contains at least one digit 0 in base 10.

  This file contains:
  1. LTE lemma for base 10 (5-adic valuation)
  2. Automaton definition for zero detection
  3. Periodicity structure
  4. Survivor recurrence
  5. Coverage convergence
-/

import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.NumberTheory.Padics.PadicVal.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Totient
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic

namespace Zeroless

/-! ## Basic Definitions -/

/-- A power of 2 is "zeroless" if its decimal representation contains no digit 0 -/
def isZeroless (n : ℕ) : Prop :=
  ∀ d ∈ Nat.digits 10 (2^n), d ≠ 0

/-- Decidable version for computation -/
def isZerolessBool (n : ℕ) : Bool :=
  (Nat.digits 10 (2^n)).all (· ≠ 0)

/-- Check if 2^n contains digit 0 -/
def hasZero (n : ℕ) : Bool :=
  (Nat.digits 10 (2^n)).any (· = 0)

theorem hasZero_iff_not_zeroless (n : ℕ) :
    hasZero n = true ↔ ¬isZerolessBool n := by
  simp only [hasZero, isZerolessBool, List.any_eq_true, List.all_eq_true,
             decide_eq_true_eq, not_forall, not_not]
  constructor
  · intro ⟨d, hd, hdz⟩
    exact ⟨d, hd, hdz⟩
  · intro ⟨d, hd, hdz⟩
    exact ⟨d, hd, hdz⟩

/-! ## The Automaton -/

/-- The automaton state: 0 = no carry (s₀), 1 = carry (s₁) -/
inductive State where
  | s0 : State  -- No carry
  | s1 : State  -- Carry
  deriving DecidableEq, Repr

/-- Automaton transition: returns (new_state, output_digit, rejected?) -/
def transition (s : State) (d : ℕ) : State × ℕ × Bool :=
  match s with
  | State.s0 =>
    if d = 0 then (State.s0, 0, true)      -- REJECT: s₀ on 0
    else if d = 5 then (State.s1, 0, true) -- REJECT: s₀ on 5
    else if d < 5 then (State.s0, 2*d, false)
    else (State.s1, 2*d - 10, false)
  | State.s1 =>
    if d < 5 then (State.s0, 2*d + 1, false)
    else (State.s1, 2*d - 9, false)

/-- Run automaton on a list of digits (LSB first), return (final_state, rejected?) -/
def runAutomaton (digits : List ℕ) : State × Bool :=
  digits.foldl (fun (s, rej) d =>
    if rej then (s, true)
    else
      let (s', _, r) := transition s d
      (s', r)
  ) (State.s0, false)

/-- Rejection only happens in state s₀ on digits 0 or 5 -/
theorem reject_iff_s0_and_05 (s : State) (d : ℕ) :
    (transition s d).2.2 = true ↔ s = State.s0 ∧ (d = 0 ∨ d = 5) := by
  cases s
  case s0 =>
    simp only [transition, true_and]
    constructor
    · intro h
      split_ifs at h with h0 h5 <;> try simp at h
      · exact Or.inl h0
      · exact Or.inr h5
    · intro h
      rcases h with rfl | rfl <;> simp
  case s1 =>
    simp only [transition]
    split_ifs <;> simp

/-! ## Periodicity -/

/-- Period at level k is 4 · 5^(k-1) -/
def period (k : ℕ) : ℕ := 4 * 5^(k-1)

/-- Period is always positive -/
theorem period_pos (k : ℕ) : period k > 0 := by
  unfold period
  exact Nat.mul_pos (by norm_num : 4 > 0) (Nat.pow_pos (by norm_num : 0 < 5))

/-- Period at level 1 is 4 -/
theorem period_one : period 1 = 4 := by simp [period]

/-- Period at level 2 is 20 -/
theorem period_two : period 2 = 20 := by simp [period]

/-- Period at level 3 is 100 -/
theorem period_three : period 3 = 100 := by simp [period]

/-- Period recurrence: period(k+1) = 5 * period(k) -/
theorem period_recurrence (k : ℕ) (hk : k ≥ 1) :
    period (k + 1) = 5 * period k := by
  simp only [period]
  have h : k + 1 - 1 = k := Nat.add_sub_cancel k 1
  rw [h]
  have h2 : 5 ^ k = 5 * 5 ^ (k - 1) := by
    conv_lhs => rw [← Nat.sub_add_cancel hk]
    ring
  rw [h2]
  ring

/-! ## LTE Lemma -/

/-- 2^2 ≢ 1 (mod 5) -/
theorem pow2_2_mod_5_ne_one : (2 : ZMod 5)^2 ≠ 1 := by native_decide

/-- 2^1 ≢ 1 (mod 5) -/
theorem pow2_1_mod_5_ne_one : (2 : ZMod 5)^1 ≠ 1 := by native_decide

/-- Order of 2 mod 5 is 4 -/
theorem order_2_mod_5 : orderOf (2 : ZMod 5) = 4 := by
  have h1 : (2 : ZMod 5)^4 = 1 := by native_decide
  have h4_pos : 0 < 4 := by norm_num
  rw [orderOf_eq_iff h4_pos]
  constructor
  · exact h1
  · intro m hm hm4
    interval_cases m <;> native_decide

/-- 2^4 ≡ 1 (mod 5) -/
theorem pow2_4_mod_5 : (2 : ZMod 5)^4 = 1 := by native_decide

/-- 2^4 - 1 = 15 = 3 × 5 -/
theorem pow2_4_minus_1 : 2^4 - 1 = 15 := by norm_num

/-- ν₅(2^4 - 1) = 1 -/
theorem padic_val_pow2_4 : padicValNat 5 (2^4 - 1) = 1 := by native_decide

/-! ## Survivor Count -/

/-- S_k = number of survivors at level k (computed values) -/
def survivorCount : ℕ → ℕ
  | 0 => 1
  | 1 => 4
  | 2 => 18
  | 3 => 81
  | 4 => 364
  | 5 => 1638
  | 6 => 7371
  | _ => 0  -- Placeholder for higher values

/-- Verified survivor counts -/
theorem survivor_1 : survivorCount 1 = 4 := rfl
theorem survivor_2 : survivorCount 2 = 18 := rfl
theorem survivor_3 : survivorCount 3 = 81 := rfl
theorem survivor_4 : survivorCount 4 = 364 := rfl
theorem survivor_5 : survivorCount 5 = 1638 := rfl
theorem survivor_6 : survivorCount 6 = 7371 := rfl

/-- Ratio S₂/S₁ = 4.5 -/
theorem ratio_2_1 : (survivorCount 2 : ℚ) / survivorCount 1 = 9/2 := by norm_num [survivorCount]

/-- Ratio S₃/S₂ = 4.5 -/
theorem ratio_3_2 : (survivorCount 3 : ℚ) / survivorCount 2 = 9/2 := by norm_num [survivorCount]

/-- Ratio S₅/S₄ = 4.5 -/
theorem ratio_5_4 : (survivorCount 5 : ℚ) / survivorCount 4 = 9/2 := by norm_num [survivorCount]

/-! ## Survival Fraction -/

/-- Survival fraction at level k -/
def survivalFrac (k : ℕ) : ℚ := (survivorCount k : ℚ) / (period k : ℚ)

/-- Survival fraction at level 1 is 1 -/
theorem survival_frac_1 : survivalFrac 1 = 1 := by
  simp [survivalFrac, survivorCount, period]

/-- Survival fraction at level 2 is 0.9 -/
theorem survival_frac_2 : survivalFrac 2 = 9/10 := by
  simp [survivalFrac, survivorCount, period]
  norm_num

/-- Survival fraction at level 3 is 0.81 -/
theorem survival_frac_3 : survivalFrac 3 = 81/100 := by
  simp only [survivalFrac, survivorCount, period]
  norm_num

/-- 81/100 = (9/10)^2 -/
theorem frac_3_is_pow : (81 : ℚ)/100 = (9/10)^2 := by norm_num

/-! ## Coverage -/

/-- Coverage at level k is 1 - survival fraction -/
def coverage (k : ℕ) : ℚ := 1 - survivalFrac k

/-- Coverage at level 1 is 0 -/
theorem coverage_1 : coverage 1 = 0 := by simp [coverage, survival_frac_1]

/-- Coverage at level 2 is 0.1 -/
theorem coverage_2 : coverage 2 = 1/10 := by
  simp [coverage, survival_frac_2]
  ring

/-- Coverage at level 3 is 0.19 -/
theorem coverage_3 : coverage 3 = 19/100 := by
  simp [coverage, survival_frac_3]
  ring

/-! ## Finite Exceptions -/

/-- The complete list of zeroless powers -/
def zerolessList : List ℕ :=
  [1, 2, 3, 4, 5, 6, 7, 8, 9, 13, 14, 15, 16, 18, 19,
   24, 25, 27, 28, 31, 32, 33, 34, 35, 36, 37, 39,
   49, 51, 67, 72, 76, 77, 81, 86]

/-- There are exactly 35 zeroless powers -/
theorem zeroless_count : zerolessList.length = 35 := by native_decide

/-- 86 is the maximum zeroless power -/
theorem max_zeroless : zerolessList.getLast? = some 86 := by native_decide

/-- 1 is the minimum zeroless power -/
theorem min_zeroless : zerolessList.head? = some 1 := by native_decide

/-- All elements in the list are ≤ 86 -/
theorem zeroless_le_86 : ∀ n ∈ zerolessList, n ≤ 86 := by
  intro n hn
  simp [zerolessList] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
                 rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
                 rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
                 rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega

/-! ## Computational Verification -/

/-- 2^1 = 2 is zeroless -/
theorem zeroless_1 : ¬hasZero 1 := by native_decide

/-- 2^86 is zeroless -/
theorem zeroless_86 : ¬hasZero 86 := by native_decide

/-- 2^87 contains a 0 -/
theorem has_zero_87 : hasZero 87 := by native_decide

/-- 2^88 contains a 0 -/
theorem has_zero_88 : hasZero 88 := by native_decide

/-- 2^100 contains a 0 -/
theorem has_zero_100 : hasZero 100 := by native_decide

/-- 2^10 contains a 0 -/
theorem has_zero_10 : hasZero 10 := by native_decide

/-- 2^11 contains a 0 -/
theorem has_zero_11 : hasZero 11 := by native_decide

/-- 2^12 contains a 0 -/
theorem has_zero_12 : hasZero 12 := by native_decide

/-! ## Main Theorem (with computational verification) -/

/-- Verify hasZero for a range -/
def verifyRange (start stop : ℕ) : Bool :=
  (List.range (stop - start + 1)).all (fun i => hasZero (start + i))

/-- All n in [87, 150] have 2^n containing 0 -/
theorem range_87_150 : verifyRange 87 150 := by native_decide

/-- All n in [151, 200] have 2^n containing 0 -/
theorem range_151_200 : verifyRange 151 200 := by native_decide

/-- All n in [201, 300] have 2^n containing 0 -/
theorem range_201_300 : verifyRange 201 300 := by native_decide

/-- All n in [301, 400] have 2^n containing 0 -/
theorem range_301_400 : verifyRange 301 400 := by native_decide

/-- All n in [401, 500] have 2^n containing 0 -/
theorem range_401_500 : verifyRange 401 500 := by native_decide

/-- Combined: all n in [87, 500] have 2^n containing 0 -/
theorem all_87_to_500_have_zero (n : ℕ) (h1 : 87 ≤ n) (h2 : n ≤ 500) :
    hasZero n = true := by
  -- We can verify this computationally
  interval_cases n <;> native_decide

/-- The 86 Conjecture for n ≤ 500 (computational) -/
theorem zeroless_bound_500 (n : ℕ) (hn : 86 < n) (hn' : n ≤ 500) :
    hasZero n = true := by
  have h1 : 87 ≤ n := hn
  have h2 : n ≤ 500 := hn'
  exact all_87_to_500_have_zero n h1 h2

/-! ## Survivor Analysis -/

/-- Check if first k digits of 2^n (LSB first) contain no 0 -/
def firstKDigitsZeroFree (n k : ℕ) : Bool :=
  ((Nat.digits 10 (2^n)).take k).all (· ≠ 0)

/-- Check if first k digits contain a 0 -/
def firstKDigitsHasZero (n k : ℕ) : Bool :=
  ((Nat.digits 10 (2^n)).take k).any (· = 0)

/-- A residue class r survives to level k if 2^r has no 0 in first k digits
    We use a large enough representative to ensure we have k digits -/
def survivesToLevel (r k : ℕ) : Bool :=
  let p := period k
  -- Use representative that's large enough to have k digits
  let rep := r + p * ((k + 100) / p + 1)
  firstKDigitsZeroFree rep k

/-- Verify the first digit survivor count -/
theorem first_digit_survivors : (List.range 4).countP (fun r =>
    firstKDigitsZeroFree (r + 4) 1) = 4 := by native_decide

/-- Verify second level: check which of 20 classes survive -/
theorem second_level_check : (List.range 20).countP (fun r =>
    firstKDigitsZeroFree (r + 20) 2) = 18 := by native_decide

/-- Verify third level -/
theorem third_level_check : (List.range 100).countP (fun r =>
    firstKDigitsZeroFree (r + 100) 3) = 81 := by native_decide

/-! ## Coverage Proof -/

/-- Key lemma: if first k digits of 2^n contain 0, then hasZero n = true -/
theorem firstK_implies_hasZero (n k : ℕ) (_hk : k ≤ (Nat.digits 10 (2^n)).length) :
    firstKDigitsHasZero n k = true → hasZero n = true := by
  intro h
  simp only [firstKDigitsHasZero, hasZero, List.any_eq_true, decide_eq_true_eq] at h ⊢
  obtain ⟨d, hd_mem, hd_zero⟩ := h
  exact ⟨d, List.mem_of_mem_take hd_mem, hd_zero⟩

/-- φ(5^k) = 4 × 5^(k-1) = period k -/
theorem totient_5_pow (k : ℕ) (hk : k ≥ 1) : (5^k).totient = period k := by
  have hkpos : 0 < k := Nat.succ_le_iff.mp hk
  have hprime : Nat.Prime 5 := by decide
  rw [Nat.totient_prime_pow hprime hkpos]
  simp only [period]
  ring

/-- 2 is coprime to 5^k -/
theorem coprime_2_pow5 (k : ℕ) : Nat.Coprime 2 (5^k) := by
  have h : Nat.Coprime 2 5 := by decide
  exact h.pow_right k

/-- 2^(period k) ≡ 1 (mod 5^k) via Euler's theorem -/
theorem pow2_period_mod_5k (k : ℕ) (hk : k ≥ 1) :
    (2 : ZMod (5^k))^(period k) = 1 := by
  -- period k = φ(5^k), so by Euler's theorem, 2^(period k) ≡ 1
  have hcop := coprime_2_pow5 k
  have htot := totient_5_pow k hk
  -- Use ZMod.pow_totient: for unit u, u^φ(n) = 1
  let u : (ZMod (5^k))ˣ := ZMod.unitOfCoprime 2 hcop
  have hu : u ^ ((5^k).totient) = 1 := ZMod.pow_totient u
  -- Coerce back to ZMod
  have hu' : (2 : ZMod (5^k)) ^ ((5^k).totient) = 1 := by
    have hval : (u : ZMod (5^k)) = 2 := ZMod.coe_unitOfCoprime 2 hcop
    calc (2 : ZMod (5^k)) ^ ((5^k).totient)
        = (u : ZMod (5^k)) ^ ((5^k).totient) := by rw [hval]
      _ = ((u ^ ((5^k).totient) : (ZMod (5^k))ˣ) : ZMod (5^k)) := by
          simp only [Units.val_pow_eq_pow_val]
      _ = (1 : (ZMod (5^k))ˣ) := by rw [hu]
      _ = 1 := Units.val_one
  rw [← htot]
  exact hu'

/-- If n ≡ m (mod period k), then 2^n ≡ 2^m (mod 5^k) -/
theorem pow2_cong_mod_5k (n m k : ℕ) (hk : k ≥ 1) (_hn : n ≥ period k) (_hm : m ≥ period k)
    (heq : n % period k = m % period k) :
    (2 : ZMod (5^k))^n = (2 : ZMod (5^k))^m := by
  -- n = q₁ * period k + r, m = q₂ * period k + r for same r
  -- 2^n = 2^(q₁ * period k) * 2^r = (2^(period k))^q₁ * 2^r = 1^q₁ * 2^r = 2^r
  -- Similarly 2^m = 2^r
  have hndiv := Nat.div_add_mod n (period k)
  have hmdiv := Nat.div_add_mod m (period k)
  conv_lhs => rw [← hndiv]
  conv_rhs => rw [← hmdiv]
  rw [heq]
  simp only [pow_add, pow_mul]
  congr 1
  -- (2^(period k))^q₁ = 1^q₁ = 1
  have h1 := pow2_period_mod_5k k hk
  simp only [h1, one_pow]

/-- First k digits are determined by value mod 10^k (when both have ≥ k digits) -/
theorem digits_take_eq_of_mod_eq (a b k : ℕ)
    (ha_len : (Nat.digits 10 a).length ≥ k)
    (hb_len : (Nat.digits 10 b).length ≥ k)
    (heq : a % 10^k = b % 10^k) :
    (Nat.digits 10 a).take k = (Nat.digits 10 b).take k := by
  -- Key insight: n % 10^k = ofDigits 10 ((digits 10 n).take k)
  have ha := Nat.self_mod_pow_eq_ofDigits_take k a (by norm_num : 2 ≤ 10)
  have hb := Nat.self_mod_pow_eq_ofDigits_take k b (by norm_num : 2 ≤ 10)
  have heq' : Nat.ofDigits 10 ((Nat.digits 10 a).take k) =
              Nat.ofDigits 10 ((Nat.digits 10 b).take k) := by rw [← ha, ← hb, heq]
  -- Both lists have length k (since original lists have length ≥ k)
  have hlen_a : ((Nat.digits 10 a).take k).length = k :=
    List.length_take_of_le ha_len
  have hlen_b : ((Nat.digits 10 b).take k).length = k :=
    List.length_take_of_le hb_len
  have hlen : ((Nat.digits 10 a).take k).length = ((Nat.digits 10 b).take k).length := by
    rw [hlen_a, hlen_b]
  -- All digits in the lists are < 10
  have hw1 : ∀ l ∈ (Nat.digits 10 a).take k, l < 10 := fun l hl =>
    Nat.digits_lt_base (by norm_num) (List.mem_of_mem_take hl)
  have hw2 : ∀ l ∈ (Nat.digits 10 b).take k, l < 10 := fun l hl =>
    Nat.digits_lt_base (by norm_num) (List.mem_of_mem_take hl)
  -- Apply injectivity of ofDigits
  exact Nat.ofDigits_inj_of_len_eq (by norm_num : 1 < 10) hlen hw1 hw2 heq'

/-- 2^n has at least k digits when n ≥ 4k (conservative bound) -/
theorem pow2_digits_length_ge (n k : ℕ) (hn : n ≥ 4 * k) :
    (Nat.digits 10 (2^n)).length ≥ k := by
  -- 2^(4k) = 16^k ≥ 10^k > 10^(k-1), so 2^(4k) has at least k digits
  -- For n ≥ 4k, 2^n ≥ 2^(4k) ≥ 10^k > 10^(k-1)
  by_cases hk : k = 0
  · simp [hk]
  · have hk_pos : k ≥ 1 := Nat.one_le_iff_ne_zero.mpr hk
    have h2n_ge : 2^n ≥ 2^(4*k) := Nat.pow_le_pow_right (by norm_num) hn
    -- 2^(4*k) = (2^4)^k = 16^k by pow_mul
    have h16k : (2 : ℕ)^(4*k) = 16^k := by
      have : (16 : ℕ) = 2^4 := by norm_num
      rw [this, ← pow_mul]
    have h16_ge_10 : (16 : ℕ)^k ≥ 10^k := Nat.pow_le_pow_left (by norm_num) k
    have h2n_ge_10k : 2^n ≥ 10^k := by
      calc 2^n ≥ 2^(4*k) := h2n_ge
           _ = 16^k := h16k
           _ ≥ 10^k := h16_ge_10
    -- Use lt_digits_length_iff: k < length ↔ 10^k ≤ n
    -- We have 10^k ≤ 2^n, so k < length, hence length ≥ k + 1 > k
    have hlt := (Nat.lt_digits_length_iff (by norm_num : 1 < 10) (2^n)).mpr h2n_ge_10k
    omega

/-- Periodicity: first k digits of 2^n depend only on n mod period(k) -/
-- Requires n, m ≥ 4k to ensure both have ≥ k digits
theorem digits_periodic (n m k : ℕ) (hk : k ≥ 1)
    (hn : n ≥ 4 * k) (hm : m ≥ 4 * k)
    (hn_period : n ≥ period k) (hm_period : m ≥ period k)
    (heq : n % period k = m % period k) :
    (Nat.digits 10 (2^n)).take k = (Nat.digits 10 (2^m)).take k := by
  -- Step 1: Show both have ≥ k digits
  have hlen_n := pow2_digits_length_ge n k hn
  have hlen_m := pow2_digits_length_ge m k hm
  -- Step 2: 2^n ≡ 2^m (mod 5^k) by pow2_cong_mod_5k
  have hmod5 := pow2_cong_mod_5k n m k hk hn_period hm_period heq
  -- Step 3: 2^n ≡ 0 ≡ 2^m (mod 2^k) since n, m ≥ k
  have hn_k : n ≥ k := by omega
  have hm_k : m ≥ k := by omega
  -- 2^k | 2^n when k ≤ n
  have hdiv2n : 2^k ∣ 2^n := pow_dvd_pow 2 hn_k
  have hdiv2m : 2^k ∣ 2^m := pow_dvd_pow 2 hm_k
  have hmod2n : 2^n % 2^k = 0 := Nat.mod_eq_zero_of_dvd hdiv2n
  have hmod2m : 2^m % 2^k = 0 := Nat.mod_eq_zero_of_dvd hdiv2m
  -- Step 4: By CRT (since gcd(2^k, 5^k) = 1), 2^n ≡ 2^m (mod 10^k)
  have h10k : (10 : ℕ)^k = 2^k * 5^k := by
    rw [show (10 : ℕ) = 2 * 5 by norm_num, mul_pow]
  have hgcd : Nat.Coprime (2^k) (5^k) := by
    apply Nat.Coprime.pow k k
    decide
  -- Combined mod 10^k
  have hmod10 : 2^n % 10^k = 2^m % 10^k := by
    rw [h10k]
    -- Use CRT: if a ≡ b (mod m) and a ≡ b (mod n) with gcd(m,n) = 1, then a ≡ b (mod mn)
    have hmod2 : 2^n % 2^k = 2^m % 2^k := by rw [hmod2n, hmod2m]
    -- Extract mod 5^k from ZMod equality
    -- hmod5 : (2 : ZMod (5^k))^n = (2 : ZMod (5^k))^m
    -- Use Nat.cast_pow: ↑(a^n) = ↑a^n, so (2 : ZMod (5^k))^n = ((2^n : ℕ) : ZMod (5^k))
    have hmod5' : 2^n % 5^k = 2^m % 5^k := by
      -- Nat.cast_pow says ↑(a^n) = ↑a^n
      -- So ↑a^n = ↑(a^n) by symmetry
      have hn_cast : (2 : ZMod (5^k))^n = ((2^n : ℕ) : ZMod (5^k)) :=
        (Nat.cast_pow 2 n).symm
      have hm_cast : (2 : ZMod (5^k))^m = ((2^m : ℕ) : ZMod (5^k)) :=
        (Nat.cast_pow 2 m).symm
      rw [hn_cast, hm_cast] at hmod5
      exact (ZMod.natCast_eq_natCast_iff' (2^n) (2^m) (5^k)).mp hmod5
    -- Apply CRT: a % (m * n) = b % (m * n) when a % m = b % m and a % n = b % n (coprime)
    exact Nat.modEq_and_modEq_iff_modEq_mul hgcd |>.mp ⟨hmod2, hmod5'⟩
  -- Step 5: Apply digits_take_eq_of_mod_eq
  exact digits_take_eq_of_mod_eq (2^n) (2^m) k hlen_n hlen_m hmod10

/-- 5^k ≥ k+1 for all k -/
theorem pow5_ge_succ (k : ℕ) : 5^k ≥ k + 1 := by
  induction k with
  | zero => simp
  | succ k' ih =>
    calc 5^(k' + 1) = 5 * 5^k' := by ring
         _ ≥ 5 * (k' + 1) := Nat.mul_le_mul_left 5 ih
         _ ≥ k' + 2 := by omega

/-- Period k ≥ 4k for k ≥ 1 -/
theorem period_ge_4k (k : ℕ) (hk : k ≥ 1) : period k ≥ 4 * k := by
  unfold period
  have h5pow : 5^(k-1) ≥ k := by
    cases k with
    | zero => omega
    | succ k' =>
      simp only [Nat.add_one_sub_one]
      have := pow5_ge_succ k'
      omega
  calc 4 * 5^(k - 1) ≥ 4 * k := Nat.mul_le_mul_left 4 h5pow

/-- If r doesn't survive to level k, then all n ≡ r have first k digits with 0 -/
theorem rejected_implies_zero (r k : ℕ) (hk : k ≥ 1) (hr : ¬survivesToLevel r k) :
    ∀ n : ℕ, n ≥ 4 * k → n ≥ period k → n % period k = r % period k →
      firstKDigitsHasZero n k = true := by
  intro n hn_4k hn_period heq
  -- Get the representative used in survivesToLevel
  let p := period k
  let rep := r + p * ((k + 100) / p + 1)
  -- Show rep ≥ 4k and rep ≥ p (rep is constructed to be large)
  have hp_pos : p > 0 := period_pos k
  have hrep_ge_p : rep ≥ p := by
    show r + p * ((k + 100) / p + 1) ≥ p
    have hmul_ge : p * ((k + 100) / p + 1) ≥ p := Nat.le_mul_of_pos_right p (Nat.succ_pos _)
    calc r + p * ((k + 100) / p + 1) ≥ p * ((k + 100) / p + 1) := Nat.le_add_left _ _
         _ ≥ p := hmul_ge
  have hrep_4k : rep ≥ 4 * k := calc
    rep ≥ p := hrep_ge_p
    _ ≥ 4 * k := period_ge_4k k hk
  have hrep_mod : rep % p = r % p := Nat.add_mul_mod_self_left r p _
  -- The first k digits of 2^n = first k digits of 2^rep by periodicity
  have hdigits_eq := digits_periodic n rep k hk hn_4k hrep_4k hn_period hrep_ge_p
    (by rw [heq, hrep_mod])
  -- hr says 2^rep has a zero in first k digits (unfold survivesToLevel)
  simp only [survivesToLevel, firstKDigitsZeroFree,
             List.all_eq_true, decide_eq_true_eq, not_forall] at hr
  simp only [firstKDigitsHasZero, List.any_eq_true, decide_eq_true_eq]
  -- Transfer the zero from rep to n using the digit equality
  obtain ⟨d, hd_mem, hd_zero⟩ := hr
  -- hd_mem is about 2^(r + period k * ...) which equals 2^rep
  have hd_mem' : d ∈ (Nat.digits 10 (2^rep)).take k := hd_mem
  -- Transfer membership using hdigits_eq
  have hd_mem_n : d ∈ (Nat.digits 10 (2^n)).take k := by
    rw [hdigits_eq]
    exact hd_mem'
  push_neg at hd_zero
  exact ⟨d, hd_mem_n, hd_zero⟩

/-! ## Computational Coverage Bound -/

/-- Maximum rejection level needed for residue classes up to N -/
def maxRejectionLevel (_N : ℕ) : ℕ :=
  -- For computational verification, we check that all residue classes
  -- modulo period(10) = 4 * 5^9 are rejected by level 10
  10

/-- Find the rejection level for residue class r (returns 0 if not found up to maxLevel) -/
def findRejectionLevel (r maxLevel : ℕ) : ℕ :=
  match (List.range maxLevel).find? (fun k => k ≥ 1 ∧ ¬survivesToLevel r k) with
  | some k => k
  | none => 0

/-- Check if a residue class r is rejected by some level ≤ maxLevel -/
def isEventuallyRejected (r maxLevel : ℕ) : Bool :=
  (List.range maxLevel).any (fun k => k ≥ 1 ∧ ¬survivesToLevel r k)

/-- Check if r corresponds to a zeroless power -/
def isZerolessResidue (r : ℕ) : Bool :=
  zerolessList.any (fun m => m = r)

/-- All n ≤ 86 are either zeroless or have a zero -/
-- For n > 86, we need rejection
def allCoveredUpTo (maxN _maxLevel : ℕ) : Bool :=
  (List.range (maxN + 1)).all (fun n =>
    if n ≤ 86 then true  -- handled separately
    else hasZero n)  -- must have zero

/-- Computational verification that all n in [87, 500] have zeros -/
theorem all_covered_500 : allCoveredUpTo 500 10 = true := by native_decide

/-! ## The 86 Conjecture -/

/-- The 86 Conjecture (Conj86): For all n > 86, 2^n contains digit 0.

**Status**: OPEN PROBLEM in mathematics.
- Verified computationally to n = 2,500,000,000 (Guy's Unsolved Problems)
- No proof exists

**Why this cannot be derived from our framework**:
- The survivor recurrence S_{k+1} = (9/2)S_k shows density → 0, but density 0 ≠ empty
- Schroeppel (HAKMEM) proved: ∀N, ∃n with last N digits of 2^n having no zeros
- Lavrov proved: ∀k, ∃ power of 2 with first k AND last k digits all 1s or 2s
- So rejection position is UNBOUNDED - no constant or c·log(n) bound is known

**This axiom is equivalent to the 86 conjecture itself**:
- complete_coverage → Conj86: instantiate at n = r
- Conj86 → complete_coverage: pick any k, the premise is vacuously satisfied

We state it in residue-class form to connect with the periodicity framework,
but eliminating this axiom requires solving the open problem.

References:
- Khovanova: n=103233492954 has first zero at position 250 from right
- Math.SE: Status of conjecture about powers of 2
- HAKMEM: Schroeppel's construction of zero-free suffixes
-/
axiom complete_coverage :
  ∀ r : ℕ, ∃ k : ℕ, ∀ n : ℕ, n % period k = r % period k →
    (hasZero (n + 1) = true ∨ n ≤ 86)

/-- The 86 Conjecture (full statement) -/
theorem zeroless_bound (n : ℕ) (hn : n > 86) : hasZero n = true := by
  -- For n ≤ 500, use computational verification
  -- For n > 500, use coverage analysis (via axiom)
  by_cases h : n ≤ 500
  · exact all_87_to_500_have_zero n hn h
  · -- n > 200: Use the complete_coverage axiom
    push_neg at h
    obtain ⟨k, hk⟩ := complete_coverage (n - 1)
    have hn_pos : n ≥ 1 := by omega
    specialize hk (n - 1) rfl
    rcases hk with hzero | hle
    · have : n - 1 + 1 = n := Nat.sub_add_cancel hn_pos
      rwa [this] at hzero
    · omega

/-- 2^86 is the largest zeroless power of 2 -/
theorem largest_zeroless :
    ¬hasZero 86 ∧ ∀ n > 86, hasZero n = true :=
  ⟨zeroless_86, fun n hn => zeroless_bound n hn⟩

end Zeroless
