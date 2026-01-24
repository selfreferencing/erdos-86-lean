/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: b4946c2c-38c0-4324-b178-cc1a91abc306

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>
-/

/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 2df5f95b-3b4e-4126-9126-d405a4079486

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>
-/

import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic


open Nat

/--
Complement trick (residue preservation):

If `d ∣ x^2` and `d ≡ -x (mod m)` (encoded as `d % m = (m - x % m) % m`),
and `gcd x m = 1`, then the complementary divisor `d' = x^2 / d` also satisfies
`d' ≡ -x (mod m)`.
-/
lemma complement_same_residue (x m d : ℕ) (hm : 0 < m) (hx : 0 < x)
    (hgcd : Nat.gcd x m = 1) (hd_div : d ∣ x^2) (hd_pos : 0 < d)
    (hd_cong : d % m = (m - x % m) % m) :
    let d' := x^2 / d
    d' % m = (m - x % m) % m := by
  dsimp
  -- Abbreviate the standard natural representative of `-x (mod m)`
  let nx : ℕ := m - x % m

  have hd : d ≡ nx [MOD m] := by
    -- `Nat.ModEq m d nx` means `d % m = nx % m`
    -- and `nx % m = (m - x % m) % m`.
    simpa [Nat.ModEq, nx] using hd_cong

  have hcopr : Nat.Coprime x m := by
    exact Nat.coprime_iff_gcd_eq_one.2 hgcd

  -- Name the complementary divisor
  set d' : ℕ := x^2 / d

  -- x ≡ x % m (mod m)
  have hx_mod : x ≡ x % m [MOD m] := by
    unfold Nat.ModEq
    simp [Nat.mod_mod]

  -- (m - (x % m)) + (x % m) = m
  have hnx_sum : nx + (x % m) = m := by
    dsimp [nx]
    exact Nat.sub_add_cancel (Nat.le_of_lt (Nat.mod_lt x hm))

  -- m ≡ 0 (mod m)
  have hm0 : m ≡ 0 [MOD m] := by
    unfold Nat.ModEq
    simp

  -- nx + x ≡ 0 (mod m)
  have hnx0 : nx + x ≡ 0 [MOD m] := by
    have h1 : nx + x ≡ nx + (x % m) [MOD m] := hx_mod.add_left nx
    have h2 : nx + (x % m) ≡ 0 [MOD m] := by
      simpa [hnx_sum] using hm0
    exact h1.trans h2

  -- d + x ≡ 0 (mod m) from d ≡ nx and nx + x ≡ 0
  have hd_plus : d + x ≡ 0 [MOD m] := by
    have hdx : d + x ≡ nx + x [MOD m] := hd.add_right x
    exact hdx.trans hnx0

  -- Multiply by d' on the right: (d + x)*d' ≡ 0
  have hmul0 : (d + x) * d' ≡ 0 [MOD m] := by
    simpa [zero_mul] using hd_plus.mul_right d'

  -- Expand (d + x)*d' = d*d' + x*d'
  have hsum0 : d * d' + x * d' ≡ 0 [MOD m] := by
    simpa [add_mul] using hmul0

  -- Use divisibility: d * (x^2 / d) = x^2
  have hmul_dd' : d * d' = x^2 := by
    simpa [d'] using (Nat.mul_div_cancel' (x^2) hd_div)

  -- Replace d*d' by x^2
  have hsum1 : x^2 + x * d' ≡ 0 [MOD m] := by
    simpa [hmul_dd'] using hsum0

  -- Rewrite x^2 as x*x
  have hsum2 : x * x + x * d' ≡ 0 [MOD m] := by
    simpa [pow_two] using hsum1

  -- Factor: x*(x + d') = x*x + x*d'
  have hprod : x * (x + d') ≡ 0 [MOD m] := by
    simpa [mul_add, add_assoc, add_comm, add_left_comm] using hsum2

  -- Cancel x (since Coprime x m) to get x + d' ≡ 0
  have hxsum : x + d' ≡ 0 [MOD m] := by
    have hprod' : x * (x + d') ≡ x * 0 [MOD m] := by
      simpa [mul_zero] using hprod
    exact hprod'.cancel_left hcopr

  -- Add nx to both sides: nx + (x + d') ≡ nx
  have hadd : nx + (x + d') ≡ nx + 0 [MOD m] := hxsum.add_left nx
  have hadd' : (nx + x) + d' ≡ nx [MOD m] := by
    simpa [add_assoc, add_comm, add_left_comm] using hadd

  -- Since nx + x ≡ 0, we have (nx + x) + d' ≡ d'
  have hnx0_add : (nx + x) + d' ≡ d' [MOD m] := by
    have := hnx0.add_right d'
    simpa [add_assoc, zero_add] using this

  -- Combine to isolate d' ≡ nx
  have hres : d' ≡ nx [MOD m] := (hnx0_add.symm).trans hadd'

  -- Convert ModEq back to the `%`-equality required by the goal.
  simpa [Nat.ModEq, nx, d'] using hres

/--
Size bound:

For any `x > 0` and `d`, either `d ≤ x` or `x^2 / d ≤ x`.
(Here we keep the hypotheses from the prompt; the inequality itself doesn't actually
need `d ∣ x^2`.)
-/
lemma complement_size_bound (x d : ℕ) (hx : 0 < x) (hd_div : d ∣ x^2) (hd_pos : 0 < d) :
    d ≤ x ∨ x^2 / d ≤ x := by
  by_cases hdx : d ≤ x
  · exact Or.inl hdx
  · right
    have hlt : x < d := Nat.lt_of_not_ge hdx
    -- Multiply x < d on the right by x (x>0): x*x < d*x
    have hmul : x * x < d * x := by
      exact Nat.mul_lt_mul_of_pos_right hlt hx
    have hle : x^2 ≤ x * d := by
      have : x * x ≤ d * x := le_of_lt hmul
      -- rewrite into x^2 ≤ x*d
      simpa [pow_two, mul_comm, mul_left_comm, mul_assoc] using this
    exact Nat.div_le_of_le_mul hle

/--
If there exists *any* witness divisor `d` with the residue condition,
then there exists one with `d ≤ x` (either the original `d`, or the complementary divisor).
-/
lemma witness_exists_small (x m : ℕ) (hm : 0 < m) (hx : 0 < x) (hgcd : Nat.gcd x m = 1)
    (h : ∃ d, d ∣ x^2 ∧ 0 < d ∧ d % m = (m - x % m) % m) :
    ∃ d, d ∣ x^2 ∧ d ≤ x ∧ d % m = (m - x % m) % m := by
  rcases h with ⟨d, hd_div, hd_pos, hd_cong⟩
  have hsize : d ≤ x ∨ x^2 / d ≤ x :=
    complement_size_bound x d hx hd_div hd_pos
  cases hsize with
  | inl hdx =>
      exact ⟨d, hd_div, hdx, hd_cong⟩
  | inr hdx =>
      let d' : ℕ := x^2 / d
      have hd'_div : d' ∣ x^2 := by
        refine ⟨d, ?_⟩
        have hmul : d * d' = x^2 := by
          simpa [d'] using (Nat.mul_div_cancel' (x^2) hd_div)
        -- x^2 = d' * d
        simpa [mul_comm, mul_left_comm, mul_assoc] using hmul.symm

      have hd'_cong : d' % m = (m - x % m) % m := by
        simpa [d'] using
          (complement_same_residue x m d hm hx hgcd hd_div hd_pos hd_cong)

      exact ⟨d', hd'_div, hdx, hd'_cong⟩