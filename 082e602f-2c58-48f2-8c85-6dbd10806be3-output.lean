/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 082e602f-2c58-48f2-8c85-6dbd10806be3

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem complementary_divisor_cong (A d e δ : ℕ)
    (hde : d * e = A * A)
    (hmod : δ ∣ (d + A))
    (hcop : Nat.Coprime A δ) :
    δ ∣ (e + A)

The following was negated by Aristotle:

- theorem coprime_A_delta (p A : ℕ) (hp : Nat.Prime p)
    (hA_pos : 0 < A) (hA_lt : A < p) :
    Nat.Coprime A (4 * A - p)

Here is the code for the `negate_state` tactic, used within these negations:

```lean
import Mathlib
open Lean Meta Elab Tactic in
elab "revert_all" : tactic => do
  let goals ← getGoals
  let mut newGoals : List MVarId := []
  for mvarId in goals do
    newGoals := newGoals.append [(← mvarId.revertAll)]
  setGoals newGoals

open Lean.Elab.Tactic in
macro "negate_state" : tactic => `(tactic|
  (
    guard_goal_nums 1
    revert_all
    refine @(((by admit) : ∀ {p : Prop}, ¬p → p) ?_)
    try (push_neg; guard_goal_nums 1)
  )
)
```
-/

import Mathlib


/-!
# Coprimality and Complementary Divisor Lemmas

Two lemmas needed for the ED2 Dyachenko bridge:

1. `coprime_A_delta`: gcd(A, 4A-p) = 1 when 0 < A < p and p is prime.
   Route: gcd(A, 4A-p) = gcd(A, p) (since 4A ≡ 0 mod A), and gcd(A, p) = 1
   since p is prime and A < p implies p ∤ A.

2. `complementary_divisor_cong`: If d*e = A*A, δ ∣ (d+A), and gcd(A,δ) = 1,
   then δ ∣ (e+A).
   Route: From d ≡ -A (mod δ) and d*e = A², get -A*e ≡ A² (mod δ),
   so A*(e+A) ≡ 0 (mod δ). Coprimality gives δ ∣ (e+A).
-/

/- Aristotle found this block to be false. Here is a proof of the negation:



theorem coprime_A_delta (p A : ℕ) (hp : Nat.Prime p)
    (hA_pos : 0 < A) (hA_lt : A < p) :
    Nat.Coprime A (4 * A - p) := by
  -- Wait, there's a mistake. We can actually prove the opposite.
  negate_state;
  -- Proof starts here:
  -- Choose $p = 37$ and $A = 9$.
  use 37, 9;
  -- Check that $37$ is prime.
  norm_num

-/
theorem coprime_A_delta (p A : ℕ) (hp : Nat.Prime p)
    (hA_pos : 0 < A) (hA_lt : A < p) :
    Nat.Coprime A (4 * A - p) := by
  sorry

theorem complementary_divisor_cong (A d e δ : ℕ)
    (hde : d * e = A * A)
    (hmod : δ ∣ (d + A))
    (hcop : Nat.Coprime A δ) :
    δ ∣ (e + A) := by
  -- From $d * e = A * A$, we get that $A * (e + A) \equiv 0 \pmod{\delta}$.
  have h_cong : A * (e + A) ≡ 0 [MOD δ] := by
    -- Since $δ$ divides $d + A$, we have $d ≡ -A \pmod{δ}$. Substituting this into $d * e = A * A$, we get $(-A) * e ≡ A * A \pmod{δ}$.
    have h_cong : (-A : ℤ) * e ≡ A * A [ZMOD δ] := by
      rw [ Int.modEq_iff_dvd ];
      obtain ⟨ k, hk ⟩ := hmod; use k * e; nlinarith;
    -- Rearrange h_cong to get A * (e + A) ≡ 0 [ZMOD δ].
    have h_rearrange : A * (e + A) ≡ 0 [ZMOD δ] := by
      convert h_cong.neg.add_right ( A * A ) using 1 <;> ring;
    exact Int.natCast_modEq_iff.mp h_rearrange;
  exact hcop.symm.dvd_of_dvd_mul_left <| Nat.dvd_of_mod_eq_zero h_cong