import ErdosStraus.Basic
import ErdosStraus.Bradford
import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic

namespace ErdosStraus

/-- A lightweight “parametric family” wrapper.

The intended use is:
* choose a modulus `m`
* specify algebraic forms `x(t)` and `d(t)`
* prove the Bradford hypotheses (`d(t) ∣ x(t)^2`, `d(t) ≤ x(t)`, and `x(t)+d(t) ≡ 0 [MOD m]`)

Then Bradford yields explicit `y(t), z(t)` and an Erdős–Straus solution.

This is *not* the final architecture; it is a convenient template for building many families quickly.
-/
structure TypeIIFamily where
  m : ℕ
  x : ℕ → ℕ
  d : ℕ → ℕ
  hm_pos : 0 < m
  hdvd : ∀ t, d t ∣ (x t)^2
  hle : ∀ t, d t ≤ x t
  hcong : ∀ t, Nat.ModEq m (x t + d t) 0

/-- Given a Type II family at modulus `m`, and a prime `p` with `m = 4*x(t) - p`,
Bradford gives an Erdős–Straus solution for that `p`.

This lemma is the *bridge* used by a finite covering argument: you show each residue class of `p` admits
some `t` placing you in a family.
-/
theorem family_gives_solution
    (F : TypeIIFamily)
    (p : ℕ) (t : ℕ)
    (hp : Nat.Prime p)
    (hxlt : F.x t < p)
    (hm : F.m = 4 * (F.x t) - p) :
    Conjecture p := by
  -- rewrite Bradford hypotheses with `m = 4*x - p`.
  -- The remaining arithmetic glue is typically where the “finite covering” bookkeeping lives.
  subst hm
  -- At this stage we can call the Bradford theorem.
  -- From F.hm_pos : 0 < 4*x - p, derive p < 4*x using Nat.lt_of_sub_pos.
  have hplt : p < 4 * (F.x t) := Nat.lt_of_sub_pos F.hm_pos
  simpa using (bradford_type_ii_valid (p := p) (x := F.x t) (d := F.d t)
    hp hxlt hplt (F.hdvd t) (F.hle t) (by simpa using F.hcong t))

