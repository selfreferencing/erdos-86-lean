import Mathlib
import ErdosStraus.Basic
import ErdosStraus.Bradford

namespace ErdosStraus

/-- The Stage 4/5 "Mordell-hard" congruence surrogate used in modular reasoning.

In the full project this may be refined to the 6 residue classes mod 840.
For Stage 5, the only fact we need is `p ≡ 1 (mod 12)`, which implies `x0(p) ≡ 1 (mod 3)`.
-/
def MordellHard (p : ℕ) : Prop := p % 12 = 1

/-- The baseline Bradford `x` for `p ≡ 1 (mod 4)`.

For `p = 4t+1`, this equals `t+1 = ⌈p/4⌉`.
-/
def x0 (p : ℕ) : ℕ := (p + 3) / 4

/-- The k=0 congruence modulus `m = 3`. -/
def m0 : ℕ := 3

/-- `k=0` works if there exists a Type II witness `d` at `x = x0(p)` and `m = 3`.

We use the additive form `d + x ≡ 0 (mod 3)`.
-/
def k0Works (p : ℕ) : Prop :=
  ∃ d : ℕ, d ∣ (x0 p)^2 ∧ d ≤ x0 p ∧ Nat.ModEq 3 (d + x0 p) 0

/-- Helper: under `p ≡ 1 (mod 12)`, the baseline `x0(p)` is `1 (mod 3)`. -/
lemma x0_mod3_of_mordellHard {p : ℕ} (h : MordellHard p) : (x0 p) % 3 = 1 := by
  -- p = 12a+1 ⇒ x0(p) = (p+3)/4 = 3a+1
  -- so mod 3 equals 1.
  --
  -- This is straightforward arithmetic; the cleanest proof in Mathlib uses `Nat.modEq_iff_dvd`.
  sorry

/--
**Stage 5 Theorem (k=0 characterization).**

For a Mordell-hard prime `p`, the k=0 Bradford search succeeds **iff**
`x0(p)` has a prime factor `q ≡ 2 (mod 3)`.

This is the formal counterpart of the Stage 4 observation:
> k=0 fails exactly when `x0` has only prime factors `≡ 0,1 (mod 3)`.
-/
theorem k0Works_iff_exists_primeFactor_mod3_eq2
    {p : ℕ} (hp : Nat.Prime p) (hMH : MordellHard p) :
    k0Works p ↔ ∃ q : ℕ, Nat.Prime q ∧ q ∣ x0 p ∧ q % 3 = 2 := by
  -- Outline:
  -- (→) From k0 witness d: d ∣ x0^2 and d ≡ -x0 ≡ 2 (mod 3). Choose a prime factor q|d with q≡2.
  --     Then q|x0^2 ⇒ q|x0.
  -- (←) If such a prime q|x0, set d=q. Then d|x0^2, d≤x0, and since x0≡1 mod3 we get d+x0≡0.
  --
  -- The only nontrivial ingredients are:
  --   * existence of a prime divisor q of d with q≡2 (mod 3) when d≡2 (mod 3)
  --   * prime divides square ⇒ divides base
  -- Both are available in Mathlib (`Nat.exists_prime_and_dvd`, `Nat.Prime.dvd_of_dvd_pow`).
  sorry

end ErdosStraus
