import ErdosStraus.Basic
import ErdosStraus.K1
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

namespace ErdosStraus

/-- The empirically discovered 10-k cover set used in Stages 6B–8. -/
def K10 : Finset ℕ := {5,7,9,11,14,17,19,23,26,29}

/-- The Bradford modulus `m = 4k + 3`. -/
def mK (k : ℕ) : ℕ := 4*k + 3

/-- The Bradford choice `x = x0(p) + k` (here `x0(p) = (p+3)/4` for odd primes `p ≡ 1 (mod 4)`). -/
def xK (p k : ℕ) : ℕ := x0 p + k

/-- The special congruence class where `d = 1` works in Bradford Type II:
`p ≡ 12k + 5 (mod 16k + 12)`.

This is *not* expected to cover all cases; it is a small, easy family. -/
def d1Sufficient (k p : ℕ) : Prop := p % (16*k + 12) = (12*k + 5)

/-- Witness-carrying sufficient condition for Bradford Type II construction.

`QRSufficient k p` means there exists a divisor `d` of `(xK p k)²` with `d ≤ xK p k`
and `d ≡ -xK p k (mod mK k)` (equivalently `xK p k + d ≡ 0 (mod mK k)`).

This is the correct formulation: having such a witness d directly enables
the Bradford Type II construction to produce an Erdős–Straus solution.

**Note**: The previous version used `constant` + `axiom` claiming that
obstruction failure implies witness existence. This was logically unsound:
¬(AllQR ∧ TargetNQR) does NOT imply ∃d with the required properties.
-/
def QRSufficient (k p : ℕ) : Prop :=
  ∃ d : ℕ, d ∣ (xK p k)^2 ∧ d ≤ xK p k ∧ Nat.ModEq (mK k) (xK p k + d) 0

/-- All prime factors of `xK p k` are quadratic residues modulo `mK k`.

This is the `AllQR_k` condition in the Stage 8 prompt.
We use the `IsQuadraticResidue` predicate from `ErdosStraus.K1`, which is
`IsSquare ((a : ZMod m))`.
-/
def AllQR (k p : ℕ) : Prop :=
  ∀ q : ℕ, Nat.Prime q → q ∣ xK p k → IsQuadraticResidue q (mK k)

/-- The target `-xK p k` is a quadratic **non**-residue modulo `mK k`.

This is the `TargetNQR_k` condition in the Stage 8 prompt.
-/
def TargetNQR (k p : ℕ) : Prop :=
  ¬ IsSquare (-(xK p k : ZMod (mK k)))

/-- The combined QR obstruction event. -/
def QROstruction (k p : ℕ) : Prop := AllQR k p ∧ TargetNQR k p

/-
**Removed**: The previous axiom `qr_obstruction_of_not_QRSufficient` was logically unsound.

It claimed: `¬ QRSufficient k p → QROstruction k p`

But this is FALSE. Counterexample from GPT analysis:
- p = 1009, k = 9, m = 39, x = 262
- Target: -x ≡ 11 (mod 39)
- QR obstruction is FALSE (2 is NQR mod 39, so not all prime factors are QR)
- BUT: No divisor of x² = 68644 is congruent to 11 (mod 39)

The correct approach is to use the witness-carrying `QRSufficient` existential above,
which directly provides the witness d when a solution exists via that k.
-/

/-- The per-k sufficiency predicate used in Stage 8: `d=1` family OR QR-based sufficiency. -/
def kSufficient (k p : ℕ) : Prop := d1Sufficient k p ∨ QRSufficient k p

-- Convenience abbreviations matching the Stage 8 prompt.
def k5Sufficient  (p : ℕ) : Prop := kSufficient 5 p
def k7Sufficient  (p : ℕ) : Prop := kSufficient 7 p
def k9Sufficient  (p : ℕ) : Prop := kSufficient 9 p
def k11Sufficient (p : ℕ) : Prop := kSufficient 11 p
def k14Sufficient (p : ℕ) : Prop := kSufficient 14 p
def k17Sufficient (p : ℕ) : Prop := kSufficient 17 p
def k19Sufficient (p : ℕ) : Prop := kSufficient 19 p
def k23Sufficient (p : ℕ) : Prop := kSufficient 23 p
def k26Sufficient (p : ℕ) : Prop := kSufficient 26 p
def k29Sufficient (p : ℕ) : Prop := kSufficient 29 p

/-- `xK` and `x_of` are the same function. -/
theorem xK_eq_x_of (p k : ℕ) : xK p k = x_of p k := rfl

/-- For primes with `p ≡ 1 (mod 4)`, `mK k = m_of p k`.

This follows because `x0 p = (p+3)/4` for such primes, so:
`m_of p k = 4*(x0 p + k) - p = 4*x0 p + 4k - p = (p+3) + 4k - p = 4k + 3 = mK k`
-/
theorem mK_eq_m_of_of_mod4 (p k : ℕ) (hp4 : p % 4 = 1) : mK k = m_of p k := by
  simp only [mK, m_of, x_of, x0]
  -- (p+3)/4 for p ≡ 1 (mod 4) gives (p+3)/4 = (p-1)/4 + 1
  -- We need: 4k + 3 = 4 * ((p+3)/4 + k) - p
  have hp3 : (p + 3) % 4 = 0 := by omega
  have hdiv : 4 * ((p + 3) / 4) = p + 3 := Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hp3)
  omega

/-- `QRSufficient k p` implies `HasBradfordII p k` for primes with p ≡ 1 (mod 4).

This connects the witness-carrying QRSufficient to the existential HasBradfordII predicate.
-/
theorem hasBradfordII_of_QRSufficient (p k : ℕ) (hp4 : p % 4 = 1) (hmpos : 0 < mK k)
    (hqr : QRSufficient k p) : HasBradfordII p k := by
  unfold HasBradfordII
  constructor
  · -- m ≠ 0
    have : m_of p k = mK k := (mK_eq_m_of_of_mod4 p k hp4).symm
    rw [this]
    exact Nat.ne_of_gt hmpos
  · -- ∃ d, ...
    obtain ⟨d, hd_dvd, hd_le, hd_cong⟩ := hqr
    use d
    have hxeq : x_of p k = xK p k := rfl
    have hmeq : m_of p k = mK k := (mK_eq_m_of_of_mod4 p k hp4).symm
    constructor
    · -- d ∣ x²
      simp only [hxeq]
      exact hd_dvd
    constructor
    · -- d ≤ x
      simp only [hxeq]
      exact hd_le
    · -- congruence
      simp only [hmeq, hxeq]
      exact hd_cong

/-- For Mordell-hard primes, `4 ∣ (p + mK k)`. -/
theorem four_dvd_p_plus_mK (p k : ℕ) (hp4 : p % 4 = 1) : 4 ∣ (p + mK k) := by
  unfold mK
  omega

/-- `xK p k` formula: `(p + mK k) / 4`. -/
theorem xK_formula (p k : ℕ) (hp4 : p % 4 = 1) : xK p k = (p + mK k) / 4 := by
  unfold xK x0 mK
  omega

/-- When `d1Sufficient k p`, we have `1 + xK p k ≡ 0 (mod mK k)`.

Key arithmetic:
- `16*k + 12 = 4 * (4*k + 3) = 4 * mK k`
- From `p % (4*mK k) = 12*k + 5`:
  - Write `p = (16*k + 12) * q + (12*k + 5)` for some q
  - Then `(p + 3) = 4 * ((4*k + 3) * q + (3*k + 2))`
  - So `(p + 3) / 4 = (4*k + 3) * q + (3*k + 2)`
  - Thus `xK p k = (p + 3) / 4 + k = (4*k + 3) * q + (4*k + 2)`
  - Therefore `xK p k + 1 = (4*k + 3) * (q + 1) ≡ 0 (mod 4*k + 3)`
-/
theorem d1Sufficient_congruence (k p : ℕ) (hp4 : p % 4 = 1) (hsuff : d1Sufficient k p) :
    Nat.ModEq (mK k) (xK p k + 1) 0 := by
  unfold d1Sufficient at hsuff
  unfold Nat.ModEq mK xK x0
  -- hsuff : p % (16 * k + 12) = 12 * k + 5
  -- Goal: ((p + 3) / 4 + k + 1) % (4 * k + 3) = 0 % (4 * k + 3)

  -- Extract q such that p = (16*k + 12) * q + (12*k + 5)
  have ⟨q, hq⟩ : ∃ q, p = (16 * k + 12) * q + (12 * k + 5) := by
    use p / (16 * k + 12)
    have hdiv := Nat.div_add_mod p (16 * k + 12)
    omega

  -- Key: (p + 3) = 4 * ((4*k + 3) * q + (3*k + 2))
  have hp3_eq : p + 3 = 4 * ((4 * k + 3) * q + (3 * k + 2)) := by
    calc p + 3 = (16 * k + 12) * q + (12 * k + 5) + 3 := by rw [hq]
      _ = (16 * k + 12) * q + (12 * k + 8) := by ring
      _ = 4 * (4 * k + 3) * q + 4 * (3 * k + 2) := by ring
      _ = 4 * ((4 * k + 3) * q + (3 * k + 2)) := by ring

  -- Therefore (p + 3) / 4 = (4*k + 3) * q + (3*k + 2)
  have hdiv_eq : (p + 3) / 4 = (4 * k + 3) * q + (3 * k + 2) := by
    rw [hp3_eq]
    exact Nat.mul_div_cancel_left _ (by norm_num : 0 < 4)

  -- xK p k + 1 = (p + 3) / 4 + k + 1 = (4*k + 3) * q + (4*k + 3) = (4*k + 3) * (q + 1)
  have hsum : (p + 3) / 4 + k + 1 = (4 * k + 3) * (q + 1) := by
    rw [hdiv_eq]
    ring

  -- Therefore ((p + 3) / 4 + k + 1) % (4*k + 3) = 0
  simp only [hsum, Nat.mul_mod_right, Nat.zero_mod]

/-- When `d1Sufficient k p` holds, d=1 is a valid `QRSufficient` witness. -/
theorem d1Sufficient_gives_QRSufficient (k p : ℕ) (hp4 : p % 4 = 1)
    (hsuff : d1Sufficient k p) : QRSufficient k p := by
  unfold QRSufficient
  use 1
  constructor
  · exact one_dvd _
  constructor
  · -- 1 ≤ xK p k
    unfold xK x0
    omega
  · exact d1Sufficient_congruence k p hp4 hsuff

end ErdosStraus
