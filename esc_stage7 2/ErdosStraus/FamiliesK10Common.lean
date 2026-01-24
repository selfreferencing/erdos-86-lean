import Mathlib

import ErdosStraus.Basic
import ErdosStraus.Bradford
import ErdosStraus.Covering

/-!
# Stage 7 helper lemmas for the 10-k covering system

This file provides *generic* interfaces for k-families used in Stage 7.

Each `Families_k*.lean` file defines a predicate `kSufficient` and proves
`k_gives_solution` by reducing to a shared lemma here.

At Stage 7 we intentionally keep the “covering” theorem as a `sorry` (it is the
main remaining mathematical step). The algebraic steps are expected to be
available after Stage 6A (Bradford validity + coprimality).
-/

namespace ErdosStraus

/-- Bradford's `m` parameter for a fixed shift `k` when `x = ⌈p/4⌉ + k`.

For Mordell-hard primes we always have `p ≡ 1 (mod 4)`, so `x = (p + (4k+3)) / 4`.
Then `m = 4x - p = 4k + 3`.
-/
def mOfK (k : ℕ) : ℕ := 4 * k + 3

/-- The Bradford `x` candidate for a fixed `k`.

We use `x = (p + mOfK k) / 4`, which equals `⌈p/4⌉ + k` for `p ≡ 1 (mod 4)`.
-/
def xOfK (p k : ℕ) : ℕ := (p + mOfK k) / 4

/-! ## Helper lemmas for side conditions -/

/-- Mordell-hard primes are ≡ 1 (mod 4). -/
lemma mordell_hard_mod_4 (p : ℕ) (hMH : MordellHard840 p) : p % 4 = 1 := by
  -- All Mordell-hard residues mod 840 are ≡ 1 (mod 4):
  -- {1, 121, 169, 289, 361, 529} all satisfy r % 4 = 1
  unfold MordellHard840 at hMH
  rcases hMH with h | h | h | h | h | h <;> omega

/-- For Mordell-hard primes, 4 divides (p + mOfK k). -/
lemma four_dvd_p_add_mOfK (p k : ℕ) (hMH : MordellHard840 p) : 4 ∣ (p + mOfK k) := by
  have h4 := mordell_hard_mod_4 p hMH
  unfold mOfK
  omega

/-- For Mordell-hard primes, m p (xOfK p k) = mOfK k. -/
lemma m_xOfK_eq_mOfK (p k : ℕ) (hMH : MordellHard840 p) :
    m p (xOfK p k) = mOfK k := by
  unfold m xOfK mOfK
  have hdiv := four_dvd_p_add_mOfK p k hMH
  unfold mOfK at hdiv  -- Now hdiv : 4 ∣ (p + (4 * k + 3))
  obtain ⟨q, hq⟩ := hdiv
  -- hq : p + (4 * k + 3) = 4 * q
  rw [hq]
  -- Goal: 4 * ((4 * q) / 4) - p = 4 * k + 3
  have h1 : (4 * q) / 4 = q := Nat.mul_div_cancel_left q (by norm_num : 4 > 0)
  rw [h1]
  -- Goal: 4 * q - p = 4 * k + 3
  -- From hq: p + (4 * k + 3) = 4 * q, so 4 * q - p = 4 * k + 3
  omega

/-- xOfK p k > 0 for any prime p. -/
lemma xOfK_pos (p k : ℕ) (hp : Nat.Prime p) : xOfK p k > 0 := by
  unfold xOfK mOfK
  have hp2 := hp.two_le
  omega

/-- xOfK p k < p for Mordell-hard primes (when k is small enough). -/
lemma xOfK_lt_p (p k : ℕ) (hp : Nat.Prime p) (hMH : MordellHard840 p) (hk : k ≤ 29) :
    xOfK p k < p := by
  -- xOfK p k = (p + 4k + 3) / 4
  -- We need (p + 4k + 3) / 4 < p, i.e., p + 4k + 3 < 4p, i.e., 4k + 3 < 3p
  -- For k ≤ 29, we need 119 < 3p, i.e., p ≥ 40
  -- Mordell-hard primes p satisfy p % 840 ∈ {1, 121, 169, 289, 361, 529}
  -- These residues are all ≥ 1, and for p to be prime, p ≥ 41 (smallest Mordell-hard prime is 1009)
  have hp41 : p ≥ 41 := by
    unfold MordellHard840 at hMH
    -- p % 840 ∈ {1, 121, 169, 289, 361, 529}
    -- All these residues are squares that are not prime: 1, 11², 13², 17², 19², 23²
    -- If p < 840, then p % 840 = p, so p would be one of these squares
    -- But a prime > 1 is not a perfect square, so p ≥ 840 > 41
    rcases hMH with h | h | h | h | h | h
    · -- p % 840 = 1: if p < 840 then p = 1 (not prime), so p ≥ 841
      by_contra hlt
      push_neg at hlt
      have heq : p = 1 := by omega
      exact hp.ne_one heq
    · -- p % 840 = 121: if p < 840 then p = 121 = 11² (not prime)
      by_contra hlt
      push_neg at hlt
      have heq : p = 121 := by omega
      rw [heq] at hp
      have hdvd : 11 ∣ 121 := by norm_num
      have h1or121 := hp.eq_one_or_self_of_dvd 11 hdvd
      omega
    · -- p % 840 = 169 = 13²
      by_contra hlt
      push_neg at hlt
      have heq : p = 169 := by omega
      rw [heq] at hp
      have hdvd : 13 ∣ 169 := by norm_num
      have h1or169 := hp.eq_one_or_self_of_dvd 13 hdvd
      omega
    · -- p % 840 = 289 = 17²
      by_contra hlt
      push_neg at hlt
      have heq : p = 289 := by omega
      rw [heq] at hp
      have hdvd : 17 ∣ 289 := by norm_num
      have h1or289 := hp.eq_one_or_self_of_dvd 17 hdvd
      omega
    · -- p % 840 = 361 = 19²
      by_contra hlt
      push_neg at hlt
      have heq : p = 361 := by omega
      rw [heq] at hp
      have hdvd : 19 ∣ 361 := by norm_num
      have h1or361 := hp.eq_one_or_self_of_dvd 19 hdvd
      omega
    · -- p % 840 = 529 = 23²
      by_contra hlt
      push_neg at hlt
      have heq : p = 529 := by omega
      rw [heq] at hp
      have hdvd : 23 ∣ 529 := by norm_num
      have h1or529 := hp.eq_one_or_self_of_dvd 23 hdvd
      omega
  have h4 := mordell_hard_mod_4 p hMH
  have hdiv := four_dvd_p_add_mOfK p k hMH
  unfold mOfK at hdiv
  obtain ⟨q, hq⟩ := hdiv
  have hx_eq : (p + (4 * k + 3)) / 4 = q := by
    rw [hq]
    exact Nat.mul_div_cancel_left q (by norm_num : 4 > 0)
  unfold xOfK mOfK
  rw [hx_eq]
  -- Need q < p where 4q = p + 4k + 3
  -- Equivalently: p + 4k + 3 < 4p, i.e., 4k + 3 < 3p
  -- Since k ≤ 29 and p ≥ 41: 4*29 + 3 = 119 < 3*41 = 123 ✓
  omega

/-- gcd(x, 4x - p) = gcd(x, p) for natural numbers. -/
lemma gcd_x_4x_sub_p (x p : ℕ) (h : 4 * x ≥ p) :
    Nat.gcd x (4 * x - p) = Nat.gcd x p := by
  -- Key insight: any common divisor of x and (4x - p) divides p, and vice versa
  -- If d | x and d | (4x - p), then d | 4x and d | (4x - p), so d | (4x - (4x - p)) = p
  -- If d | x and d | p, then d | 4x and d | p, so d | (4x - p)
  apply Nat.dvd_antisymm
  · -- gcd(x, 4x-p) | gcd(x, p)
    apply Nat.dvd_gcd
    · exact Nat.gcd_dvd_left x (4 * x - p)
    · -- gcd(x, 4x-p) | p
      have hdvd_x : Nat.gcd x (4 * x - p) ∣ x := Nat.gcd_dvd_left x (4 * x - p)
      have hdvd_4xp : Nat.gcd x (4 * x - p) ∣ (4 * x - p) := Nat.gcd_dvd_right x (4 * x - p)
      have hdvd_4x : Nat.gcd x (4 * x - p) ∣ 4 * x := Dvd.dvd.mul_left hdvd_x 4
      -- 4x - (4x - p) = p (since 4x ≥ p)
      have heq : 4 * x - (4 * x - p) = p := Nat.sub_sub_self h
      calc Nat.gcd x (4 * x - p) ∣ 4 * x - (4 * x - p) := Nat.dvd_sub' hdvd_4x hdvd_4xp
        _ = p := heq
  · -- gcd(x, p) | gcd(x, 4x-p)
    apply Nat.dvd_gcd
    · exact Nat.gcd_dvd_left x p
    · -- gcd(x, p) | (4x - p)
      have hdvd_x : Nat.gcd x p ∣ x := Nat.gcd_dvd_left x p
      have hdvd_p : Nat.gcd x p ∣ p := Nat.gcd_dvd_right x p
      have hdvd_4x : Nat.gcd x p ∣ 4 * x := Dvd.dvd.mul_left hdvd_x 4
      exact Nat.dvd_sub h hdvd_4x hdvd_p

/-- Coprimality of x and m for Mordell-hard primes. -/
lemma coprime_xOfK_m (p k : ℕ) (hp : Nat.Prime p) (hMH : MordellHard840 p) (hk : k ≤ 29) :
    Nat.Coprime (xOfK p k) (m p (xOfK p k)) := by
  have hxpos := xOfK_pos p k hp
  have hxlt := xOfK_lt_p p k hp hMH hk
  -- m p (xOfK p k) = 4 * (xOfK p k) - p
  -- gcd(x, 4x - p) = gcd(x, p) = 1 since p is prime and x < p
  unfold Nat.Coprime m
  -- Need 4 * (xOfK p k) ≥ p
  have h4x : 4 * (xOfK p k) ≥ p := by
    unfold xOfK mOfK
    have h4 := mordell_hard_mod_4 p hMH
    omega
  have heq : Nat.gcd (xOfK p k) (4 * (xOfK p k) - p) = Nat.gcd (xOfK p k) p :=
    gcd_x_4x_sub_p (xOfK p k) p h4x
  rw [heq]
  -- gcd(x, p) = 1 since p prime and 0 < x < p
  exact Nat.Coprime.symm (hp.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt hxpos hxlt))

/-- The standard "d=1" parametric family (Stage 4/5):

If `p ≡ 12k+5 (mod 16k+12)`, then `d=1` is a Type II Bradford witness.

Equivalently, writing `m = 4k+3` and `4m = 16k+12`, this is the single residue class
`p ≡ -(m+4) (mod 4m)`.

This condition depends only on `p mod (16k+12)`.
-/
def d1Sufficient (k p : ℕ) : Prop := p % (16 * k + 12) = (12 * k + 5)

/-- Core witness lemma for the d=1 family.

When `p ≡ 12k+5 (mod 16k+12)`, then `d=1` is a Type II Bradford witness.

Key arithmetic:
- m = 4k + 3, so 4m = 16k + 12
- p ≡ 12k + 5 (mod 4m) implies p + m ≡ 16k + 8 (mod 4m)
- x = (p + m)/4 ≡ (16k + 8)/4 = 4k + 2 (mod m)
- 1 + x ≡ 4k + 3 = m ≡ 0 (mod m) ✓
-/
theorem d1Sufficient_witness
    (k p : ℕ) (hp : Nat.Prime p) (hMH : MordellHard840 p)
    (hsuff : d1Sufficient k p) :
    TypeIIWitness p (xOfK p k) 1 := by
  unfold TypeIIWitness
  refine ⟨one_dvd _, ?_, ?_⟩
  -- 1 ≤ x follows from x > 0
  · exact Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt (xOfK_pos p k hp))
  -- (1 + x) ≡ 0 (mod m) — the key step
  · have hm_eq : m p (xOfK p k) = mOfK k := m_xOfK_eq_mOfK p k hMH
    rw [hm_eq]
    -- Need: (1 + xOfK p k) % (mOfK k) = 0
    unfold Nat.ModEq
    simp only [Nat.zero_mod]
    -- Unfold definitions and use omega with the key facts
    unfold xOfK mOfK d1Sufficient at *
    -- hsuff : p % (16 * k + 12) = 12 * k + 5
    -- Need: (1 + (p + (4 * k + 3)) / 4) % (4 * k + 3) = 0
    have h4 := mordell_hard_mod_4 p hMH
    -- p % 4 = 1, so (p + 4k + 3) % 4 = (1 + 3) % 4 = 0
    have hdiv4 : 4 ∣ (p + (4 * k + 3)) := by omega
    obtain ⟨q, hq⟩ := hdiv4
    -- p + (4*k + 3) = 4 * q, so x = q
    have hx_eq : (p + (4 * k + 3)) / 4 = q := by
      rw [hq]; exact Nat.mul_div_cancel_left q (by norm_num : 4 > 0)
    rw [hx_eq]
    -- From hsuff: p = (16*k + 12) * t + (12*k + 5) for some t
    -- So p + (4*k + 3) = (16*k + 12) * t + (16*k + 8)
    -- Thus 4*q = (16*k + 12) * t + (16*k + 8)
    -- q = (4*k + 3) * t + (4*k + 2)
    -- 1 + q = (4*k + 3) * t + (4*k + 3) = (4*k + 3) * (t + 1)
    -- Therefore (1 + q) % (4*k + 3) = 0
    have hmod : (4 * k + 3) ∣ (1 + q) := by
      -- From hq: p + (4*k + 3) = 4*q
      -- From hsuff: p % (16*k + 12) = 12*k + 5
      -- Note: 16*k + 12 = 4 * (4*k + 3)
      -- Let t = p / (16*k + 12)
      set t := p / (16 * k + 12) with ht_def
      -- p = (16*k + 12) * t + (12*k + 5)
      have hp_form : p = (16 * k + 12) * t + (12 * k + 5) := by
        have hmod_eq : p % (16 * k + 12) = 12 * k + 5 := hsuff
        have hdiv_mod : p = (16 * k + 12) * t + p % (16 * k + 12) := (Nat.div_add_mod p (16 * k + 12)).symm
        rw [hmod_eq] at hdiv_mod
        exact hdiv_mod
      -- From hq: 4*q = p + (4*k + 3) = (16*k+12)*t + (12*k+5) + (4*k+3) = (16*k+12)*t + (16*k+8)
      -- So q = (4*k+3)*t + (4*k+2)
      have hq_form : q = (4 * k + 3) * t + (4 * k + 2) := by
        have h4q : 4 * q = p + (4 * k + 3) := hq.symm
        -- 4*q = (16*k+12)*t + (12*k+5) + (4*k+3) = (16*k+12)*t + (16*k+8)
        have h4q' : 4 * q = (16 * k + 12) * t + (16 * k + 8) := by
          calc 4 * q = p + (4 * k + 3) := h4q
            _ = (16 * k + 12) * t + (12 * k + 5) + (4 * k + 3) := by rw [hp_form]
            _ = (16 * k + 12) * t + (16 * k + 8) := by ring
        -- 4*q = 4*((4*k+3)*t + (4*k+2))
        have hfactor : (16 * k + 12) * t + (16 * k + 8) = 4 * ((4 * k + 3) * t + (4 * k + 2)) := by ring
        have h4q'' : 4 * q = 4 * ((4 * k + 3) * t + (4 * k + 2)) := by rw [h4q', hfactor]
        exact Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 4) h4q''
      -- 1 + q = (4*k+3)*t + (4*k+2) + 1 = (4*k+3)*t + (4*k+3) = (4*k+3)*(t+1)
      use t + 1
      calc 1 + q = 1 + ((4 * k + 3) * t + (4 * k + 2)) := by rw [hq_form]
        _ = (4 * k + 3) * t + (4 * k + 3) := by ring
        _ = (4 * k + 3) * (t + 1) := by ring
    exact Nat.mod_eq_zero_of_dvd hmod

/-- Generic bridge: `d=1` sufficiency implies `HasSolution p` via Bradford Type II.

This packages the "algebraic" side (Bradford validity + coprimality) and is reused
for every k-family.
-/
theorem d1Sufficient_gives_solution
    (k p : ℕ) (hp : Nat.Prime p) (hMH : MordellHard840 p)
    (hk : k ≤ 29) (hsuff : d1Sufficient k p) : HasSolution p := by
  -- Construct the witness.
  have hw : TypeIIWitness p (xOfK p k) 1 := d1Sufficient_witness (k := k) (p := p) hp hMH hsuff
  -- Bradford validity needs a few side conditions (`m>0`, `x<p`, `Coprime x m`).
  have hmpos : m p (xOfK p k) > 0 := by
    rw [m_xOfK_eq_mOfK p k hMH]
    unfold mOfK
    omega
  have hxlt : xOfK p k < p := xOfK_lt_p p k hp hMH hk
  have hcop : Nat.Coprime (xOfK p k) (m p (xOfK p k)) := coprime_xOfK_m p k hp hMH hk
  -- Apply Bradford.
  have hpos_and_es := bradford_typeII_valid (p := p) (x := xOfK p k) (d := 1) hp hmpos hxlt hw hcop
  rcases hpos_and_es with ⟨hypos, hzpos, hES⟩
  exact ⟨xOfK p k, bradfordY p (xOfK p k) 1, bradfordZ p (xOfK p k) 1,
    xOfK_pos p k hp, hypos, hzpos, hES⟩

end ErdosStraus
