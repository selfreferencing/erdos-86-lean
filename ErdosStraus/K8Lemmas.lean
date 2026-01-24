import ErdosStraus.Basic
import ErdosStraus.FamiliesK10Common
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic

namespace ErdosStraus

/-!
# k=8 Interface Lemmas for Erdős-Straus Conjecture

This file contains the four key lemmas that show k=8 (m=35) eliminates all
symbolic QR obstructions for Mordell-hard primes.

## Main Results

* `mordell_hard_mod_12`: Mordell-hard primes satisfy p ≡ 1 (mod 12)
* `three_divides_x_k8`: For p ≡ 1 (mod 12), we have 3 ∣ x where x = (p+35)/4
* `three_nqr_mod_35`: 3 is a quadratic non-residue mod 35
* `no_qr_obstruction_k8`: The QR obstruction cannot hold at k=8 for Mordell-hard primes

## References

These lemmas were identified through multi-AI collaboration (GPT 5.2 Pro Extended)
as part of the ESC decomposition project, 2025-01-20.
-/

/-- The six Mordell-hard residue classes as a Finset. -/
def mordellHardResidues : Finset ℕ := {1, 121, 169, 289, 361, 529}

/-- Alternative definition of Mordell-hard using Finset membership. -/
def MordellHard' (p : ℕ) : Prop := p % 840 ∈ mordellHardResidues

/-- `MordellHard` and `MordellHard'` are equivalent. -/
theorem mordellHard_iff_mordellHard' (p : ℕ) : MordellHard p ↔ MordellHard' p := by
  unfold MordellHard MordellHard' mordellHardResidues
  simp only [Finset.mem_insert, Finset.mem_singleton]

/-!
## Lemma 3.1.A: Mordell-hard implies p ≡ 1 (mod 12)
-/

/-- All Mordell-hard residues are congruent to 1 mod 12.

This is verified by direct computation on the six residue classes:
- 1 % 12 = 1
- 121 % 12 = 1
- 169 % 12 = 1
- 289 % 12 = 1
- 361 % 12 = 1
- 529 % 12 = 1
-/
theorem mordell_hard_mod_12 (p : ℕ) (hp : MordellHard p) : p % 12 = 1 := by
  -- Since 12 ∣ 840, we have p % 12 = (p % 840) % 12
  have h840 : 12 ∣ 840 := by norm_num
  have hmod : p % 12 = (p % 840) % 12 := (Nat.mod_mod_of_dvd p h840).symm
  rw [hmod]
  -- Case analysis on the six Mordell-hard residue classes
  rcases hp with h1 | h121 | h169 | h289 | h361 | h529
  all_goals simp_all

/-- Corollary: Mordell-hard implies p ≡ 1 (mod 4). -/
theorem mordell_hard_mod_4 (p : ℕ) (hp : MordellHard p) : p % 4 = 1 := by
  have h12 : p % 12 = 1 := mordell_hard_mod_12 p hp
  have h4_12 : 4 ∣ 12 := by norm_num
  have : p % 4 = (p % 12) % 4 := (Nat.mod_mod_of_dvd p h4_12).symm
  simp [this, h12]

/-- Corollary: Mordell-hard implies p ≡ 1 (mod 3). -/
theorem mordell_hard_mod_3 (p : ℕ) (hp : MordellHard p) : p % 3 = 1 := by
  have h12 : p % 12 = 1 := mordell_hard_mod_12 p hp
  have h3_12 : 3 ∣ 12 := by norm_num
  have : p % 3 = (p % 12) % 3 := (Nat.mod_mod_of_dvd p h3_12).symm
  simp [this, h12]

/-!
## Lemma 3.1.B: 3 divides x for k=8
-/

/-- For p ≡ 1 (mod 12), we have 4 ∣ (p + 35). -/
theorem four_dvd_p_plus_35 (p : ℕ) (hp : p % 12 = 1) : 4 ∣ (p + 35) := by
  have hp4 : p % 4 = 1 := by
    have h4_12 : 4 ∣ 12 := by norm_num
    have : p % 4 = (p % 12) % 4 := (Nat.mod_mod_of_dvd p h4_12).symm
    simp [this, hp]
  have h : (p + 35) % 4 = 0 := by omega
  exact Nat.dvd_of_mod_eq_zero h

/-- For p ≡ 1 (mod 12), we have 3 ∣ (p + 35). -/
theorem three_dvd_p_plus_35 (p : ℕ) (hp : p % 12 = 1) : 3 ∣ (p + 35) := by
  have hp3 : p % 3 = 1 := by
    have h3_12 : 3 ∣ 12 := by norm_num
    have : p % 3 = (p % 12) % 3 := (Nat.mod_mod_of_dvd p h3_12).symm
    simp [this, hp]
  have h : (p + 35) % 3 = 0 := by omega
  exact Nat.dvd_of_mod_eq_zero h

/-- For p ≡ 1 (mod 12), we have 3 ∣ (p + 35) / 4.

This is Lemma 3.1.B: since gcd(3,4) = 1 and 3 ∣ (p+35) = 4x, we get 3 ∣ x.
-/
theorem three_divides_x_k8 (p : ℕ) (hp12 : p % 12 = 1) : 3 ∣ (p + 35) / 4 := by
  have h4 : 4 ∣ (p + 35) := four_dvd_p_plus_35 p hp12
  have h3 : 3 ∣ (p + 35) := three_dvd_p_plus_35 p hp12
  -- Since 4 ∣ (p+35), we have (p+35) = 4 * ((p+35)/4)
  have hdiv : p + 35 = 4 * ((p + 35) / 4) := by
    have := Nat.div_mul_cancel h4
    omega
  -- So 3 ∣ 4 * ((p+35)/4)
  rw [hdiv] at h3
  -- Since gcd(3,4) = 1, we get 3 ∣ (p+35)/4
  exact Nat.Coprime.dvd_of_dvd_mul_left (by norm_num : Nat.Coprime 3 4) h3

/-- For Mordell-hard p, 3 divides xK p 8. -/
theorem three_divides_xK_8 (p : ℕ) (hp : MordellHard p) : 3 ∣ xK p 8 := by
  have hp12 : p % 12 = 1 := mordell_hard_mod_12 p hp
  -- xK p 8 = x0 p + 8 = (p+3)/4 + 8
  -- For p ≡ 1 (mod 4), (p+3)/4 + 8 = (p+3+32)/4 = (p+35)/4
  simp only [xK, x0]
  -- We need to show (p+3)/4 + 8 = (p+35)/4 for p ≡ 1 (mod 4)
  have hp4 : p % 4 = 1 := mordell_hard_mod_4 p hp
  have hdiv4 : 4 ∣ (p + 3) := by
    have : (p + 3) % 4 = 0 := by
      have : (p + 3) % 4 = (p % 4 + 3) % 4 := Nat.add_mod p 3 4
      simp [this, hp4]
    exact Nat.dvd_of_mod_eq_zero this
  have hdiv4' : 4 ∣ (p + 35) := four_dvd_p_plus_35 p hp12
  have heq : (p + 3) / 4 + 8 = (p + 35) / 4 := by
    have h1 : (p + 3) / 4 * 4 = p + 3 := Nat.div_mul_cancel hdiv4
    have h2 : (p + 35) / 4 * 4 = p + 35 := Nat.div_mul_cancel hdiv4'
    omega
  rw [heq]
  exact three_divides_x_k8 p hp12

/-!
## Lemma 3.1.C: 3 is NQR mod 35
-/

/-- 3 is not a quadratic residue mod 5.

Squares mod 5 are {0, 1, 4}, and 3 ∉ {0, 1, 4}.
-/
theorem three_nqr_mod_5 : ¬ IsSquare (3 : ZMod 5) := by
  intro ⟨y, hy⟩
  -- Enumerate all y : ZMod 5 and check y^2 ≠ 3
  fin_cases y <;> exact absurd hy (by native_decide)

/-- If a is a square mod 35, then a is a square mod 5.

This follows because 5 ∣ 35, so the natural map ZMod 35 → ZMod 5
preserves squares.
-/
theorem square_mod_35_implies_mod_5 (a : ℕ) (h : IsSquare (a : ZMod 35)) :
    IsSquare (a : ZMod 5) := by
  obtain ⟨y, hy⟩ := h
  -- The projection ZMod 35 → ZMod 5 sends y to some y'
  let f := ZMod.castHom (by norm_num : 5 ∣ 35) (ZMod 5)
  use f y
  -- f is a ring hom, so f(y*y) = f(y)*f(y)
  have hfmul : f y * f y = f (y * y) := (map_mul f y y).symm
  -- f preserves nat casts: f(a : ZMod 35) = (a : ZMod 5)
  have hfa : f (a : ZMod 35) = (a : ZMod 5) := by simp [f]
  -- Goal: (a : ZMod 5) = f y * f y
  -- From hfa: f (a : ZMod 35) = (a : ZMod 5)
  -- From hy: (a : ZMod 35) = y * y
  -- So: (a : ZMod 5) = f (a : ZMod 35) = f (y * y) = f y * f y
  calc (a : ZMod 5) = f (a : ZMod 35) := hfa.symm
    _ = f (y * y) := by rw [hy]
    _ = f y * f y := (map_mul f y y)

/-- 3 is not a quadratic residue mod 35.

**Note**: The Jacobi symbol (3/35) = +1, but this does NOT imply 3 is a QR mod 35.
The correct proof reduces mod 5: since 3 is NQR mod 5 and 5 ∣ 35, 3 is NQR mod 35.
-/
theorem three_nqr_mod_35 : ¬ IsSquare (3 : ZMod 35) := by
  intro h
  have h5 : IsSquare (3 : ZMod 5) := square_mod_35_implies_mod_5 3 h
  exact three_nqr_mod_5 h5

/-- 3 is not a quadratic residue mod 35, stated using our IsQuadraticResidue predicate. -/
theorem three_nqr_mod_35' : ¬ IsQuadraticResidue 3 35 := by
  unfold IsQuadraticResidue
  exact three_nqr_mod_35

/-!
## Lemma 3.1.D: No QR obstruction at k=8
-/

/-- For Mordell-hard primes, the QR obstruction cannot hold at k=8.

The QR obstruction requires all prime factors of x to be QR mod m.
But 3 ∣ x (Lemma 3.1.B) and 3 is NQR mod 35 (Lemma 3.1.C), contradiction.
-/
theorem no_qr_obstruction_k8 (p : ℕ) (_hp : Nat.Prime p) (hMH : MordellHard p) :
    ¬ QROstruction 8 p := by
  intro hobs
  -- QROstruction 8 p means AllQR 8 p ∧ TargetNQR 8 p
  obtain ⟨hAllQR, _⟩ := hobs
  -- AllQR 8 p means all prime factors of xK p 8 are QR mod mK 8 = 35
  -- In particular, 3 must be QR mod 35 (since 3 is prime and 3 ∣ xK p 8)
  have h3_prime : Nat.Prime 3 := by norm_num
  have h3_dvd : 3 ∣ xK p 8 := three_divides_xK_8 p hMH
  have h3_qr : IsQuadraticResidue 3 (mK 8) := hAllQR 3 h3_prime h3_dvd
  -- But mK 8 = 35, and 3 is NQR mod 35
  have hmK8 : mK 8 = 35 := by simp [mK]
  rw [hmK8] at h3_qr
  exact three_nqr_mod_35' h3_qr

/-!
## Coprimality Lemma for k=8
-/

/-- Mordell-hard primes are coprime to 35.

We check that no Mordell-hard residue class is divisible by 5 or 7.
-/
theorem mordell_hard_coprime_35 (p : ℕ) (_hp : Nat.Prime p) (hMH : MordellHard p) :
    Nat.Coprime p 35 := by
  -- Show p is not divisible by 5 or 7
  have h5 : ¬ 5 ∣ p := by
    intro hdvd
    have : p % 5 = 0 := Nat.mod_eq_zero_of_dvd hdvd
    -- Check all Mordell-hard residues mod 5
    have h840_5 : 5 ∣ 840 := by norm_num
    have hmod : p % 5 = (p % 840) % 5 := (Nat.mod_mod_of_dvd p h840_5).symm
    rcases hMH with h1 | h121 | h169 | h289 | h361 | h529
    all_goals simp_all
  have h7 : ¬ 7 ∣ p := by
    intro hdvd
    have : p % 7 = 0 := Nat.mod_eq_zero_of_dvd hdvd
    have h840_7 : 7 ∣ 840 := by norm_num
    have hmod : p % 7 = (p % 840) % 7 := (Nat.mod_mod_of_dvd p h840_7).symm
    rcases hMH with h1 | h121 | h169 | h289 | h361 | h529
    all_goals simp_all
  -- Since p is prime and not divisible by 5 or 7, gcd(p, 35) = 1
  have hp5 : Nat.Coprime p 5 := by
    rw [Nat.coprime_comm, Nat.Coprime]
    have h5p : Nat.Prime 5 := by norm_num
    exact (h5p.coprime_iff_not_dvd).mpr h5
  have hp7 : Nat.Coprime p 7 := by
    rw [Nat.coprime_comm, Nat.Coprime]
    have h7p : Nat.Prime 7 := by norm_num
    exact (h7p.coprime_iff_not_dvd).mpr h7
  have h35 : 35 = 5 * 7 := by norm_num
  rw [h35]
  exact Nat.Coprime.mul_right hp5 hp7

/-- The key identity: 4 * xK p k = p + mK k for p ≡ 1 (mod 4). -/
theorem four_mul_xK_eq (p k : ℕ) (hp4 : p % 4 = 1) : 4 * xK p k = p + mK k := by
  simp only [xK, x0, mK]
  have hdiv : 4 ∣ (p + 3) := by
    have : (p + 3) % 4 = 0 := by
      have : (p + 3) % 4 = (p % 4 + 3) % 4 := Nat.add_mod p 3 4
      simp [this, hp4]
    exact Nat.dvd_of_mod_eq_zero this
  have h : (p + 3) / 4 * 4 = p + 3 := Nat.div_mul_cancel hdiv
  omega

/-- gcd(xK p k, mK k) = gcd(p, mK k) for p ≡ 1 (mod 4). -/
theorem gcd_xK_mK_eq_gcd_p_mK (p k : ℕ) (hp4 : p % 4 = 1) :
    Nat.gcd (xK p k) (mK k) = Nat.gcd p (mK k) := by
  -- Use the identity 4 * x = p + m
  have hid : 4 * xK p k = p + mK k := four_mul_xK_eq p k hp4
  -- m = 4k + 3 is odd
  have hm_odd : Odd (mK k) := by
    simp only [mK]
    exact ⟨2 * k + 1, by ring⟩
  -- Show both divisibility directions
  apply Nat.dvd_antisymm
  · -- gcd(x, m) ∣ gcd(p, m)
    apply Nat.dvd_gcd
    · -- gcd(x, m) ∣ p
      have hx : Nat.gcd (xK p k) (mK k) ∣ xK p k := Nat.gcd_dvd_left _ _
      have hm : Nat.gcd (xK p k) (mK k) ∣ mK k := Nat.gcd_dvd_right _ _
      have h4x : Nat.gcd (xK p k) (mK k) ∣ 4 * xK p k := Dvd.dvd.mul_left hx 4
      rw [hid] at h4x
      -- h4x : gcd | (p + mK k), hm : gcd | mK k
      -- Use: if d | a and d | b with b ≤ a, then d | (a - b)
      have hle : mK k ≤ p + mK k := Nat.le_add_left _ _
      -- If d | (a + b) and d | b, then d | a
      -- Proof: a = (a + b) - b, and d | (a+b) - b since both are divisible by d
      have hdvd_p : Nat.gcd (xK p k) (mK k) ∣ p := by
        -- gcd divides both (p + mK k) and mK k
        -- gcd divides any linear combination, in particular (p + mK k) - mK k = p
        have hlin : ∃ c : ℤ, (p : ℤ) = c * (Nat.gcd (xK p k) (mK k)) := by
          obtain ⟨q1, hq1⟩ := h4x
          obtain ⟨q2, hq2⟩ := hm
          use (q1 : ℤ) - (q2 : ℤ)
          have h1 : (p + mK k : ℤ) = (Nat.gcd (xK p k) (mK k) : ℤ) * (q1 : ℤ) := by
            have : (p + mK k : ℕ) = Nat.gcd (xK p k) (mK k) * q1 := hq1
            omega
          have h2 : (mK k : ℤ) = (Nat.gcd (xK p k) (mK k) : ℤ) * (q2 : ℤ) := by
            have : (mK k : ℕ) = Nat.gcd (xK p k) (mK k) * q2 := hq2
            omega
          linarith
        obtain ⟨c, hc⟩ := hlin
        have hpos : 0 ≤ c := by
          have hp_nn : (0 : ℤ) ≤ (p : ℤ) := Nat.cast_nonneg p
          have hg_pos : (0 : ℤ) < (Nat.gcd (xK p k) (mK k) : ℤ) ∨
                        (Nat.gcd (xK p k) (mK k) : ℤ) = 0 := by
            cases Nat.eq_zero_or_pos (Nat.gcd (xK p k) (mK k)) with
            | inl h => right; simp [h]
            | inr h => left; exact Nat.cast_pos.mpr h
          rcases hg_pos with hpos | hzero
          · by_contra hneg
            push_neg at hneg
            have : (p : ℤ) < 0 := by nlinarith
            linarith
          · simp [hzero] at hc; omega
        use c.toNat
        have hceq : (c.toNat : ℤ) = c := Int.toNat_of_nonneg hpos
        have : (p : ℤ) = (Nat.gcd (xK p k) (mK k) * c.toNat : ℤ) := by
          simp only [hceq, hc, mul_comm]
        exact Nat.cast_injective this
      exact hdvd_p
    · exact Nat.gcd_dvd_right _ _
  · -- gcd(p, m) ∣ gcd(x, m)
    apply Nat.dvd_gcd
    · -- gcd(p, m) ∣ x
      have hp_dvd : Nat.gcd p (mK k) ∣ p := Nat.gcd_dvd_left _ _
      have hm_dvd : Nat.gcd p (mK k) ∣ mK k := Nat.gcd_dvd_right _ _
      have hpm : Nat.gcd p (mK k) ∣ p + mK k := Nat.dvd_add hp_dvd hm_dvd
      rw [← hid] at hpm
      -- gcd(p, m) divides 4x and is odd, so divides x
      have hg_odd : Odd (Nat.gcd p (mK k)) := by
        -- If m is odd and d divides m, then d is odd
        obtain ⟨r, hr⟩ := hm_odd
        obtain ⟨s, hs⟩ := hm_dvd
        -- mK k = gcd * s, and mK k = 2r + 1
        by_contra heven
        simp only [Nat.not_odd_iff_even] at heven
        obtain ⟨t, ht⟩ := heven
        -- gcd = 2t, so mK k = 2t * s = 2(ts), contradicting oddness
        have : mK k = 2 * (t * s) := by rw [hs, ht]; ring
        rw [hr] at this
        omega
      have hg_coprime_4 : Nat.Coprime (Nat.gcd p (mK k)) 4 := by
        rw [Nat.Coprime, Nat.gcd_comm]
        -- gcd(4, g) = 1 because g is odd
        have h2_ndvd : ¬ (2 ∣ Nat.gcd p (mK k)) := Odd.not_two_dvd_nat hg_odd
        -- If gcd(4, g) > 1, then 2 | g (since prime factors of 4 are just 2)
        by_contra hne
        have hgt : Nat.gcd 4 (Nat.gcd p (mK k)) > 1 := by
          have hne1 : Nat.gcd 4 (Nat.gcd p (mK k)) ≠ 1 := hne
          have hpos : Nat.gcd 4 (Nat.gcd p (mK k)) > 0 := Nat.gcd_pos_of_pos_left _ (by norm_num)
          omega
        have hdvd' : Nat.gcd 4 (Nat.gcd p (mK k)) ∣ Nat.gcd p (mK k) := Nat.gcd_dvd_right _ _
        -- gcd divides 4, so it's 1, 2, or 4. Since > 1, it's 2 or 4.
        have hdvd4 : Nat.gcd 4 (Nat.gcd p (mK k)) ∣ 4 := Nat.gcd_dvd_left _ _
        -- Either way, 2 divides gcd p (mK k)
        have h2_dvd : 2 ∣ Nat.gcd p (mK k) := by
          -- gcd divides 4, so gcd ∈ {1, 2, 4}. Since gcd > 1, gcd ∈ {2, 4}.
          have hle4 : Nat.gcd 4 (Nat.gcd p (mK k)) ≤ 4 := Nat.gcd_le_left _ (by norm_num)
          have hdivs : Nat.gcd 4 (Nat.gcd p (mK k)) = 1 ∨
                       Nat.gcd 4 (Nat.gcd p (mK k)) = 2 ∨
                       Nat.gcd 4 (Nat.gcd p (mK k)) = 4 := by
            -- Divisors of 4 are exactly {1, 2, 4}
            have hpos : 0 < Nat.gcd 4 (Nat.gcd p (mK k)) := Nat.gcd_pos_of_pos_left _ (by norm_num)
            have hdiv : Nat.gcd 4 (Nat.gcd p (mK k)) ∣ 4 := hdvd4
            rcases hdiv with ⟨c, hc⟩
            have hc_pos : 0 < c := by
              by_contra hle
              push_neg at hle
              interval_cases c
              · simp only [mul_zero] at hc; omega
            have hle_c : c ≤ 4 := by
              by_contra hgt_c
              push_neg at hgt_c
              have : Nat.gcd 4 (Nat.gcd p (mK k)) * c > 4 := by nlinarith
              omega
            interval_cases c
            · right; right; omega
            · right; left; omega
            · left; omega
            · omega
          rcases hdivs with h1 | h2 | h4
          · omega  -- contradicts hgt > 1
          · rw [h2] at hdvd'; exact hdvd'
          · rw [h4] at hdvd'; exact Nat.dvd_trans (by norm_num : 2 ∣ 4) hdvd'
        exact h2_ndvd h2_dvd
      exact Nat.Coprime.dvd_of_dvd_mul_left hg_coprime_4 hpm
    · exact Nat.gcd_dvd_right _ _

/-- For Mordell-hard primes, gcd(xK p 8, 35) = 1. -/
theorem gcd_xK_8_eq_one (p : ℕ) (hp : Nat.Prime p) (hMH : MordellHard p) :
    Nat.gcd (xK p 8) 35 = 1 := by
  have hp4 : p % 4 = 1 := mordell_hard_mod_4 p hMH
  have hmK8 : mK 8 = 35 := by simp [mK]
  rw [← hmK8, gcd_xK_mK_eq_gcd_p_mK p 8 hp4, hmK8]
  exact mordell_hard_coprime_35 p hp hMH

end ErdosStraus
