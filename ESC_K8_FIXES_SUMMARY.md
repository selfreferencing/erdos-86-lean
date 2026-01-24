# Erdős-Straus Conjecture Formalization: K8Lemmas.lean Fixes

**Date:** 2026-01-20
**Session:** K8Lemmas.lean compilation error fixes

## Overview

This document summarizes the fixes applied to `/Users/kvallie2/Desktop/esc_stage8/ErdosStraus/K8Lemmas.lean` to resolve compilation errors. The file now compiles cleanly with no errors or warnings.

## Project Context

The Erdős-Straus Conjecture states that for every integer n ≥ 2, the fraction 4/n can be expressed as a sum of three unit fractions: 4/n = 1/x + 1/y + 1/z.

This Lean 4 formalization focuses on the **Bradford Type II construction** for handling "Mordell-hard" primes (those with p % 840 ∈ {1, 121, 169, 289, 361, 529}).

### Key Definitions (from FamiliesK10Common.lean)

```lean
-- The Bradford modulus m = 4k + 3
def mK (k : ℕ) : ℕ := 4*k + 3

-- The Bradford choice x = x0(p) + k where x0(p) = (p+3)/4
def xK (p k : ℕ) : ℕ := x0 p + k

-- Witness-carrying sufficient condition
def QRSufficient (k p : ℕ) : Prop :=
  ∃ d : ℕ, d ∣ (xK p k)^2 ∧ d ≤ xK p k ∧ Nat.ModEq (mK k) (xK p k + d) 0

-- QR obstruction (both conditions must hold)
def QROstruction (k p : ℕ) : Prop := AllQR k p ∧ TargetNQR k p
```

## K8Lemmas.lean: Purpose

K8Lemmas.lean contains the four key interface lemmas showing that **k=8 (m=35)** eliminates all symbolic QR obstructions for Mordell-hard primes:

1. **`mordell_hard_mod_12`**: Mordell-hard primes satisfy p ≡ 1 (mod 12)
2. **`three_divides_x_k8`**: For p ≡ 1 (mod 12), we have 3 ∣ x where x = (p+35)/4
3. **`three_nqr_mod_35`**: 3 is a quadratic non-residue mod 35
4. **`no_qr_obstruction_k8`**: The QR obstruction cannot hold at k=8 for Mordell-hard primes

The key insight: Since 3 divides x and 3 is NQR mod 35, the "AllQR" condition (all prime factors of x are QR mod m) cannot hold.

## Fixes Applied

### 1. `three_nqr_mod_5` (line 143-146)

**Problem:** `fin_cases y <;> simp_all [sq]` couldn't prove False from hypotheses like `3 = 0` in ZMod 5.

**Solution:** Use `native_decide` for computational verification:
```lean
theorem three_nqr_mod_5 : ¬ IsSquare (3 : ZMod 5) := by
  intro ⟨y, hy⟩
  fin_cases y <;> exact absurd hy (by native_decide)
```

### 2. `square_mod_35_implies_mod_5` (lines 153-169)

**Problem:** Unknown constant `ZMod.castHom_natCast` and calc chain type mismatches.

**Solution:** Rewrote using explicit ring homomorphism properties:
```lean
theorem square_mod_35_implies_mod_5 (a : ℕ) (h : IsSquare (a : ZMod 35)) :
    IsSquare (a : ZMod 5) := by
  obtain ⟨y, hy⟩ := h
  let f := ZMod.castHom (by norm_num : 5 ∣ 35) (ZMod 5)
  use f y
  have hfmul : f y * f y = f (y * y) := (map_mul f y y).symm
  have hfa : f (a : ZMod 35) = (a : ZMod 5) := by simp [f]
  calc (a : ZMod 5) = f (a : ZMod 35) := hfa.symm
    _ = f (y * y) := by rw [hy]
    _ = f y * f y := (map_mul f y y)
```

### 3. `mordell_hard_coprime_35` (lines 211-240)

**Problem:** omega couldn't prove `gcd(p, 35) = 1` from `gcd(p, 5) = 1` and `gcd(p, 7) = 1`.

**Solution:** Use `Nat.Coprime.mul_right`:
```lean
have h35 : 35 = 5 * 7 := by norm_num
rw [h35]
exact Nat.Coprime.mul_right hp5 hp7
```

### 4. `gcd_xK_mK_eq_gcd_p_mK` (lines 253-378)

This was the most complex fix, involving multiple sub-issues:

#### 4a. Divisibility Subtraction

**Problem:** `Nat.dvd_sub'` doesn't exist; `Nat.dvd_sub` has different argument order.

**Solution:** Use integer arithmetic with `linarith`:
```lean
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
```

#### 4b. Odd Divisor Lemma

**Problem:** `Nat.Odd.of_dvd_nat` doesn't exist.

**Solution:** Prove directly by contradiction:
```lean
have hg_odd : Odd (Nat.gcd p (mK k)) := by
  obtain ⟨r, hr⟩ := hm_odd
  obtain ⟨s, hs⟩ := hm_dvd
  by_contra heven
  simp only [Nat.not_odd_iff_even] at heven
  obtain ⟨t, ht⟩ := heven
  have : mK k = 2 * (t * s) := by rw [hs, ht]; ring
  rw [hr] at this
  omega
```

#### 4c. Coprimality with 4

**Problem:** `interval_cases` couldn't find upper bound on gcd.

**Solution:** Manually enumerate divisors of 4:
```lean
have hdivs : Nat.gcd 4 (Nat.gcd p (mK k)) = 1 ∨
             Nat.gcd 4 (Nat.gcd p (mK k)) = 2 ∨
             Nat.gcd 4 (Nat.gcd p (mK k)) = 4 := by
  have hdiv : Nat.gcd 4 (Nat.gcd p (mK k)) ∣ 4 := hdvd4
  rcases hdiv with ⟨c, hc⟩
  have hc_pos : 0 < c := by
    by_contra hle; push_neg at hle
    interval_cases c
    · simp only [mul_zero] at hc; omega
  have hle_c : c ≤ 4 := by
    by_contra hgt_c; push_neg at hgt_c
    have : Nat.gcd 4 (Nat.gcd p (mK k)) * c > 4 := by nlinarith
    omega
  interval_cases c
  · right; right; omega
  · right; left; omega
  · left; omega
  · omega
```

## Key Theorems Now Proven

| Theorem | Statement |
|---------|-----------|
| `mordell_hard_mod_12` | MordellHard p → p % 12 = 1 |
| `mordell_hard_mod_4` | MordellHard p → p % 4 = 1 |
| `mordell_hard_mod_3` | MordellHard p → p % 3 = 1 |
| `four_dvd_p_plus_35` | p % 12 = 1 → 4 ∣ (p + 35) |
| `three_dvd_p_plus_35` | p % 12 = 1 → 3 ∣ (p + 35) |
| `three_divides_x_k8` | p % 12 = 1 → 3 ∣ (p + 35) / 4 |
| `three_divides_xK_8` | MordellHard p → 3 ∣ xK p 8 |
| `three_nqr_mod_5` | ¬ IsSquare (3 : ZMod 5) |
| `square_mod_35_implies_mod_5` | IsSquare (a : ZMod 35) → IsSquare (a : ZMod 5) |
| `three_nqr_mod_35` | ¬ IsSquare (3 : ZMod 35) |
| `no_qr_obstruction_k8` | Nat.Prime p → MordellHard p → ¬ QROstruction 8 p |
| `mordell_hard_coprime_35` | Nat.Prime p → MordellHard p → Nat.Coprime p 35 |
| `four_mul_xK_eq` | p % 4 = 1 → 4 * xK p k = p + mK k |
| `gcd_xK_mK_eq_gcd_p_mK` | p % 4 = 1 → gcd(xK p k, mK k) = gcd(p, mK k) |
| `gcd_xK_8_eq_one` | Nat.Prime p → MordellHard p → gcd(xK p 8, 35) = 1 |

## Remaining Tasks

From the todo list:

1. **Formalize Bradford Type I construction for 18 primes** - The 18 easy primes that have direct Type I solutions
2. **Implement certificate verification with native_decide** - Use decidable checking for witness verification

## Lessons Learned

1. **`native_decide`** is essential for ZMod computations that `simp` can't handle
2. **Natural number subtraction** is tricky in Lean - often easier to lift to integers and use `linarith`
3. **`interval_cases`** needs explicit bounds - when proving divisor properties, manually establish bounds first
4. **`simp_all`** can cause recursion issues - prefer targeted `simp only` with specific lemmas
5. **Coprimality composition** uses `Nat.Coprime.mul_right` not omega

## File Locations

- Main lemmas: `/Users/kvallie2/Desktop/esc_stage8/ErdosStraus/K8Lemmas.lean`
- Shared definitions: `/Users/kvallie2/Desktop/esc_stage8/ErdosStraus/FamiliesK10Common.lean`
- Basic definitions: `/Users/kvallie2/Desktop/esc_stage8/ErdosStraus/Basic.lean`
- K1 lemmas: `/Users/kvallie2/Desktop/esc_stage8/ErdosStraus/K1.lean`

## Compilation

```bash
cd /Users/kvallie2/Desktop/esc_stage8
lake env lean ErdosStraus/K8Lemmas.lean
```

Should produce no output (clean compile).
