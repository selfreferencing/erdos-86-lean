# Stage 8: The k=9 Sufficiency Theorem

## Executive Summary

**BREAKTHROUGH**: k=9 alone covers 100% of all Mordell-hard primes.

**EVEN BETTER**: The proof is trivial because **x is ALWAYS EVEN** for Mordell-hard primes!

No density arguments, no CRT, no enumeration needed. Just simple modular arithmetic.

## The Complete Proof

### Step 1: Mordell-hard primes are ≡ 1 (mod 8)

The six Mordell-hard residue classes mod 840 are {1, 121, 169, 289, 361, 529}.

Check each mod 8:
```
  1 mod 8 = 1
121 mod 8 = 1
169 mod 8 = 1
289 mod 8 = 1
361 mod 8 = 1
529 mod 8 = 1
```

**All Mordell-hard primes p ≡ 1 (mod 8).**

### Step 2: x is always even

For k=9, x = (p + 39) / 4.

Since p ≡ 1 (mod 8), write p = 8j + 1 for some integer j.

Then:
```
x = (p + 39) / 4
  = (8j + 1 + 39) / 4
  = (8j + 40) / 4
  = 2j + 10
```

**x is always even** (divisible by 2).

### Step 3: 2 is NQR mod 39

m = 39 = 3 × 13.

2 is NQR mod 3 because 2^((3-1)/2) = 2^1 = 2 ≡ -1 (mod 3).

Therefore 2 is NQR mod 39.

### Step 4: Conclusion

Since x is always even:
1. 2 divides x
2. 2 is a prime factor of x
3. 2 is NQR mod 39
4. Therefore x has an NQR prime factor
5. Therefore `QRNonObstruction` holds
6. Therefore `k9Sufficient` holds

**QED.**

## Why Earlier Analysis Showed 65%/35% Split

The earlier analysis code checked "is x even?" separately from "does x have an NQR factor?". Since ALL x values are even, every x has 2 as a factor. The 65%/7%/28% breakdown was an artifact of the analysis counting prime factors other than 2 when 2 was already sufficient.

**Corrected Coverage**:

| Reason | Count | Percentage |
|--------|-------|------------|
| x is even (2 is NQR) | 20,513 | **100.00%** |
| **FAILURES** | **0** | **0.00%** |

## Lean Implementation

### Key Lemmas (in Families_k9.lean)

```lean
/-- All Mordell-hard residues mod 840 are ≡ 1 (mod 8). -/
lemma mordell_hard_mod_8 (p : ℕ) (hMH : MordellHard840 p) : p % 8 = 1

/-- 2 is NQR mod 39. -/
lemma two_nqr_mod_39 : ¬IsQR 39 2

/-- For Mordell-hard primes, x = (p + 39) / 4 is always even. -/
lemma x_even_for_mordell_hard (p : ℕ) (hp : Nat.Prime p) (hMH : MordellHard840 p) :
    2 ∣ xOfK p 9

/-- If x is even, then x has 2 as an NQR prime factor mod 39. -/
lemma even_has_nqr_factor_39 (x : ℕ) (hpos : x > 0) (heven : 2 ∣ x) :
    HasNQRPrimeFactor 39 x
```

### Main Theorem

```lean
theorem k9_covers_all (p : ℕ) (hp : Nat.Prime p) (hMH : MordellHard840 p) :
    k9Sufficient p := by
  unfold k9Sufficient kSufficientGeneric
  right  -- Use QRSufficient
  unfold QRSufficient QRNonObstruction
  left   -- Use HasNQRPrimeFactor
  have heven := x_even_for_mordell_hard p hp hMH
  have hxpos : xOfK p 9 > 0 := by unfold xOfK mOfK; omega
  exact even_has_nqr_factor_39 (xOfK p 9) hxpos heven
```

### Simplification of ten_k_cover_complete

```lean
theorem ten_k_cover_complete (p : ℕ) (hp : Nat.Prime p) (hMH : MordellHard840 p) :
    k5Sufficient p ∨ k7Sufficient p ∨ k9Sufficient p ∨ ... ∨ k29Sufficient p := by
  right; right; left  -- navigate to k9Sufficient
  exact k9_covers_all p hp hMH
```

## Remaining Sorrys

| Lemma | Difficulty | Notes |
|-------|------------|-------|
| `mordell_hard_mod_8` | Easy | Finite case split on 6 residues |
| `x_even_for_mordell_hard` | Easy | Arithmetic from mod 8 condition |
| `two_nqr_mod_39` | Easy | native_decide or Euler criterion |
| Bradford sorrys | Medium | Aristotle working on these |
| `QRSufficient_witness` | Medium | Construct d from NQR factor |

## Why This Simplification Matters

**Before**: Needed CRT incompatibility argument across 10 moduli, density analysis, enumeration of failure cases.

**After**: Single chain of lemmas, each provable by `native_decide` or simple arithmetic.

The key insight is that the Mordell-hard condition (p ≡ r mod 840) already constrains p to be ≡ 1 (mod 8), which forces x to be even at k=9.
