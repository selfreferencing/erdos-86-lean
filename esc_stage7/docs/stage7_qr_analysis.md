# Stage 7 QR Obstruction Analysis

## Executive Summary

**BREAKTHROUGH**: The `QRSufficient` predicate covers **100%** of all 20,513 Mordell-hard primes ≤ 10^7.

This means the key theorem `ten_k_cover_complete` is empirically validated and reduces to proving the QR obstruction conditions are CRT-incompatible across the 10-k set.

## The QR Obstruction Pattern

### Bradford Type II Fails When:
1. **All prime factors of x are QR mod m**: The divisor residue set of x² is confined to the QR subgroup
2. **-x mod m is NQR**: The target residue class is outside the QR subgroup

### Bradford Type II Succeeds When EITHER:
- **x has an NQR prime factor** (breaks QR closure, all residues become reachable)
- **-x is QR mod m** (target is in the QR subgroup)

## Coverage Statistics

| Predicate | Coverage (20,513 primes) |
|-----------|--------------------------|
| d1Sufficient (any k) | 16.92% (3,471) |
| QRSufficient (any k) | **100.00%** (20,513) |
| Combined | **100.00%** (20,513) |

## QR Sets for Prime Moduli

| k | m = 4k+3 | Prime? | QR Set |
|---|----------|--------|--------|
| 5 | 23 | Yes | {1,2,3,4,6,8,9,12,13,16,18} |
| 7 | 31 | Yes | {1,2,4,5,7,8,9,10,14,16,18,19,20,25,28} |
| 11 | 47 | Yes | (23 elements) |
| 14 | 59 | Yes | (29 elements) |
| 17 | 71 | Yes | (35 elements) |
| 19 | 79 | Yes | (39 elements) |
| 26 | 107 | Yes | (53 elements) |

Composite moduli (k=9,23,29) have more complex QR structures but same obstruction principle applies.

## Why 100% Coverage

For a prime p to fail ALL 10 k-values, it would need:

```
(AllQR₅ ∧ TargetNQR₅) ∧ (AllQR₇ ∧ TargetNQR₇) ∧ ... ∧ (AllQR₂₉ ∧ TargetNQR₂₉)
```

Since x_k = ⌈p/4⌉ + k, consecutive x-values differ by small amounts:
- x₇ = x₅ + 2
- x₉ = x₅ + 4
- etc.

The prime factorizations of these values are essentially independent. For ALL of them to have only QR prime factors across 10 different moduli is astronomically unlikely.

Furthermore, even if AllQR_k holds, the target -x_k being NQR is an additional independent constraint at each modulus.

## Formal Proof Strategy

### Approach 1: CRT Density Argument
Show that the density of primes satisfying ALL 10 obstruction conditions is 0.

### Approach 2: Explicit Covering
For small subsets of k-values (e.g., just k=5,7), explicitly enumerate the residue classes where both fail, and show at least one of k=9,11,... covers those cases.

### Approach 3: Factorization Constraints
The condition "all prime factors of x are QR mod m" severely constrains x. Show that these constraints for different m-values are CRT-incompatible.

## Files Updated

- `FamiliesK10Common.lean`: Added QR definitions and QRSufficient predicate
- `Families_k*.lean`: Updated to use kSufficientGeneric (= d1Sufficient ∨ QRSufficient)
- `CoveringUnbounded.lean`: Updated documentation with QR analysis

## Remaining Sorrys

| File | Sorry | Status |
|------|-------|--------|
| ten_k_cover_complete | Prove QR coverage | **Key theorem** |
| QRSufficient_witness | Construct d from QR analysis | Medium |
| d1Sufficient_witness | Modular arithmetic | Easy |
| Bradford side conditions | m>0, x<p, coprimality | Easy |
| bradford_typeII_valid | Core ES identity | Aristotle working |

## Next Steps

1. **Aristotle**: Complete Bradford.lean sorrys
2. **Formalize**: Prove QRSufficient_witness using ZMod
3. **Prove**: ten_k_cover_complete via CRT incompatibility argument
