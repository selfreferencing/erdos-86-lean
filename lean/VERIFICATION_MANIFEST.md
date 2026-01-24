# Erdős-Straus K10 Coverage - Verification Manifest

## Verification Order (dependency-sorted)

Send files to Aristotle in this order. Each file only depends on Mathlib, not on other project files (except K10CoverageMain.lean which is the assembly).

### Tier 1: Independent Components (can verify in parallel)
1. **GCDCoupling.lean** - GCD coupling lemma, prime isolation
2. **ComplementTrick.lean** - Complement d' = x²/d has same residue
3. **Mod210Setup.lean** - Mordell-hard classes mod 840, divisibility by 3
4. **DirectDivisibility.lean** - Direct m_k | x_k witness mechanism
5. **SmoothGapBound.lean** - R₀ = 4,252,385,304 (axiomatized)

### Tier 2: Characterizations (can verify in parallel)
6. **K0Characterization.lean** - k=0 ⟺ ∃ prime ≡ 2 (mod 3)
7. **K1Characterization.lean** - k=1 obstruction direction
8. **K2Characterization.lean** - k=2 residue cases mod 11

### Tier 3: Framework Components (can verify in parallel)
9. **SmallPrimeBreakers.lean** - NQR breakers with typeclass bridge
10. **AAFramework.lean** - A·A saturation, witness characterization
11. **ObstructionPatterns.lean** - Downward closure, minimal patterns

### Tier 4: Main Assembly (verify last)
12. **K10CoverageMain.lean** - Main theorem (currently `sorry`)

## Expected Errors

Some files use `sorry` for:
- Computed facts (R₀ smooth gap bound)
- Lemmas requiring extensive case analysis
- The main theorem itself (to be filled after component verification)

These are intentional placeholders, not bugs.

## Verification Commands

If Aristotle has Lean 4 + Mathlib available:
```bash
cd /path/to/lean/
lake update
lake build
```

## Key Theorems to Verify

1. `gcd_of_shifted` - gcd(r+a, r+b) | |a-b|
2. `complement_same_residue` - d' = x²/d has same residue as d
3. `k0_witness_iff` - k=0 characterization
4. `direct_divisibility_witness` - m | x ⟹ witness
5. `fails_of_dvd_of_fails` - Downward closure
6. `prod_set_saturates` - |A| > |G|/2 ⟹ A·A = G

## File Sizes

| File | Size |
|------|------|
| AAFramework.lean | 11KB |
| K2Characterization.lean | 15KB |
| K1Characterization.lean | 11KB |
| K0Characterization.lean | 6KB |
| Mod210Setup.lean | 5KB |
| ComplementTrick.lean | 5KB |
| GCDCoupling.lean | 4KB |
| SmallPrimeBreakers.lean | 4KB |
| DirectDivisibility.lean | 2KB |
| SmoothGapBound.lean | 3KB |
| ObstructionPatterns.lean | 4KB |
| K10CoverageMain.lean | 3KB |
