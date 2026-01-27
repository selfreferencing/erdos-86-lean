# Phase 3 Integration Guide

## Files Created

1. **`ED2/Type2CertDataExtended.lean`** - 142 certificates for uncovered primes 1M-10M
2. **`ED2/Type2CoveringExtended.lean`** - `native_decide` verification + bridge theorem

## Changes to Existence.lean

### Step 1: Add import (near top of file, with other imports)

```lean
import ErdosStraus.ED2.Type2CoveringExtended
```

### Step 2: Replace the sorry at line 4755-4757

**Current code (lines 4755-4757):**
```lean
                                                                            · /- Primes > 10^6 in uncovered residue classes.
                                                                                 Requires Phase 3: Dyachenko lattice density argument. -/
                                                                              sorry
```

**Replace with:**
```lean
                                                                            · /- Phase 3: 142 extended certificates for primes 10^6 < p < 10^7. -/
                                                                              by_cases h_ext : p ∈ ED2.extendedCertPrimes
                                                                              · exact ed2_extended_prime_covered p h_ext
                                                                              · /- Primes NOT in extended certificate list.
                                                                                   For full proof: needs asymptotic argument (Dyachenko Prop 9.25)
                                                                                   or certificates up to higher bound. -/
                                                                                sorry
```

## What This Achieves

- **Before**: sorry covers ALL primes in uncovered residue classes (infinitely many)
- **After**: sorry only covers primes NOT in the 142-entry certificate list
  - All uncovered primes below 10^7 have certificates
  - The remaining sorry fires only for primes >= 10^7 (or primes < 10^7
    that happen to be D.6-covered but not in the certificate list, which
    don't exist by construction)

## Build Instructions (when ready)

Close the Existence.lean tab in VS Code first, then:

```bash
cd /Users/kvallie2/Desktop/esc_stage8

# Step 1: Build the new files first (low memory)
lake build ErdosStraus.ED2.Type2CertDataExtended
lake build ErdosStraus.ED2.Type2CoveringExtended

# Step 2: Only after both succeed, build Existence
lake build ErdosStraus.ED2.Existence
```

Build each file separately to isolate memory usage. The extended cert
files should be lightweight (native_decide on 142 small structs).

## To Fully Eliminate the Sorry

The remaining sorry requires ONE of:
1. **More certificates**: extend to 10^8, 10^9, etc. (mechanical but doesn't finish)
2. **Asymptotic argument**: formalize Dyachenko Prop 9.25 application (finishes the proof)
   - The window lemma is already proven in `WindowLattice.lean`
   - Need: back-test bridge connecting lattice point to Type II solution
   - This is what the GPT prompt (`GPT_PROMPT_PHASE3.md`) targets
