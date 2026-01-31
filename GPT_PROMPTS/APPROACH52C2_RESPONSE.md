# APPROACH 52C2: GPT Response — 18×18 Matrix Confirmation

## Summary

52C2 confirms 52C1's analysis using the exact Exp 82 pair counts.

## Key Results (Identical to 52C1)

| Quantity | Exp 82 Data | 52A/B Prediction |
|----------|-------------|------------------|
| p₀ = π̃(5,0) | **0.04877** | 0.0385 |
| \|λ₂\| | **0.01546** | 0.227 |
| ρ (survival) | **0.94853** | 0.9602 |
| Carry marginal P(c=0) | 0.4476 | — |
| Carry marginal P(c=1) | 0.5524 | — |

## Explicit 18×18 Matrix Structure

The matrix P has the form:
- Rows 1-4 (low digits, any carry): transition to c'=0 block
- Rows 5-9 (high digits, any carry): transition to c'=1 block
- Rows 10-13 = Rows 1-4 (carry doesn't change outgoing distribution)
- Rows 14-18 = Rows 5-9

**Key insight:** The outgoing row depends only on digit a, not on carry c. This is because the 9×9 pair data doesn't distinguish by carry state.

## Eigenvalue Analysis

Full 9×9 digit chain eigenvalues:
- λ₁ = 1
- **λ₂ ≈ -0.01546** (SLEM)
- All other eigenvalues < 0.015 in magnitude

> "This is **extremely** close to the i.i.d. case (uniform i.i.d. on 1–9 would give all other eigenvalues exactly 0)."

## Stationary Distribution

| digit d | π̃(d,0) | π̃(d,1) | π(d) |
|---------|---------|---------|------|
| 1 | 0.0524 | 0.0617 | 0.1141 |
| 2 | 0.0507 | 0.0618 | 0.1124 |
| 3 | 0.0499 | 0.0603 | 0.1101 |
| 4 | 0.0501 | 0.0608 | 0.1110 |
| **5** | **0.0488** | 0.0623 | 0.1110 |
| 6 | 0.0487 | 0.0613 | 0.1100 |
| 7 | 0.0489 | 0.0609 | 0.1098 |
| 8 | 0.0487 | 0.0608 | 0.1095 |
| 9 | 0.0495 | 0.0626 | 0.1120 |

## Explanation of the 0.227 Discrepancy

> "The |λ₂| ≈ 0.227 from the earlier carry proxy is **not describing the same positional dependence** that Exp-82 measures."

Three possible explanations for the mismatch:

1. **(3) Miscalibration / mismatch of meaning** - The H₀, H₁ from 52A weren't measuring the same "stay in class" probabilities as the low/high positional chain

2. **(1) Positional digit transitions are much closer to uniform** than the earlier carry proxy implied

3. **(2) "2×2 aggregation loses information"** is **NOT** the main culprit - the full 9×9 already has |λ₂| ~ 10⁻²

## Why Exp 82 May Understate Effects

> "Exp-82 is an *average over all positions and many n* and (crucially) uses *zeroless pairs*, which can wash out the **conditional/rare-event structure** that matters when you condition on extended zeroless survival."

This explains why earlier conditional experiments showed larger suppression/enhancement effects.

## What Missing Data Would Help

1. **Carry-conditioned transition matrices** Q^(0)[a][b] and Q^(1)[a][b]
   - Require triple counts or pairs stratified by previous digit being low/high
   - **We computed this in Exp 85**

2. **Include zeros** (full 10×10 or 10×10×10)

3. **Position stratification** (LSB vs middle vs MSB)

4. **Rare-event conditioning** - transitions from zeroless powers only
   - **We computed this in Exp 86**

## Reconciliation with Our Findings

Our Exp 85-86 provided exactly what 52C2 requested:

| Experiment | What It Tests | Result |
|------------|---------------|--------|
| Exp 85 | Carry-conditioned Q^(0), Q^(1) | |λ₂| ≈ 0.05, p₀ ≈ 0.0487 |
| Exp 86 | Zeroless powers only | Killing **enhanced** 25%, not suppressed |

**Both confirm the 52A/B model is invalid.** The digit transitions are nearly i.i.d. uniform regardless of how we condition.
