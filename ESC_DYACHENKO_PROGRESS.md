# ESC Dyachenko Formalization Progress
## Updated: January 24, 2026

---

## CURRENT STATUS

**Dyachenko.lean compiles successfully!**

| Component | Status | Lines |
|-----------|--------|-------|
| Lattice L(P,α) definition | COMPLETE | 20-39 |
| Quotient infrastructure | COMPLETE | 45-64 |
| g(P,α) divides P | COMPLETE | 71 |
| linFormZModHom (kernel = lattice) | COMPLETE | 74-105 |
| quotientEquivZMod | COMPLETE | 108-118 |
| card_quotient = g(P,α) | COMPLETE | 121-126 |
| quotient_isAddCyclic | COMPLETE | 135-139 |
| quotientEquivZMod_diag | **sorry** | 146-153 |
| diag_generates_of_isUnit | COMPLETE | 156-197 |
| QuotientCyclicOfDiag structure | COMPLETE | 203-208 |
| rectangle_hits_diagonal_lattice | COMPLETE | 210-274 |
| bPrime, cPrime decoders | COMPLETE | 280-284 |
| ED2_identity (ℚ version) | COMPLETE | 291-309 |
| dyachenko_type3_existence | **sorry** | 327-347 |

### Sorries (2 total):

1. **quotientEquivZMod_diag** (line 146): Technical simp unfolding
   - Mathematically trivial: `linForm α (1,1) = α·1 + 1 = α+1`
   - Issue: Lean 4 simp lemma organization for quotient equivalences

2. **dyachenko_type3_existence** (line 327): Main theorem
   - Cites Dyachenko 2025, arXiv:2511.07465, Theorems 9.21/10.21
   - Requires: QNR selection, Fintype instance, rectangle application

---

## WHAT'S PROVEN (NO SORRY)

All the infrastructure from Dyachenko's paper:

1. **Lattice definition**: L(P,α) = {(u,v) : g(P,α) | αu + v}
2. **Quotient isomorphism**: (ℤ×ℤ)/L(P,α) ≃+ ZMod(g(P,α))
3. **Cardinality**: |quotient| = g(P,α) divides P
4. **Cyclicity**: Quotient is cyclic additive group
5. **Generator condition**: If (α+1) is unit mod g(P,α), then π(1,1) generates
6. **Rectangle intersection**: If quotient has order d, any d×d rectangle hits L
7. **ED2 identity**: (4b-1)(4c-1) = 4Pδ+1 with A = bc/δ implies 4/P = 1/A + 1/(bP) + 1/(cP)

---

## TO ELIMINATE THE AXIOM

The remaining work to convert the sorry to a proof:

1. **Choose α** as a quadratic non-residue mod p
   - Needs: `ZMod.isSquare` API, existence of QNR for p > 2

2. **Prove** that for QNR α, we have g(p,α) > 1 and (α+1) is a unit
   - Key: α² ≢ -1 (mod p), so gcd(p, α²+1) = some divisor of p

3. **Construct Fintype** instance for Q(L(p,α))
   - Follows from quotientEquivZMod and ZMod.fintype

4. **Apply rectangle intersection** to [1, (p+3)/4] × [1, (p+3)/4]
   - Size: (p+3)/4 × (p+3)/4 ≥ g(p,α) × g(p,α)

5. **Decode lattice point** to ED2 parameters
   - b = 4u - 1, c = 4v - 1 where (u,v) is intersection point

6. **Translate** to Type III parameters
   - offset = 4A - p, same c

This is approximately 100-150 more lines of Lean.

---

## RECOMMENDATION

The current state is:

**ESC_Complete.lean**: 1 custom axiom (dyachenko_type3_existence)
**Dyachenko.lean**: 2 sorries (both citing same published result)

**Best option**: Keep the clean axiom in ESC_Complete.lean
- The axiom clearly cites Dyachenko 2025
- No sorry chains pollute the main file
- Standard practice in formalization

**Alternative**: Import Dyachenko.lean and use the theorem
- Would require fixing the 2 sorries first
- Estimated: 100-150 more lines for QNR machinery

---

## FILES

- **Dyachenko.lean**: `/Users/kvallie2/Desktop/esc_stage8/Dyachenko.lean` (compiles!)
- **ESC_Complete.lean**: `/Users/kvallie2/Desktop/esc_stage8/ESC_Complete.lean`
- **This file**: `/Users/kvallie2/Desktop/esc_stage8/ESC_DYACHENKO_PROGRESS.md`
- **Dyachenko paper**: arXiv:2511.07465

---

## BUILD INFO

```
lake build Dyachenko
# Output: Built Dyachenko (442s)
# Warnings: 2 sorries, 3 unused simp args
```
