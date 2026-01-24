# GPT Analysis: Salez Modular-Equation Framework

## Date: January 21, 2025

## Connection to Our Work

This response maps our (k,d) witness approach onto Salez's classification of constant-coefficient modular identities. Key reference: arXiv:1406.6307

---

## 1. Why 6 Resistant Classes = Square Subgroup

### Group-Theoretic Derivation (Repeated for Completeness)

```
(ℤ/840ℤ)* ≅ (ℤ/8ℤ)* × (ℤ/3ℤ)* × (ℤ/5ℤ)* × (ℤ/7ℤ)*

Squares in each factor:
- mod 8: {1}
- mod 3: {1}
- mod 5: {1, 4}
- mod 7: {1, 2, 4}

Square subgroup size: 1 × 1 × 2 × 3 = 6
```

Alternative calculation via squaring map kernel:
- Kernel = square roots of 1 mod 840
- Size = 4 × 2 × 2 × 2 = 32
- Image size = φ(840)/32 = 192/32 = 6

### Mordell's Sieve Characterization

Minimal counterexample y would satisfy:
- y ≡ 1 (mod 24)
- y ≡ ±1 (mod 5) [i.e., y is a square mod 5]
- y is a quadratic residue mod 7

This gives exactly 6 classes mod 840.

---

## 2. Why 11 is Forced, and 23 is Natural

### 11 is the First Unavoidable New Prime

840 = 2³ × 3 × 5 × 7 already contains small primes.

**Key fact**: Higher powers don't break the square obstruction:
- For odd prime q: if a is a square mod q and q∤a, then a remains a square mod q^k (Hensel)
- For 2^k with k ≥ 3: odd squares mod 2^k are exactly ≡ 1 (mod 8)

Therefore, the first genuinely new quadratic character comes from prime **11**.

### Why 23 is Natural (Not Uniquely Optimal)

Three objective functions give different answers:

| Criterion | Optimal Choice |
|-----------|----------------|
| Smallest new prime after 11 | 13, then 17, 19, 23 |
| Largest prime-filter coverage | 23 (certifies 9 of 22 nonzero residues) |
| Smallest k in 4k-1 form | 11 (k=3), then 23 (k=6) |

**For our m_k = 4k + 3 framework**: 23 = 4×6 - 1, making it natural since our moduli are of form 4k + 3.

---

## 3. Salez Prime Filters (Explicit)

From Salez (arXiv:1406.6307):

### Prime Filter S_11
```
S_11 = {0, 7, 8, 10}
```
Nonzero "easy" residues mod 11: {7, 8, 10}

### Prime Filter S_23
```
S_23 = {0, 7, 10, 11, 15, 17, 19, 20, 21, 22}
```
Nine nonzero "easy" residues: {7, 10, 11, 15, 17, 19, 20, 21, 22}

These are exactly the residues produced by Salez's equation (14a) with k=6 (since 23 = 4×6 - 1).

### Composite Cross-Filters (Critical!)

**S*_55 = {24, 39}** (mod 55 = 5 × 11)
**S*_77 = {46, 72}** (mod 77 = 7 × 11)

These composite filters certify classes that are NOT certified by 5, 7, 11 alone.

---

## 4. The 26/34 Split Explained

### Why 26 Easy, 34 Hard mod 9240

When you intersect the prime filter S_11 with the 6 square classes mod 840:

- **26** sub-classes are certified ("easy")
- **34** remain ("hard")

### Detailed Easy/Hard by Resistant Class

For r ∈ {1, 121, 169, 289, 361, 529}, the "easy" residues p mod 11 are:

| r mod 840 | Easy mod 11 | Hard mod 11 |
|-----------|-------------|-------------|
| 1 | {7, 8, 10} | {1, 2, 3, 4, 5, 6, 9} |
| 121 | {6, 7, 8, 10} | {1, 2, 3, 4, 5, 9} |
| 169 | {2, 6, 7, 8, 10} | {1, 3, 4, 5, 9} |
| 289 | {2, 6, 7, 8, 10} | {1, 3, 4, 5, 9} |
| 361 | {2, 7, 8, 10} | {1, 3, 4, 5, 6, 9} |
| 529 | {2, 6, 7, 8, 10} | {1, 3, 4, 5, 9} |

### Pattern Explanation

- **Always easy**: {7, 8, 10} from prime filter S_11
- **Sometimes easy**: {2, 6} from composite filters S*_55 and S*_77
- **Always hard**: {1, 3, 4, 5, 9} (mostly QR mod 11)

> Hard mod 11 is "mostly the quadratic residues mod 11", except for two non-residues (2, 6) that are rescued only when the fixed mod5/mod7 constraints align to hit the exceptional composite classes mod 55 or 77.

---

## 5. What Mod 23 is Really Doing

### The S_23 Filter Structure

The 9 nonzero residues {7, 10, 11, 15, 17, 19, 20, 21, 22} are exactly those produced by Salez's equation (14a) with BCD = 6.

In (14a), modulus m = 4BCD - 1. With BCD = 6: m = 23.

The congruence is:
```
B + pC ≡ 0 (mod 23)  ⟺  p ≡ -B/C (mod 23)
```

As B, C range over coprime divisors of 6, you get exactly those 9 residues.

### Missing Non-Residues

Two quadratic non-residues mod 23 (namely 5 and 14) are NOT hit by BCD = 6 parametrization.

These are handled by:
1. Other modular equation types (15b-15d)
2. Composite cross-filters involving 23
3. Further primes (13, 17, 19, ...)

---

## 6. Salez's 7 Modular Equation Types

Salez proves that for linear prime polynomials, there are only **7 modular-equation types** (14a-15d).

Each certified residue class corresponds to one fixed choice of constants, giving a **uniform explicit decomposition** for all p in that class.

This means: once you've refined enough, **a single witness (k,d)** works for all primes in that sub-class.

---

## 7. Actionable Certificate Simplification

### Minimal Conceptual Certificate (3 Levels)

**Level 1 (mod 840)**: Use Mordell's sieve. Everything handled unless p falls in one of the 6 square classes.

**Level 2 (mod 9240)**: Inside those 6 classes, declare "easy" exactly when:
```
p mod 11 ∈ {7, 8, 10}
   OR  p mod 55 ∈ {24, 39}
   OR  p mod 77 ∈ {46, 72}
```
This gives exactly 26 easy classes.

**Level 3 (×23)**: Remaining 34 classes handled by 23-based rule family (and analog composite cross-terms).

### Why This Structure is Minimal

- Some refinement beyond 840 is **forced** because the 6 square classes are exactly where small-prime modular identities cannot trigger
- Once you choose 11, you get a nontrivial hard remainder (34), so Level 3 is not just aesthetic
- You can "flatten" to modulus 212,520 but this just hides the decision tree

---

## 8. Universal Witnesses

**Key result**: In the Salez framework, once refined enough:
- Each certified residue class corresponds to ONE fixed choice of constants
- A single witness (k,d) works for ALL primes in that sub-class

**Implication for our approach**:
- If sub-class is fine enough (certified by single modular equation), one (k,d) suffices
- If sub-class is too coarse (e.g., p ≡ 1 mod 840), multiple witnesses unavoidable

---

## 9. Connection to Our K_COMPLETE

Our moduli m_k = 4k + 3 include:
- 3, 7, 11, 15, 19, **23**, 27, 31, 39, 47, **55**, 59, 67, 71, **77**, 79, 87, 95, 103, 107, 119, 127, 159, 167

Note: 55 = 5 × 11 and 77 = 7 × 11 appear naturally as composite values!

The K_COMPLETE set was empirically derived, but it matches the Salez framework:
- Prime filters for 11, 23
- Composite cross-filters for 55, 77

---

## 10. Next Step: Map Our (k,d) to Salez Types

To complete the connection, we need to map our explicit (k,d) rule:
```
x_k = (p + m_k)/4
d | x_k²
d ≡ -x_k (mod m_k)
```

onto Salez's equation types (14a-15d). This would tell us:
1. Which Salez types we're using at each level
2. Whether a single (k,d) must exist per class in our rule language

---

## References

- Salez: arXiv:1406.6307
- Eppstein (UCI): ics.uci.edu/~eppstein/numth/egypt/smallnum.html
- Wikipedia: Erdős-Straus conjecture
