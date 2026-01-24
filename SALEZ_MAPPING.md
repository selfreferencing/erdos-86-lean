# Mapping (k,d) Witnesses to Salez's Framework

## Date: January 21, 2025

## The Correct Decomposition Form

Our witness rule produces a **Type II decomposition** (two denominators divisible by p):

### Derivation

1. Since p + m = 4x, we have:
   ```
   4/p = (p+m)/(px) = 1/x + m/(px)
   ```

2. So it suffices to write m/x as sum of two unit fractions:
   ```
   m/x = 1/y + 1/z
   ```

3. Classical parametrization:
   ```
   1/y + 1/z = m/x  ⟺  (my - x)(mz - x) = x²
   ```

4. Choose any d | x² and set:
   ```
   my - x = d,  mz - x = x²/d
   ```
   Then:
   ```
   y = (x + d)/m,  z = (x + x²/d)/m
   ```

5. Integrality condition y ∈ ℤ is exactly **d ≡ -x (mod m)**

### Result

Our witness produces:
```
4/p = 1/x + 1/(py) + 1/(pz)

where y = (x+d)/m,  z = (x+x²/d)/m
```

This is the **Salez/Rosati Type II pattern**: two denominators are multiples of p.

---

## Salez's 7 Reference Equations

Salez's Proposition 3 splits constant-coefficient identities into 7 types (14a-15d):

| Family | Rosati Form | Denominators with p |
|--------|-------------|---------------------|
| **(14*)** | 4ABCD = A + B + pC | Two |
| **(15*)** | 4ABCD = p(A+B) + C | One |

**Our method sits on the (14*) / Rosati (A+B+pC) side.**

---

## Key Insight: Not Constant-Coefficient, But Same Moduli

### Salez (14a)
- Fixed congruence condition on p:
  ```
  B + pC ≡ 0 (mod 4BCD-1)
  ```
- B, C, D are constants
- Modulus is 4BCD - 1

### Our (k,d) Rule
- Fix m = 4k + 3 = 4(k+1) - 1
- Find divisor d | x² hitting d ≡ -x (mod m)
- **Factorization-driven**, not fixed residue class

### The Alignment

Our moduli m_k = 4k + 3 match (14a) moduli exactly:
```
m_k = 4k + 3 = 4(k+1) - 1  ⟺  BCD = k + 1
```

| k | m_k | BCD in (14a) |
|---|-----|--------------|
| 0 | 3 | 1 |
| 1 | 7 | 2 |
| 2 | 11 | 3 |
| 5 | 23 | 6 |
| 13 | 55 | 14 |

**Conclusion**: Our "choose k" step matches the (14a) modulus family. Our "find d" step goes **beyond** constant-coefficient (14a) by exploiting divisors of x².

---

## Why Composite Moduli (55, 77) Appear: Cross-Filters

### Salez's Filter Inheritance

Salez defines filters S_m (sets of residues mod m that certify solutions).

**Key property**: If q | m, certification mod q implies certification mod m.

This creates redundancy for composite m, so Salez defines **shortened filters**:
```
S*_m = residues in S_m NOT already certified by any proper divisor
```

### The Cross-Filter Values

| Modulus | Shortened Filter S*_m |
|---------|----------------------|
| 55 = 5×11 | {24, 39} |
| 77 = 7×11 | {46, 72} |

**Meaning**: These catch "leftover" residue classes that slip past the prime-factor filters.

This is exactly the cross-filter/interaction effect we observed empirically.

---

## k=5 ↔ m_k=23 ↔ BCD=6 Alignment

### Our k=5
- m_k = 4×5 + 3 = 23

### Salez (14a) with modulus 23
- 4BCD - 1 = 23 ⟹ BCD = 6

### Salez's Filter S_23
```
S_23 = {0, 7, 10, 11, 15, 17, 19, 20, 21, 22}
```

### Derivation
Enumerate all factorizations BCD = 6 with coprimality constraints:
- (B,C,D) ∈ {(1,1,6), (1,2,3), (1,3,2), (1,6,1), (2,1,3), (2,3,1), (3,1,2), (3,2,1), (6,1,1)}

For each, the congruence B + pC ≡ 0 (mod 23) gives residues.

Result: exactly the **nine nonzero residues** {7, 10, 11, 15, 17, 19, 20, 21, 22}.

The "0" is included because multiples of 23 are automatically trapped.

**Conclusion**: k=5 aligns exactly with Salez's (14a) modulus-23 filter.

---

## Implications for K_COMPLETE

1. Our (k,d) method lives in the **Rosati / Salez (14*) universe** (two denominators divisible by p)

2. It is **not restricted to constant-coefficient subfamilies** - we exploit factorization structure

3. The moduli m_k = 4k+3 line up with natural (14a) moduli 4BCD-1

4. Salez's filter analysis explains why:
   - Prime moduli (like 23) have specific filter sets
   - Composite moduli (like 55, 77) catch cross-filter residues

5. **K_COMPLETE is optimal within this framework**: it provides the necessary moduli to cover all residue classes through the (14a) structure plus cross-filters

---

## Summary Table: K_COMPLETE ↔ Salez

| k | m_k | Type | BCD | Filter Size |
|---|-----|------|-----|-------------|
| 0 | 3 | Prime | 1 | 2 |
| 1 | 7 | Prime | 2 | 4 |
| 2 | 11 | Prime | 3 | 4 |
| 3 | 15 | Composite | 4 | Cross-filter |
| 5 | 23 | Prime | 6 | 10 |
| 13 | 55 | Composite | 14 | Cross-filter |

**Note on 77**: 77 is NOT of form 4BCD-1 since (77+1)/4 = 19.5 ∉ ℤ. It comes from the (15*) family (mod F), not (14a).

The prime moduli provide independent quadratic character tests.
The composite moduli provide cross-filter coverage for interaction effects.

---

## Explicit S_23 Derivation (from GPT Response B)

For BCD = 6, enumerate all (B,C,D) factorizations:

| (B,C,D) | Residue p ≡ -B·C⁻¹ (mod 23) |
|---------|----------------------------|
| (1,1,6) | 22 |
| (1,2,3) | 11 |
| (1,3,2) | 15 |
| (1,6,1) | 19 |
| (2,1,3) | 21 |
| (2,3,1) | 7 |
| (3,1,2) | 20 |
| (3,2,1) | 10 |
| (6,1,1) | 17 |

**Result**: S_23 = {0, 7, 10, 11, 15, 17, 19, 20, 21, 22}

Our k=5 corresponds most naturally to (B,C,D) = (1,1,6), giving p ≡ 22 ≡ -1 (mod 23).

---

## Key Clarification: Dynamic Union vs Constant-Coefficient

Our method is:
> **(14a)-shaped at the modulus level**, but **not a single (14a) congruence class**

It's a **dynamic union** of many (14a)-style subcases, with the choice driven by prime factors of x_k.

- **Salez (14a)**: Constants (B,C,D) → fixed congruence class for p
- **Our (k,d) rule**: Pick m_k, compute x_k, then search for divisor d | x_k² with d ≡ -x_k (mod m_k)

The "residue mechanism" depends on **factorization of x_k**, not only on p mod m_k.

---

## Why Composite Moduli Are Powerful

Two effects create the "cross-filter" phenomenon:

1. **CRT structure**: Working mod 55 = 5×11 simultaneously encodes mod 5 AND mod 11 constraints

2. **More factorizations**: Composite BCD → more (B,C) divisor choices → more residue classes covered
   - BCD = 14 has factorizations: (1,1,14), (1,2,7), (1,7,2), (1,14,1), (2,1,7), (2,7,1), (7,1,2), (7,2,1), (14,1,1)
   - Each produces a different residue class mod 55
