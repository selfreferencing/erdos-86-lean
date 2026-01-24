# GPT Analysis: Quadratic Character Structure of Resistant Classes

## Date: January 21, 2025

## Key Insight: Resistant Classes = Square Subgroup

The 6 resistant classes {1, 121, 169, 289, 361, 529} mod 840 are **exactly the square subgroup** G² ⊆ (ℤ/840ℤ)*.

### Group-Theoretic Derivation

```
840 = 2³ × 3 × 5 × 7

(ℤ/840ℤ)* ≅ (ℤ/8ℤ)* × (ℤ/3ℤ)* × (ℤ/5ℤ)* × (ℤ/7ℤ)*
```

Image of squaring map on each factor:
- mod 8: every odd square ≡ 1 (mod 8), so squares = {1}
- mod 3: 1² ≡ 2² ≡ 1, so squares = {1}
- mod 5: squares = {1, 4}
- mod 7: squares = {1, 2, 4}

Combined constraint for being a square mod 840:
```
n ≡ 1 (mod 24)
n ≡ 1 or 4 (mod 5)
n ≡ 1, 2, or 4 (mod 7)
```

This gives exactly 1 × 2 × 3 = **6 residue classes** via CRT:
```
{1, 121, 169, 289, 361, 529}
```

### Why This Matters

**G² is the kernel of every quadratic character** coming from prime-power factors of 840 (mod 8, mod 3, Legendre symbols mod 5, mod 7).

**Schinzel/Mordell Obstruction**: If you have a uniform modular identity solving ESC on arithmetic progression at + b, then **b cannot be a quadratic residue modulo a**.

This explains why these 6 classes are "structurally resistant" to congruence-based methods.

---

## Why 11 is Forced as First Refinement

Refining by higher powers of 2, 3, 5, 7 **does NOT create new quadratic information**:
- A unit that is a square mod p lifts to a square mod p^k (odd p)
- "Square mod 2^k" stabilizes at ≡ 1 (mod 8)

**Therefore**: To break the square-subgroup phenomenon, you MUST introduce a prime not dividing 840.

**11 is optimal by size** as the first new prime.

---

## Is 23 Optimal as Second Refinement?

**No, not uniquely optimal in the abstract.**

- 13 is smaller than 23 and appears naturally in classical literature
- Ionascu-Wilson discuss adding 13 to move from modulus 9240 to 120120

**But 23 may be optimal within a specific (k,d) family** due to structural constraints:
- In (k,d) witness frameworks, available moduli are constrained
- Numbers of form 4k+3 or divisors appear naturally
- k=5 gives m_k = 23, which may be more natural than k values giving 13

---

## Pattern Prediction: Quadratic Character Decision Tree

### The Key Principle

> As you refine the modulus by multiplying by a new odd prime ℓ, the resistant set is exactly the set of residue classes that remain **squares modulo ℓ**.

The easy/hard split is predicted by the quadratic character (·/ℓ).

### Mod 11 Split

```
QR(11) = {1, 3, 4, 5, 9}      ← HARD (remain square classes)
QNR(11) = {2, 6, 7, 8, 10}    ← EASY (eligible for congruence identities)
```

Tao exhibited identities eliminating {7, 8, 10} mod 11 for p ≡ 1 (mod 24).
Stubborn: {2, 6} mod 11 (still non-residues but harder for specific identity family).

### Mod 23 Split

```
QR(23) = {1, 2, 3, 4, 6, 8, 9, 12, 13, 16, 18}     ← HARD
QNR(23) = {5, 7, 10, 11, 14, 15, 17, 19, 20, 21, 22}  ← EASY
```

**Prediction**: Mod 23 resolves hard mod 11 ones exactly when (p/23) = -1.

### Exploitable Pattern

> Track a small set of Legendre symbols, not a huge list of congruence classes.

The certificate is naturally a **decision tree over quadratic characters**:
1. First the 5 characters from 840
2. Then (·/11)
3. Then (·/23)
4. etc., until each leaf is "non-square somewhere"

---

## Detailed Subclass Analysis (Mod 11 Refinement)

For each resistant r mod 840, refinement to mod 9240:
```
p ≡ r + 840t (mod 9240), t = 0, 1, ..., 10
Since 840 ≡ 4 (mod 11): p mod 11 ≡ r + 4t
```

### r = 1:
- QNR mod 11 subclasses: {2521, 3361, 4201, 5881, 8401} mod 9240
- Tao-easy (7,8,10 mod 11): {3361, 5881, 6721}
- Hard non-res (2,6 mod 11): {2521, 4201}

### r = 121:
- QNR: {1121, 1961, 3641, 4481, 5321}
- Tao-easy: {1961, 4481, 6161}
- Hard non-res: {1121, 3641}

### r = 169:
- QNR: {1009, 1849, 2689, 4369, 6889}
- Tao-easy: {1849, 4369, 5209}
- Hard non-res: {1009, 2689}

### r = 289:
- QNR: {1289, 2969, 3809, 5489, 8009}
- Tao-easy: {2969, 5489, 6329}
- Hard non-res: {1289, 3809}

### r = 361:
- QNR: {1201, 2041, 2881, 4561, 7081}
- Tao-easy: {2881, 4561, 7081}
- Hard non-res: {1201, 2041}

### r = 529:
- QNR: {3049, 3889, 4729, 6409, 8929}
- Tao-easy: {3889, 6409, 7249}
- Hard non-res: {3049, 4729}

---

## Minimal Certificate Structure

### What the 3 Levels Really Are

**A decision tree on quadratic characters:**

1. **Level 1 (mod 840)**: Eliminate every class NOT in G²
2. **Level 2 (×11)**: Among G², eliminate subclasses with (p/11) = -1
3. **Level 3 (×23)**: Among what remains, eliminate those with (p/23) = -1

This is **exactly the structure forced by Schinzel/Mordell obstruction**.

### Is It Minimal?

- If rules are genuinely modular identities, **some branching is unavoidable**
- You can collapse to one modulus (e.g., 212520) but don't remove complexity
- You still need different witnesses on different sub-classes

### Fundamental Limitation

> A finite, one-shot covering by polynomial modular identities cannot exist in full generality, because some residue class will always be square-like (e.g., 1 is a square modulo every modulus).

---

## Universal Witnesses

If "(k,d) rule" maps fixed parameters → one congruence class → explicit (x,y,z):

- **Yes**: Each leaf class has a universal witness (one (k,d) works for all primes in that leaf)
- **But**: You need multiple (k,d) to cover a union of leaves

---

## Implications for Our Approach

### What This Explains

1. **Why 6 resistant classes**: They are G² ⊆ (ℤ/840ℤ)*
2. **Why K_COMPLETE works**: It provides enough moduli to "break" the square structure
3. **Why D_max grows**: For square-class primes, the witness d must overcome the QR obstruction

### Connection to Our (k,d) Witnesses

Our Type II witnesses have structure:
- m_k = 4k + 3 (always ≡ 3 mod 4)
- Witness condition: d ≡ -x_k (mod m_k)

The m_k values include primes 3, 7, 11, 19, 23, 31, 47, 59, 67, 71, 79, 103, 107, 127, 167.

**Key insight**: These m_k values provide quadratic character tests via different primes, allowing the certificate to "escape" the square-class obstruction through multiple routes.

---

## References

- Ionascu-Wilson: ar5iv.org/pdf/1001.1100
- Tao: terrytao.wordpress.com/2011/07/07/...
- Bradford: math.colgate.edu/~integers/z54/z54.pdf
- López: arxiv.org/pdf/2404.01508
- Wikipedia: Erdős-Straus conjecture
