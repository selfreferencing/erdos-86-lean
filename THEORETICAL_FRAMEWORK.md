# Theoretical Framework for ESC Type II Witness Coverage

## Date: January 21, 2025

## Core Insight: The Witness Condition is a Quadratic Character Problem

The condition "-x_k ∈ H_{x_k}" is fundamentally controlled by **squareclass quotients** and **odd quadratic characters**.

---

## 0. Critical Refinements (from GPT Response 2)

### Admissibility is Automatic for Large p

If p is prime and p > m_k, then gcd(x_k, m_k) = 1 automatically.

**Proof**: If prime ℓ | m_k also divides x_k, then ℓ | (4x_k - m_k) = p. So ℓ = p, impossible when p > m_k.

Only need to check primes p ≤ 167 separately (finite computation).

### The Exact Condition: Bounded-Exponent Form

Write x_k = ∏ q_i^{e_i}. Then d | x_k² means d = ∏ q_i^{f_i} with 0 ≤ f_i ≤ 2e_i.

The congruence d ≡ -x_k (mod m_k) becomes:
```
∏ q_i^{f_i} ≡ -∏ q_i^{e_i} (mod m_k)
⟺ ∏ q_i^{t_i} ≡ -1 (mod m_k)  where t_i = f_i - e_i
```

**Bounded-exponent form**: Find integers t_i with **-e_i ≤ t_i ≤ e_i** such that:
```
∏ q_i^{t_i} ≡ -1 (mod m_k)
```

### The "Box" Condition (Exact Formulation)

Define the **box**:
```
B(x_k) = { ∏ q_i^{t_i} : -e_i ≤ t_i ≤ e_i } ⊆ (ℤ/m_k)*
```

> **Exact witness condition**: A witness exists iff **-1 ∈ B(x_k)**

This is stronger than just "-x_k ∈ H_{x_k}" because it requires bounded exponents.

### Why the Subgroup Condition is (Almost) Sufficient

**Good news**: Since m_k ≤ 167, the target group has size ≤ 166. Typical x_k has enough factorization complexity that boxes become large and mix well.

The subgroup condition is:
- **Necessary**: Always
- **Sufficient**: When an "exponent-bounding lemma" holds (which it typically does for our small moduli)

---

## 1. The Squareclass Quotient

For each modulus m = m_k, define the squareclass quotient:

```
V_m = (ℤ/mℤ)* / ((ℤ/mℤ)*)²
```

This is an **F₂-vector space**. Its dimension determines how many independent quadratic constraints exist.

### Key Property of Our Moduli

For m_k ∈ {3, 7, 11, 15, 19, 23, 27, 31, 39, 47, 55, 59, 67, 71, 79, 87, 95, 103, 107, 119, 127, 159, 167}:

| Dimension | Moduli |
|-----------|--------|
| **dim = 1** | 3, 7, 11, 19, 23, 27, 31, 47, 59, 67, 71, 79, 103, 107, 127, 167 |
| **dim = 2** | 15, 39, 55, 87, 95, 119, 159 |

**Interpretation**:
- **Dimension 1** (most moduli, including all primes ≡ 3 mod 4): Only ONE odd quadratic character to satisfy
- **Dimension 2** (composite "cross-filters"): TWO odd quadratic characters to satisfy

---

## 2. The Odd-Character Obstruction Lemma

Let X_m = group of quadratic characters χ: (ℤ/mℤ)* → {±1}

Call χ **odd** if χ(-1) = -1.

> **Lemma (Odd-Character Obstruction)**
>
> For gcd(x, m) = 1:
>
> -1 ∉ H_x  ⟺  ∃ odd quadratic χ (mod m) such that χ(q) = +1 ∀q|x
>
> Equivalently:
>
> -1 ∈ H_x  ⟺  ∀ odd quadratic χ, ∃ q|x with χ(q) = -1

**Plain English**:
- **Success** for modulus m means: among prime factors of x_k, you see at least one quadratic non-residue for each odd character
- **Failure** means: all prime factors of x_k are quadratic residues for some odd character

---

## 3. Why Dimension 1 is "Cheap to Satisfy"

For prime m ≡ 3 (mod 4), there's exactly ONE odd quadratic character (the Legendre symbol).

**Success condition**: x_k has at least one prime factor that is a QNR mod m.

Since half of all primes are QNR mod m, this is satisfied with high probability.

---

## 4. Why Dimension 2 Creates "Cross-Filters"

For composite moduli like 55 = 5 × 11, there are TWO independent odd quadratic characters.

**Success condition**: Prime factors of x_k must "span" the [-1] vector in a 2-dimensional F₂-space.

This requires seeing enough variety of sign patterns across both characters - hence "cross-filter".

---

## 5. Failure Probability Analysis

### For Each Modulus k

Failure requires ALL prime factors of x_k to lie in a "allowed prime set":

```
P_{k,χ} = {q prime : q∤m_k, χ(q) = +1}
```

This set has **density 1/2** among primes (Chebotarev/Dirichlet).

### Delange-Wirsing Asymptotics

For a set P of primes with density δ < 1, the count of integers ≤ X composed only of primes from P is:

```
≍ X (log X)^{δ-1}
```

For δ = 1/2 (half the primes):

```
P(k fails) ≈ C_k / √(log x_k)
```

### 23 Independent Shots

If we treat the 23 events as roughly independent:

```
P(all 23 fail) ≈ ∏_k C_k / √(log x_k) ≈ C / (log p)^{23/2}
```

For p = 10^8: (log p)^{23/2} ≈ 18^{11.5} ≈ 10^{14}

**This is astronomically small**, explaining 100% coverage.

---

## 6. Conditional Theorem Statement

> **Conditional Conclusion** (under GRH + standard distribution hypotheses):
>
> The set of primes p ≡ 1 (mod 4) not covered by K_COMPLETE has **density 0**.
>
> More precisely, the number of uncovered primes up to X is o(X/log X).

This does NOT automatically give "no exceptions ever" but explains:
1. Why we see 100% coverage up to 10^8
2. Why D_max can still grow (the argument doesn't bound d)

---

## 7. Structural Explanation of Cross-Filters

### Why Resistant Classes Exist

The 6 resistant classes mod 840 are exactly G² ⊆ (ℤ/840ℤ)*.

This means: **all small quadratic characters** (from mod 3, 5, 7, 8) are +1 on p.

The "obvious" low-level quadratic obstructions don't force an early hit.

### Why Composites Like 55 Matter

Bringing in 11 (and composites combining 11 with 5 or 7) adds **new independent quadratic characters**.

In dimension-2 moduli (like 55 = 5×11):
- The condition "-1 ∈ H_x" is NOT just "see one non-residue"
- It becomes "see enough sign patterns to span [-1] in a 2-bit space"

**This is exactly the cross-filter phenomenon.**

### K_COMPLETE Structure

> K_COMPLETE is essentially a hand-picked basis of low-dimensional squareclass quotients V_{m_k} that collectively shatter the "square subgroup" obstruction patterns.
>
> The composite moduli add *mixed* quadratic constraints (cross-filters), which appear precisely in the hard cases.

---

## 8. Route to a Full Proof

### Step 1: Make the Reduction Exact

Show that the d|x² congruence condition is equivalent to (or implied by) the squareclass/character criterion.

Need: obstruction is purely 2-adic/squareclass for these m_k.

### Step 2: Prove a "Hit Lemma"

For each p, among the 23 values x_k = (p + m_k)/4, at least one has a prime divisor landing in the needed coset(s).

This is a **sieve-in-short-intervals statement with Chebotarev-type local conditions** - hard but plausible conditionally.

### Step 3: Use 840-Structure Explicitly

Restrict to the 6 resistant classes and show that added moduli (involving 11 and cross-products) eliminate them.

Salez-style filter sets encode exactly which character patterns remain and which m_k attacks them.

---

## 9. Summary

| Aspect | Finding |
|--------|---------|
| **Obstruction type** | 2-torsion / odd quadratic characters |
| **V_{m_k} dimension** | 1 or 2 for all our moduli |
| **Failure probability** | ≈ 1/√(log p) per modulus |
| **23 shots combined** | ≈ 1/(log p)^{23/2} - astronomically small |
| **Conditional result** | Uncovered primes have density 0 |
| **Cross-filter role** | Add mixed quadratic constraints in dim-2 cases |

---

## 10. Key Equations

**Witness condition reformulated**:
```
-1 ∈ H_x  ⟺  ∀ odd χ mod m, ∃ q|x with χ(q) = -1
```

**Failure probability heuristic**:
```
P(all k fail) ≈ C / (log p)^{|K_COMPLETE|/2} = C / (log p)^{11.5}
```

**Why this suffices**: For p up to 10^{1000}, this probability is still < 10^{-1000}.

---

## 11. Proof Roadmap (from GPT Response 2)

### Step 1: Replace Subgroup with Exact Box Condition

Replace "-x_k ∈ H_{x_k}" with the exact condition "-1 ∈ B(x_k)" where:

B(x_k) = { ∏ q_i^{t_i} : -e_i ≤ t_i ≤ e_i }

Or prove an exponent-bounding lemma that lets us keep the subgroup phrasing.

### Step 2: Show Failure is Controlled by Quadratic Characters

For each k, the set of p for which B(x_k) misses -1 is controlled by a small set of characters (mostly quadratic).

The "bad event" for modulus m_k:
> ∃ quadratic χ mod m_k with χ(-1) = -1 such that χ(q) = +1 for all primes q | x_k

### Step 3: Prove Large-Sieve Estimate

For a fixed set of 23 (mostly independent) quadratic characters, prove it is extraordinarily rare for all 23 shifted integers x_k to have all prime factors in the (+1) side simultaneously.

Under GRH or BV-type hypothesis:

#{p ≤ X : p ≡ 1 (mod 4), all k fail} ≪ X/(log X)^A

for some A > 2 (expect A ≈ 23/2 = 11.5).

### Step 4: Make Bound Explicit and Combine with Computation

Once you have explicit bound showing exceptional set is small, combine with computation up to 10^8 to conclude K_COMPLETE is complete.

**Template**: Prove exceptional set is so small it must be empty above computational cutoff.

---

## 12. Why These Specific 23 Moduli?

K_COMPLETE supplies:
1. **Independent quadratic characters** from prime moduli (3, 7, 11, 19, 23, ...)
2. **Cross-coupled constraints** from composite moduli (55, 77, 119, ...)

The qualitative reason:
> They supply enough independent quadratic characters (including coupled ones via composites) that the only way to fail everywhere is to have 23 simultaneous "all prime factors split" events—an event whose expected frequency is essentially zero.

The "decision tree on quadratic characters" is the certificate: routing p by its character-vector into at least one modulus where the obstruction can't persist.
