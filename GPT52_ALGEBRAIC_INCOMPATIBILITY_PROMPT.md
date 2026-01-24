# Algebraic Incompatibility Prompt

## THE PRECISE QUESTION

For K10 = {5,7,9,11,14,17,19,23,26,29}, prove that the 10 obstruction events cannot occur simultaneously for any Mordell-hard prime.

---

## SETUP

For a Mordell-hard prime p (p ≡ 1,121,169,289,361,529 mod 840):

```
x_k = (p + 4k + 3) / 4
m_k = 4k + 3
```

Key relationship: x_k = x_5 + (k - 5) for all k.

So: x_5, x_7, x_9, x_11, x_14, x_17, x_19, x_23, x_26, x_29 are:
```
x_5, x_5+2, x_5+4, x_5+6, x_5+9, x_5+12, x_5+14, x_5+18, x_5+21, x_5+24
```

---

## THE OBSTRUCTION CONDITIONS

For each k, define:
```
Obs_k := ¬∃d. (d | x_k²) ∧ (d ≤ x_k) ∧ (d ≡ -x_k mod m_k)
```

This happens when:
1. All prime factors of x_k are quadratic residues mod m_k
2. The target -x_k is NOT a quadratic residue mod m_k
3. p is NOT in the d=1 family for this k

---

## THE 10 MODULI

```
m_5 = 23 (prime)
m_7 = 31 (prime)
m_9 = 39 = 3 × 13
m_11 = 47 (prime)
m_14 = 59 (prime)
m_17 = 71 (prime)
m_19 = 79 (prime)
m_23 = 95 = 5 × 19
m_26 = 107 (prime)
m_29 = 119 = 7 × 17
```

Seven are prime; three are composite.

---

## QUADRATIC RESIDUE SUBGROUPS

For prime m: Q_m = {squares in (ℤ/m)×} has index 2.

For m = 39: Q_39 is determined by QR mod 3 and mod 13.
For m = 95: Q_95 is determined by QR mod 5 and mod 19.
For m = 119: Q_119 is determined by QR mod 7 and mod 17.

---

## THE COUPLING

The x_k values are: n, n+2, n+4, n+6, n+9, n+12, n+14, n+18, n+21, n+24
where n = x_5 = (p + 23)/4.

For Obs_k to hold, we need specific QR conditions on the prime factors of x_k.

**Question**: Can consecutive/nearby integers n, n+2, n+4, ... ALL have their prime factors lying in specific subgroups (varying by k)?

---

## ATTACK ANGLES

### Angle 1: Small prime factor analysis
If any x_k has a small prime factor q that is NQR mod m_k, then Obs_k fails.

The 10 consecutive-ish values n, n+2, ..., n+24 span a range of 25.
At least one of them is divisible by 2, 3, 5, 7, 11, 13, etc.

For each small prime q, determine which k have q as NQR mod m_k.
If q | x_k and q is NQR mod m_k, then Obs_k fails.

### Angle 2: The coupled factorizations
The 10 numbers n, n+2, n+4, n+6, n+9, n+12, n+14, n+18, n+21, n+24 cannot all avoid small primes that would break their respective obstructions.

### Angle 3: The d=1 escape
For k, d=1 works when p ≡ 12k+5 (mod 16k+12).
These are 10 congruence conditions mod different moduli.
Perhaps the union of complements (where d=1 fails for all k) is small enough to analyze?

### Angle 4: Direct modular arithmetic
Fix p mod some large M (maybe lcm of relevant moduli).
For each residue class, compute which k are guaranteed to work.
Show every Mordell-hard residue class has at least one working k.

---

## SPECIFIC COMPUTATIONS TO PERFORM

1. For each small prime q ∈ {2,3,5,7,11,13,17,19,23,29,31}, compute which k ∈ K10 have q as NQR mod m_k.

2. For the range x_5 to x_5+24, determine divisibility patterns by small primes.

3. Compute the density of primes p where each individual k fails.

4. Look for k₁, k₂ ∈ K10 such that Obs_{k₁} ∧ Obs_{k₂} is impossible.

---

## DELIVERABLE

Prove: ∀ Mordell-hard prime p, ∃ k ∈ K10, ¬Obs_k.

Equivalently: The conjunction ⋀_{k∈K10} Obs_k is false for all Mordell-hard p.

Provide either:
(A) An algebraic/number-theoretic proof of mutual exclusion, or
(B) A reduction to finite computation that can be verified in Lean via native_decide
