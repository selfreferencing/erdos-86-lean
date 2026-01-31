# APPROACH 48: Modular Covering for Zero-Forcing

## Context

We are seeking an **analytic proof** of the Erdős 86 Conjecture: 2^86 is the last power of 2 with no zero digit.

**The zero-forcing gap:** We've proved |P_m| ≤ 4 (at most 4 prefixes appear). To complete the proof, we need: for m ≥ 36, all appearing prefixes contain a zero.

**This prompt:** Explore whether modular arithmetic / covering arguments can force zeros.

---

## The Modular Structure

### Trailing digits are periodic

The last k digits of 2^n are determined by 2^n mod 10^k.

**Key facts:**
- 2^n mod 2^k: the last k binary digits, period 1 after n ≥ k
- 2^n mod 5^k: period 4·5^{k-1} (since ord_5(2) = 4 and lifting)

By CRT, 2^n mod 10^k has period lcm(1, 4·5^{k-1}) = 4·5^{k-1} for n ≥ k.

**Periods:**
| k | Period of 2^n mod 10^k | # residues to check |
|---|------------------------|---------------------|
| 1 | 4 | 4 |
| 2 | 20 | 20 |
| 3 | 100 | 100 |
| 4 | 500 | 500 |
| 5 | 2500 | 2500 |

### The last k digits cycle

For k = 4, the last 4 digits of 2^n cycle through 500 values.

**Example cycle start:**
- 2^0 mod 10000 = 0001
- 2^1 mod 10000 = 0002
- 2^4 mod 10000 = 0016
- 2^10 mod 10000 = 1024
- ...

---

## Questions

### Q1: Census of "zeroless" residues mod 10^k

For each k, how many of the 4·5^{k-1} residues 2^n mod 10^k are zeroless (no zero digit)?

| k | Period | Zeroless count | Fraction |
|---|--------|----------------|----------|
| 1 | 4 | 4 (2,4,8,6) | 100% |
| 2 | 20 | ? | ? |
| 3 | 100 | ? | ? |
| 4 | 500 | ? | ? |

**Expected:** The fraction should decay roughly as 0.9^k (if digits were independent).

### Q2: Census of "safe" residues mod 10^k

Define "safe" = zeroless AND no unprotected 5 (no 51, 52, 53, 54 substring).

For each k, how many residues are safe?

### Q3: Can we cover all n ≥ N₀ with "unsafe" residue classes?

**Goal:** Find moduli m₁, ..., m_r and residue classes a₁, ..., a_r such that:
1. Every n ≥ N₀ lies in some class n ≡ a_i (mod m_i)
2. For each class, 2^{a_i} mod 10^{k_i} contains a zero or unprotected 5

This is a **covering congruence** approach.

### Q4: The "lifted zeros" phenomenon

If 2^n mod 10^k contains a zero, does 2^n mod 10^{k+1} also contain a zero?

Not necessarily in the SAME position, but: once a zero appears in trailing digits, does it persist?

**Observation:** 2^10 = 1024 has a zero. For all n ≥ 10, does 2^n contain a zero?

NO: 2^13 = 8192, 2^14 = 16384, etc. are zeroless.

So zeros in trailing digits don't guarantee zeros in the full number.

### Q5: Combining leading and trailing constraints

**Leading digits:** Determined by {n·θ} mod 1, where θ = log₁₀(2).
**Trailing digits:** Determined by 2^n mod 10^k, periodic with period 4·5^{k-1}.

These are essentially INDEPENDENT because:
- Leading digits depend on the irrational rotation n·θ mod 1
- Trailing digits depend on the rational residue n mod (4·5^{k-1})

**Key insight:** The probability that BOTH leading m digits AND trailing k digits are zeroless is roughly:
```
Pr(leading m zeroless) × Pr(trailing k zeroless) ≈ 0.9^m × (zeroless fraction for k)
```

### Q6: Joint constraint for m = 36

For m = 36, we need the first 36 digits to be zeroless.

The first 36 digits include:
- Some leading digits (determined by {n·θ})
- Some trailing digits (determined by 2^n mod 10^k for various k)

Actually, for 2^n with ~0.301n digits:
- n = 117: 2^117 has 36 digits, so ALL 36 are "leading" (no trailing overlap)
- n = 120: 2^120 has 37 digits, first 36 includes positions 2-37 (not the unit digit)

**Observation:** For small n (where digit count ≈ prefix length m), there's significant overlap between leading and trailing constraints.

### Q7: The "suffix forces zero" approach

**Claim:** There exists k such that for all n in a full period of 2^n mod 10^k, either:
1. The last k digits contain a zero, OR
2. The last k digits contain an unprotected 5

If true, then for ALL n, 2^n or 2^{n+1} contains a zero.

**Question:** What's the smallest such k? Can we prove it exists?

### Q8: Explicit computation for k = 4

For n = 0, 1, ..., 499, compute:
1. 2^n mod 10000
2. Does it contain a zero?
3. Does it contain 51, 52, 53, or 54?
4. Is it "safe" (neither)?

**Goal:** If very few residues are safe, we can argue probabilistically that the orbit can't stay safe for long.

### Q9: The covering number

Define: κ(k) = min number of residue classes mod 4·5^{k-1} needed to cover all "safe" residues.

If κ(k) is small (say, O(1) independent of k), then:
- Safe residues form a sparse set
- The orbit 2^n can only stay safe by hitting this sparse set repeatedly
- Probabilistic/ergodic arguments might show this is impossible

### Q10: Connection to the 5-adic lifting tree

From APPROACH 33: The 5-adic lifting tree has survival ratio λ_k ≈ 0.9 per level.

**Key connection:** The "survival" in the 5-adic tree corresponds to:
- Last k digits being zeroless (not exactly, but related)

The tree expands as 4.5^k, so there are many surviving residues. But most of these might be "unsafe" (contain unprotected 5).

**Question:** What's the survival ratio for "safe" residues (zeroless AND no unprotected 5)?

---

## Desired Output

1. Census of zeroless and safe residues mod 10^k for k = 1, 2, 3, 4, 5
2. Analysis of whether a covering argument can force zeros
3. Computation of the "safe survival ratio" in the modular setting
4. Assessment of whether modular constraints alone can prove zero-forcing
5. If not, what additional input from leading-digit / Diophantine side is needed

---

## Computational Hints

To compute the census:
```python
def is_zeroless(n):
    return '0' not in str(n)

def has_unprotected_5(n):
    s = str(n)
    for i in range(len(s) - 1):
        if s[i] == '5' and s[i+1] in '1234':
            return True
    return False

def is_safe(n):
    return is_zeroless(n) and not has_unprotected_5(n)

# For k digits
def census(k):
    period = 4 * (5 ** (k - 1))
    zeroless = 0
    safe = 0
    for n in range(period):
        val = pow(2, n, 10**k)
        if is_zeroless(val):
            zeroless += 1
            if is_safe(val):
                safe += 1
    return zeroless, safe, period
```
