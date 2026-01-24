# Enhanced Prompt for GPT-5.2 Pro Extended / Gemini DeepThink

## PROBLEM STATEMENT

Prove that K10 = {5,7,9,11,14,17,19,23,26,29} covers ALL Mordell-hard primes.

**This is a FULL PROOF requirement. Not finite verification. Not asymptotic bounds. FULL COVERAGE.**

---

## PRECISE DEFINITIONS (from Lean formalization)

### Mordell-hard primes
```
MordellHard p := p ≡ 1, 121, 169, 289, 361, or 529 (mod 840)
```
Equivalently: p ≡ 1 (mod 4), p ≡ 1 (mod 3), p ≡ 1 (mod 5), p ≡ 1 (mod 7).

### Bradford parameters
For each k ∈ K10:
```
m_k := 4k + 3
x_k(p) := (p + m_k) / 4 = (p + 4k + 3) / 4
```

The m_k values are: {23, 31, 39, 47, 59, 71, 79, 95, 107, 119}

### Witness condition (QRSufficient)
```lean
def QRSufficient (k p : ℕ) : Prop :=
  ∃ d : ℕ, d ∣ (xK p k)^2 ∧ d ≤ xK p k ∧ (xK p k + d) ≡ 0 (mod mK k)
```
Equivalently: ∃ d | x², d ≤ x, d ≡ -x (mod m)

### Alternative sufficient condition (d=1 family)
```lean
def d1Sufficient (k p : ℕ) : Prop := p % (16*k + 12) = (12*k + 5)
```
When this holds, d=1 works as a witness.

### The theorem to prove
```lean
theorem ten_k_cover_exists (p : ℕ) (hp : Nat.Prime p) (hMH : MordellHard p) :
    ∃ k ∈ K10, kSufficient k p := by
  sorry
```
where `kSufficient k p := d1Sufficient k p ∨ QRSufficient k p`

---

## KNOWN OBSTRUCTIONS (why this is hard)

### Obstruction 1: Individual k-values have genuine failures
For k=8 (m=35=5×7), define the obstruction:
```
AllQR_k(p) := ∀ prime q | x_k, (q/5) and (q/7) are both +1 or both -1
TargetNQR_k(p) := -x_k is not a quadratic residue mod 35
```
When both hold, no divisor d | x² can satisfy d ≡ -x (mod 35).

**Critical fact**: These obstructions persist to arbitrarily large primes.
Example: p = 61,757,089 fails for k=8 alone.

### Obstruction 2: The x_k values are coupled
```
x_k = x_5 + (k - 5) for all k
```
So x_5, x_7, x_9, ... differ by fixed small integers.
The prime factorizations of consecutive x_k values are NOT independent.

### Obstruction 3: Subgroup traps
For each m_k, the quadratic residues form a subgroup Q ⊂ (ℤ/m_k)×.
If all prime factors of x lie in Q, then all divisors of x² also lie in Q.
If -x ∉ Q, no witness exists.

### Why naive approaches fail
1. **Chebotarev density**: Cannot assume QR conditions are independent across different k
2. **Divisor counting**: ω(x) or τ(x²) bounds don't guarantee witnesses
3. **Single-k asymptotics**: Each individual k fails infinitely often

---

## KEY STRUCTURAL INSIGHT

The obstructions across K10 are NOT independent, but they ARE mutually exclusive.

The x_k = x_5 + (k-5) relationship means:
- Changing k by 1 changes x by 1
- Prime factorizations are coupled
- Obstruction conditions interact

**The goal**: Prove that for any Mordell-hard prime p, the 10 obstruction conditions CANNOT all hold simultaneously.

---

## STRATEGY DIRECTIONS TO EXPLORE

### Direction A: d=1 covering analysis
The d1Sufficient conditions are:
```
k=5:  p ≡ 65 (mod 92)
k=7:  p ≡ 89 (mod 124)
k=9:  p ≡ 113 (mod 156)
k=11: p ≡ 137 (mod 188)
k=14: p ≡ 173 (mod 236)
k=17: p ≡ 209 (mod 284)
k=19: p ≡ 233 (mod 316)
k=23: p ≡ 281 (mod 380)
k=26: p ≡ 317 (mod 428)
k=29: p ≡ 353 (mod 476)
```

Question: Do these 10 congruence classes, together with the Mordell-hard constraint, cover enough residue classes to reduce the problem to a finite check?

### Direction B: QR obstruction incompatibility
For each k, define:
```
Obs_k(p) := (AllQR_k(p) ∧ TargetNQR_k(p)) ∧ ¬d1Sufficient(k,p)
```

Question: Can Obs_5 ∧ Obs_7 ∧ ... ∧ Obs_29 ever hold for a Mordell-hard prime?

The m_k values share factors:
- m_9 = 39 = 3×13
- m_23 = 95 = 5×19
- m_29 = 119 = 7×17

Perhaps QR constraints mod different m_k conflict through shared prime factors?

### Direction C: CRT constraint analysis
The moduli for d1Sufficient are:
{92, 124, 156, 188, 236, 284, 316, 380, 428, 476}

Their LCM is large. Combined with Mordell-hard constraint (mod 840), perhaps simultaneous non-d1 + all-obstruction is impossible?

### Direction D: The saturation lemma route
Lemma: If A = {a mod m : a | x} satisfies |A| > |G|/2 where G = (ℤ/m)×, then A·A = G, so every target is reachable.

For which k and x does |A| > |G|/2 hold?
Can we guarantee at least one k achieves saturation?

---

## YOUR TASK

1. **Characterize precisely** what property of p would force ALL k ∈ K10 to fail
2. **Prove** no Mordell-hard prime has this property
3. **Focus on INTERACTIONS** between different k-obstructions (single-k analysis fails)
4. **Provide explicit lemmas** that can be formalized in Lean 4

---

## DELIVERABLES

Provide a complete proof strategy consisting of:

1. **Main theorem statement** in mathematical notation
2. **Key lemmas** with precise hypotheses
3. **Proof sketch** for each lemma showing the key step
4. **Identification of any remaining finite computation** that can be verified by native_decide

The strategy must prove FULL COVERAGE for all Mordell-hard primes, not asymptotic or finite bounds.

---

## VERIFICATION DATA

Computational verification exists for all 20,513 Mordell-hard primes up to 10^7.
Each prime has a certificate (p, k, x, y, z, d) stored in CoveringData.lean.
The certificates verify via native_decide.

This confirms the conjecture is TRUE. The task is to prove WHY it's true for ALL primes.
