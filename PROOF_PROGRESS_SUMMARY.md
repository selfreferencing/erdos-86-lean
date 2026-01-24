# Erdős-Straus K10 Proof: Progress Summary

**Date:** January 20, 2026 (Updated)
**Original Goal:** Prove `ten_k_cover_exists` - that K₁₀ covers ALL Mordell-hard primes
**Revised Goal:** Prove `k10_covers_hard10` - that K₁₀ covers all Hard10 primes (residual after k=0,1,2)

---

## 0. CRITICAL UPDATE: Theorem Restructured

### Original Claim (FALSE)
> K₁₀ = {5,7,9,11,14,17,19,23,26,29} covers all Mordell-hard primes under Type II.

**STATUS: DISPROVEN** - 18 counterexamples found ≤ 10^7

### Corrected Theorem Structure

**K₁₃ = {0, 1, 2} ∪ K₁₀** covers all Mordell-hard primes:

| Small k | m_k | Coverage |
|---------|-----|----------|
| k=0 | 3 | 41.9% (8,590 primes) |
| k=1 | 7 | 23.3% (4,779 primes) |
| k=2 | 11 | 21.5% (4,419 primes) |
| **K₁₀** | various | **13.3% (2,725 "Hard10" primes)** |

**Hard10 Definition:** Mordell-hard primes NOT covered by k ∈ {0, 1, 2}

**New Main Theorem:** `k10_covers_hard10` - K₁₀ covers all Hard10 primes

---

## 1. The Problem (Revised)

For Hard10 primes (Mordell-hard primes failing k=0,1,2), prove:

```
∃ k ∈ K₁₀, ∃ d | x_k², d ≤ x_k ∧ d ≡ -x_k (mod m_k)
```

Where:
- K₁₀ = {5, 7, 9, 11, 14, 17, 19, 23, 26, 29}
- x_k = (p + 4k + 3) / 4
- m_k = 4k + 3

---

## 2. What We've Proven

### 2.1 Computational Verification ✓
- All 2,725 Hard10 primes p ≤ 10⁷ are covered by K₁₀
- K₁₃ = {0,1,2} ∪ K₁₀ covers ALL 20,513 Mordell-hard primes ≤ 10⁷

### 2.2 The Reciprocity Transformation ✓

**Theorem (Gemini).** For odd prime q | x_k with q ∤ m_k:
```
(q/m_k) = (p/q)
```

**Corollary.** The obstruction at k holds ⟺ all prime factors q of x_k satisfy (p/q) = +1.

### 2.3 The Interaction Framework ✓

**Theorem (GPT2).** Define:
- r = (p + 3)/4, so x_k = r + k
- G_ℓ = {-k mod ℓ : k ∈ K₁₀ and (ℓ/m_k) = -1}

Then: All 10 obstructions hold ⟺ r mod ℓ ∉ G_ℓ for every prime ℓ.

### 2.4 The GCD Lemma ✓

**Lemma.** gcd(x_k, x_j) | (k - j) for k ≠ j.

So primes > 24 can divide at most one x_k.

### 2.5 The Cascade Structure ✓

Empirical distribution of first successful k for Hard10 primes:
- k=5 (m=23): catches **64%**
- k=7 (m=31): catches **21%** of remainder
- k=9 (m=39): catches **8%** of remainder
- k=11 (m=47): catches **4%** of remainder
- Higher k: catches **< 3%** combined

### 2.6 The A·A Framework (GPT3) ✓

**Key Abstraction:** Define A_k = {d mod m_k : d | x_k}

Then:
- Divisors of x_k² have residues **A_k · A_k** = {ab : a,b ∈ A_k}
- Witness exists ⟺ **-x_k ∈ A_k · A_k**

**Saturation Lemma:** |A_k| > |G_k|/2 ⟹ A_k · A_k = G_k ⟹ witness exists

### 2.7 The Complement Trick (GPT3) ✓

For p > 119, gcd(x_k, m_k) = 1.

**Lemma:** If d | x_k² with d ≡ -x_k (mod m_k), then d' = x_k²/d also satisfies d' ≡ -x_k (mod m_k).

**Corollary:** One of {d, d'} is ≤ x_k automatically.

**Consequence:** We can DROP the "d ≤ x_k" condition in proofs and recover it via complement.

### 2.8 The Mod 210 Case Split (GPT4) ✓

**Key Insight:** MordellHard primes have only 6 residue classes for x_5 mod 210:

| p mod 840 | x_5 mod 210 |
|-----------|-------------|
| 1 | 6 |
| 121 | 36 |
| 169 | 48 |
| 289 | 78 |
| 361 | 96 |
| 529 | 138 |

**Proof Strategy:** For each of the 6 cases:
- Either a "breaker" prime (2,3,5,7) divides some x_k where it's NQR
- Or k ∈ {0,1,2} succeeds (contradicting Hard10)

### 2.9 Small-Prime Obstruction Breakers (GPT4) ✓

From QR analysis data:
- **3 | x_k for k ∈ {7, 19}** → obstruction fails (3 is NQR mod 31, 79)
- **5 | x_14** → obstruction fails (5 is NQR mod 59)
- **7 | x_5** → obstruction fails (7 is NQR mod 23)

These are the "interaction lemmas" that kill obstructions when small primes divide x_k.

### 2.10 The D_m(x) ∩ (-D_m(x)) Reformulation (GPT6) ✓

**Lemma B:** Let D_m(x) = {d mod m : d | x}. Then:

> Witness exists ⟺ **D_m(x) ∩ (-D_m(x)) ≠ ∅**

Equivalently: find two divisors a, b of x with **a ≡ -b (mod m)**.

This is cleaner than searching divisors of x² directly.

### 2.11 Why 3 | x_5 Always (GPT6) ✓

For Mordell-hard primes, p ≡ 1 (mod 3). Since 23 ≡ 2 (mod 3):
- p + 23 ≡ 1 + 2 ≡ 0 (mod 3)
- Hence **3 | x_5 always** for Hard10 primes

And critically: **ord_23(3) = 11** (generates full QR subgroup).

This explains why k=5 catches 64%: the forced factor 3 creates a dense divisor-residue footprint mod 23.

### 2.12 Finite Obstruction Lemma Architecture (GPT6) ✓

**Goal:** For each k ∈ K10, compute finite list B_k of "bad residue multisets" such that:
- k fails for p ⟺ prime residue multiset of x_k lies in B_k

**Proof Template:**
1. Compute minimal obstruction patterns for each m_k (finite: m_k ≤ 119)
2. Use gcd-divides-difference to isolate overlaps to primes ≤ 24
3. Impose Hard10 constraints from k=0,1,2 failures
4. Exhaust finite remaining cases to prove incompatibility

This reduces the theorem to a **finite, mechanizable check** in Lean.

### 2.13 Exact Small-k Characterizations (GPT2) ✓

**k=0 (m=3) - EXACT:**
- For Mordell-hard p, x_0 ≡ 1 (mod 3), so target is 2 (mod 3)
- **k=0 works ⟺ x_0 has a prime factor q ≡ 2 (mod 3)**
- **k=0 fails ⟺ all prime factors of x_0 are ≡ 1 (mod 3)**

**k=1 (m=7) - EXACT:**
- For Mordell-hard p, x_1 ∈ {1,2,4} (mod 7) - always QR
- Target -x_1 is always NQR mod 7
- **k=1 works ⟺ x_1 has a prime factor q ≡ 3,5,6 (mod 7)** (NQR)
- **k=1 fails ⟺ all prime factors of x_1 are ≡ 1,2,4 (mod 7)** (QR)

**k=2 (m=11) - PARTIAL:**
- For Mordell-hard p, **3 | x_2 always**
- Unconditional success cases:
  - p ≡ 7 (mod 11): d=1 works
  - p ≡ 10 (mod 11): d=3 works
  - p ≡ 8 (mod 11): d=9 works
- Higher 3-power cases:
  - p ≡ 2 (mod 11) + v_3(x_2) ≥ 2: d=27 works
  - p ≡ 6 (mod 11) + v_3(x_2) ≥ 2: d=81 works
- Plus QR obstruction + narrow residue-set patterns

**Hard10 as Conjunction:**
- ¬TypeII(p,0): all q | x_0 have q ≡ 1 (mod 3)
- ¬TypeII(p,1): all q | x_1 have q ≡ 1,2,4 (mod 7)
- ¬TypeII(p,2): failure patterns above

### 2.14 Strategy A: Finite Cascade Certificate Proof (GPT1) ✓

**The Key Insight:** Separate small-prime coupling from large-prime tails.

**Coupling Primes:** P_coup = {2,3,5,7,11,13,17,19,23,29}
- By GCD lemma, primes > 29 divide **at most one** x_k among K10
- So large primes are disjoint; only small primes couple different k's

**The Proof Structure:**

1. **Local State:** For each k, record v_ℓ(x_k) for ℓ ∈ P_coup (capped at 3-4)

2. **Compute R_k:** Residues achievable by small-prime divisors d₀ | s_k² with d₀ ≤ x_k

3. **Compute Good_k:** Residue classes in (Z/m_k)* where a large prime factor q > 29 with q mod m_k ∈ Good_k guarantees a witness d = q^e · d₀

4. **Lemma 4 (Smooth-gap bound):** Beyond explicit R₀, not all {x_k : k ∈ K10} are 29-smooth

5. **Finite Coverage:** For every local state consistent with Hard10:
   - Either some k already has witness from small primes alone
   - Or at least one Good_k ≠ ∅

6. **Combine:** For r ≥ R₀, some t_k ≠ 1 (not 29-smooth), forcing q > 29 | t_k, which must land in some Good_k

**Result:** Purely finite+elementary proof reducing to:
- Finite computation on valuations at primes ≤ 29
- Explicit smooth-gap bound (finite verification)
- One-time finite state space exhaustion

---

## 3. GENUS APPROACH: DEAD ☠️

### The Question
Does Bradford's obstruction O_k (all prime factors split in Q(√-m_k)) force x_k into the principal genus?

### The Answer: NO

**GPT2 Proof:** "All primes split" does NOT imply principal genus.

**GPT1 Counterexample (k=9, m=39, D=-156):**
- n = 5 satisfies (5/39) = +1 (all-split)
- Class group of D=-156 has 4 elements: {(1,0,39), (3,0,13), (5,2,8), (5,-2,8)}
- Principal genus = {(1,0,39), (3,0,13)} (size 2)
- 5 is NOT represented by x² + 39y² or 3x² + 13y²
- 5 IS represented by (5,2,8) - a non-principal genus form

**Additional Counterexample (k=5, m=23):**
- (3/23) = +1, so 3 is "split"
- But 3 ≠ x² + 23y² (no solution)

**Structural Reason:** Splitting in Q(√-m_k) does not control genus characters. The genus field is a larger 2-extension.

### Consequence
- Strategy A (Faltings/fiber product) is DEAD
- Cannot use Diophantine rigidity through genus

---

## 4. Remaining Viable Strategies

### 4.1 Strategy B: Covering Congruences
Find modulus M such that p mod M determines which k ∈ K₁₀ works.

**Status:** GPT5 working on this

### 4.2 Strategy C: Asymptotic Bound + Finite Verification
Find explicit N such that for p > N, divisor density guarantees K₁₀ witness.

**Status:** GPT3, GPT4 working on this

### 4.3 Strategy D: Cascade Analysis
Prove the 64/21/8/4/3 cascade structure algebraically shows K₁₀ must cover Hard10.

**Status:** GPT6 working on this

### 4.4 Strategy E: G_ℓ Direct Coverage
Show the residue avoidance system G_ℓ cannot be avoided by Hard10 primes.

**Status:** Open

---

## 5. AI Instance Status

| Instance | Prompt | Status | Finding |
|----------|--------|--------|---------|
| GPT1 | Hard10 Coverage | **DONE** | Strategy A: finite cascade certificate proof |
| GPT2 | Small-k Characterization | **DONE** | Exact iff lemmas for k=0,1,2 |
| GPT3 | Asymptotic Bound | **DONE** | A·A framework + complement trick |
| GPT4 | Computational Bound | **DONE** | 6 Lean lemmas + mod 210 case split |
| GPT5 | Covering Congruences | **DONE** | ⚠️ WRONG DEFINITION - used d|x not d|x² |
| GPT6 | Cascade Analysis | **DONE** | Finite obstruction lemma + why 3|x_5 matters |

---

## 6. Files

### Lean Files
| File | Purpose |
|------|---------|
| `CoveringRestructured.lean` | Restructured theorem with Hard10 definition |

### Prompts Created
| File | Target |
|------|--------|
| `GPT_PROMPT_HARD10_COVERAGE.md` | Main theorem proof |
| `GPT_PROMPT_SMALL_K_CHARACTERIZATION.md` | When k=0,1,2 work/fail |
| `GPT_PROMPT_ASYMPTOTIC_BOUND.md` | Explicit N for large-p argument |
| `GPT_PROMPT_COMPUTATIONAL_BOUND.md` | Hardy-Ramanujan + Artin bounds |
| `GPT_PROMPT_COVERING_CONGRUENCES.md` | CRT-based covering system |
| `GPT_PROMPT_CASCADE_ANALYSIS.md` | Why 64/21/8/4/3 pattern exists |
| `GPT_PROMPT_SIEVE_BOUND.md` | Sieve-theoretic bound |
| `GPT_PROMPT_COPRIMALITY_EXPLOITATION.md` | Large primes divide ≤1 x_k |
| `GPT_PROMPT_NEW_INVARIANT.md` | Algebraic invariant beyond genus |

---

## 7. Current Status

```
PROVEN:
  ├── Reciprocity: (q/m_k) = (p/q) ✓
  ├── Obstruction ⟺ all factors QR ✓
  ├── G_ℓ framework (interaction) ✓
  ├── GCD lemma: primes > 24 divide ≤ 1 x_k ✓
  ├── K13 = {0,1,2} ∪ K10 covers all Mordell-hard ≤ 10^7 ✓
  └── K10 covers all Hard10 ≤ 10^7 ✓

DEAD:
  └── Genus approach ☠️ (GPT1, GPT2 independently confirmed)

UNPROVEN:
  └── k10_covers_hard10 for ALL Hard10 primes (not just ≤ 10^7)

WAITING ON:
  └── GPT2-6 responses on alternative strategies
```

---

## 8. What Success Looks Like

A complete proof requires ONE of:

1. **Covering Congruences:** Find M such that Hard10 p mod M determines k ∈ K₁₀

2. **Asymptotic + Finite:** Prove K₁₀ works for p > N, verify computationally for p ≤ N ≤ 10^7

3. **Cascade Proof:** Show the 64/21/8/4/3 pattern algebraically guarantees coverage

4. **G_ℓ Direct:** Show Hard10 primes cannot avoid all G_ℓ sets

---

## 9. GPT Prompt Fleet (Ready to Deploy)

### Lean Code Generation (8 prompts)
| # | File | Target Lemma |
|---|------|--------------|
| 1 | `GPT_LEAN_PROMPT_1_GCD_COUPLING.md` | gcd(r+a, r+b) \| \|a-b\| |
| 2 | `GPT_LEAN_PROMPT_2_COMPLEMENT_TRICK.md` | complement_same_residue, witness_exists_small |
| 3 | `GPT_LEAN_PROMPT_3_K0_CHARACTERIZATION.md` | k=0 works ⟺ factor ≡ 2 (mod 3) |
| 4 | `GPT_LEAN_PROMPT_4_K1_CHARACTERIZATION.md` | k=1 works ⟺ NQR factor mod 7 |
| 5 | `GPT_LEAN_PROMPT_5_K2_CHARACTERIZATION.md` | k=2 unconditional cases + v_3 |
| 6 | `GPT_LEAN_PROMPT_6_SMALL_PRIME_BREAKERS.md` | 3\|x_7, 3\|x_19, 5\|x_14, 7\|x_5 |
| 7 | `GPT_LEAN_PROMPT_7_AA_FRAMEWORK.md` | A·A framework + saturation lemma |
| 8 | `GPT_LEAN_PROMPT_8_MOD210_SETUP.md` | Mod 210 case split structure |

### Computation Prompts (2 prompts)
| # | File | Output |
|---|------|--------|
| 9 | `GPT_COMPUTE_PROMPT_9_SMOOTH_GAP.md` | R₀ smooth-gap bound |
| 10 | `GPT_COMPUTE_PROMPT_10_OBSTRUCTION_PATTERNS.md` | B_k patterns for each k ∈ K10 |

### Analysis Prompts (4 prompts)
| # | File | Goal |
|---|------|------|
| 11 | `GPT_PROMPT_CASCADE_ANALYSIS.md` | Why k=5 catches 64%, orthogonality |
| 12 | `GPT_PROMPT_COMPUTATIONAL_BOUND.md` | Explicit N for asymptotic argument |
| 13 | `GPT_PROMPT_NEW_INVARIANT.md` | Algebraic invariant beyond "all split" |
| 14 | `GPT_PROMPT_COVERING_CONGRUENCES.md` | Finite covering congruence system |

### Main Theorem Assembly (1 prompt)
| # | File | Goal |
|---|------|------|
| 15 | `GPT_LEAN_PROMPT_15_MAIN_THEOREM_ASSEMBLY.md` | Combine all lemmas into k10_covers_hard10 |

**TOTAL: 15 prompts ready for GPT 5.2 Pro Extended deployment**

---

## 10. Next Steps

1. **Deploy prompts 1-8** to GPT instances for Lean code generation
2. **Deploy prompts 9-10** for computational verification
3. **Deploy prompts 11-14** for mathematical analysis (if not already done)
4. **Collect Lean outputs** and verify through Aristotle
5. **Assemble final proof** using prompt 15

**The theorem is k10_covers_hard10, NOT the original ten_k_cover_exists.**

---

## 11. Key Lessons Learned

1. **Original theorem was FALSE** - K₁₀ alone fails for 18 Mordell-hard primes
2. **Small k is crucial** - k ∈ {0,1,2} handles 86.7% of cases
3. **Genus approach is DEAD** - "all primes split" ≠ principal genus
4. **Type I vs Type II matters** - certificate database uses both
5. **Restructuring was necessary** - Hard10 definition is the correct scope

**WE DO NOT STOP UNTIL `k10_covers_hard10` IS PROVED.**
