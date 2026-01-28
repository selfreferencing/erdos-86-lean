# Experiment 11: Parity Balance of the Survivor Set

## Date: January 27, 2026

---

## 1. Summary

Experiment 11 tested the central prediction of the C-series analysis: that the survivor set at each digit level splits between even-type and odd-type fibers, and that the identity Z_{m+1} = 4*E_m + 5*O_m holds.

**The experiment discovered and corrected a mathematical error in the C-series classification, then confirmed the corrected framework completely through m=12.**

Key results with corrected classification:
- E/Z converges to 1/2 with geometric rate theta ~ 0.29
- Z_{m+1} = 4*E_m + 5*O_m verified exactly for all m=1..11
- S_m = 0.9000 to 8 decimal places at m=12
- Even-type parents split children exactly 50/50 (proved, not just observed)

---

## 2. The Bug: Wrong Parity Classification

### What the C-series assumed

All 6 GPT responses classified a level-m survivor with 5-adic parameter u = x/2^m as:
- Even-type if 2u < 5^m (i.e., u < 5^m/2)
- Odd-type if 2u >= 5^m

### What the first run found

With this classification:
- E/Z locked at exactly 4/9 (not 1/2)
- The identity Z_{m+1} = 4*E_m + 5*O_m failed at every level m >= 2
- |E/Z - 1/2| = 0.0556 = 1/18 with no decay

### The mathematical error

The C-series stated: "each survivor u_0 at level m-1 has 5 lifts u = u_0 + a*5^{m-1}." This lift formula is incorrect. The correct relation between parent parameter u_0 (level m-1) and child parameter u (level m) is:

2u = u_0 (mod 5^{m-1})

not u = u_0 (mod 5^{m-1}). The factor of 2 arises because x = 2^m * u at level m while x = 2^{m-1} * u_0 at level m-1.

### The correct classification

The 5 lifts of a level-m survivor to level m+1 depend on the base lift parameter v_0, where 2*v_0 = u (mod 5^m):

- If u is **even**: v_0 = u/2 < 5^m/2. Lift digits: {0,2,4,6,8}. Four survive (digit 0 kills one).
- If u is **odd**: v_0 = (u+5^m)/2 >= 5^m/2. Lift digits: {1,3,5,7,9}. All five survive.

The correct classification is **u even vs u odd**. Equivalently: even-type iff u * 2^{-1} mod 5^m < 5^m/2.

---

## 3. Corrected Results (m=1..12)

### 3.1 Core Data

| m | Z_m | E_m | O_m | E/Z | |E/Z - 1/2| | S(m+1) |
|---|-----|-----|-----|-----|------------|--------|
| 1 | 4 | 2 | 2 | 0.500000 | 0 | 0.9000 |
| 2 | 18 | 9 | 9 | 0.500000 | 0 | 0.9000 |
| 3 | 81 | 41 | 40 | 0.506173 | 6.17e-03 | 0.8988 |
| 4 | 364 | 182 | 182 | 0.500000 | 0 | 0.9000 |
| 5 | 1,638 | 819 | 819 | 0.500000 | 0 | 0.9000 |
| 6 | 7,371 | 3,685 | 3,686 | 0.499932 | 6.78e-05 | 0.9000 |
| 7 | 33,170 | 16,582 | 16,588 | 0.499910 | 9.04e-05 | 0.9000 |
| 8 | 149,268 | 74,639 | 74,629 | 0.500033 | 3.35e-05 | 0.9000 |
| 9 | 671,701 | 335,852 | 335,849 | 0.500002 | 2.23e-06 | 0.9000 |
| 10 | 3,022,653 | 1,511,320 | 1,511,333 | 0.499998 | 2.15e-06 | 0.9000 |
| 11 | 13,601,945 | 6,800,982 | 6,800,963 | 0.500001 | 6.98e-07 | 0.9000 |
| 12 | 61,208,743 | 30,604,369 | 30,604,374 | 0.500000 | 4.08e-08 | 0.9000 |

### 3.2 Identity Verification

Z_{m+1} = 4*E_m + 5*O_m: **ALL VERIFIED** for m=1..11.

S(formula) = S(direct) to machine precision at every level. Zero discrepancies.

### 3.3 Convergence Rate

Fitted decay: |E/Z - 1/2| ~ 0.26 * (0.29)^m, with **theta ~ 0.29 < 1 (CONVERGES)**.

| m | |E/Z - 1/2| | log2|bias| |
|---|-----------|-----------|
| 3 | 6.17e-03 | -7.34 |
| 6 | 6.78e-05 | -13.85 |
| 8 | 3.35e-05 | -14.87 |
| 9 | 2.23e-06 | -18.77 |
| 10 | 2.15e-06 | -18.83 |
| 11 | 6.98e-07 | -20.45 |
| 12 | 4.08e-08 | -24.55 |

Note: m=1,2,4,5 have E/Z = 1/2 exactly (zero bias).

### 3.4 Parity Imbalance

E - O sequence: [0, 0, +1, 0, 0, -1, -6, +10, +3, -13, +19, -5]

The imbalance oscillates in sign, stays tiny (|E-O| <= 19 even at m=12 where Z = 61M), and |E-O|/Z < 10^{-6} for m >= 9.

Compare with the wrong classification: E-O grew as ~4.5^m, reaching -335,849 at m=10.

---

## 4. Structural Findings

### 4.1 Even parents split exactly 50/50 (THEOREM)

For an even-type parent (u even) at level m, the 4 surviving lifts have parameters v_0 + a*5^m for a in {1,2,3,4} (a=0 is killed by digit 0). Since v_0 = u/2 and 5^m is odd:
- a=1: v_0 + 5^m (parity flipped from v_0)
- a=2: v_0 + 2*5^m (same parity as v_0)
- a=3: v_0 + 3*5^m (flipped)
- a=4: v_0 + 4*5^m (same)

Exactly 2 children are even-type, 2 are odd-type, regardless of v_0's parity. This is a theorem, verified computationally: even parents show exactly 0.5000 transition probability at every level m=2..8.

### 4.2 Odd parents split approximately 50/50

For an odd-type parent (u odd), all 5 lifts survive with v = v_0 + a*5^m for a=0,...,4. The split is 3:2 or 2:3 depending on v_0's parity:
- v_0 even: 3 even children (a=0,2,4), 2 odd children (a=1,3)
- v_0 odd: 2 even children, 3 odd children

The split averages to 5/2 : 5/2 when v_0's parity is balanced, which it is by the same parity-balance mechanism at the previous level. Self-correcting dynamics.

### 4.3 Transition matrix interpretation

The parity-balance dynamics can be modeled as:
- E_{m+1} = 2*E_m + (5/2)*O_m + perturbation
- O_{m+1} = 2*E_m + (5/2)*O_m + perturbation
- Z_{m+1} = 4*E_m + 5*O_m (exact)

The perturbation is O(1) (bounded, oscillating). The dominant dynamics push E/Z toward 1/2 at each step. This is inherently self-correcting: even if the system starts with E != O, the even-parent 50/50 split stabilizes the ratio.

### 4.4 Why 4/9 with the wrong classification

The wrong classification (u < 5^m/2 vs u >= 5^m/2) is a "half-space" split that does not align with the fiber structure. Among survivors, the fraction with u < 5^m/2 converges to 4/9 because of the specific distribution of survivors' leading digits. The digit d_m = floor(2u/5^{m-1}) mod 10 is uniform on {1,...,9}, and the condition u < 5^m/2 corresponds roughly to d_m in {1,...,4}, giving probability 4/9.

---

## 5. Implications for Density Zero

### The argument is now computationally complete

With the corrected classification:
1. Z_{m+1} = 4*E_m + 5*O_m (proved, verified exactly)
2. E/Z -> 1/2 with theta ~ 0.29 (verified to m=12)
3. Therefore Z_{m+1}/Z_m -> 4*(1/2) + 5*(1/2) = 4.5
4. Z_m grows as 4.5^m while the orbit period grows as 5^m
5. Survivor density = Z_m/(4*5^{m-1}) ~ (4.5/5)^m = (0.9)^m -> 0

### What remains for a proof

The weak parity-balance lemma (E/Z >= delta > 0) suffices. Even delta = 0.01 gives density zero. The data shows delta >= 0.49.

Three routes to proving the lemma:

1. **Spectral gap of the parity-augmented transfer operator** (Noda's framework): Show the projection onto the parity character has spectral radius < Perron eigenvalue. The structural 50/50 split from even parents already gives half the spectral gap.

2. **Self-correction argument**: The even-parent 50/50 split is proved. If one could show that odd parents don't systematically favor one parity (which follows from secondary parity balance), the lemma follows.

3. **Probabilistic argument**: The parity of u = x/2^m depends on the (m+1)-th binary digit of x. For a random-looking orbit element, this bit is approximately unbiased. Making "random-looking" precise would suffice.

### Corrected provability hierarchy

| Statement | Status |
|-----------|--------|
| Within-parity digit uniformity | **Proved** |
| Parity-fiber formula Z_{m+1} = 4E_m + 5O_m | **Proved** (arithmetic identity) |
| Even parents split children exactly 50/50 | **Proved** (5^m is odd) |
| S_m = 1 - E_m/(5*Z_m) | **Proved** (arithmetic identity) |
| E/Z >= delta > 0 (weak parity-balance) | **Verified to m=12, theta ~ 0.29** |
| E/Z -> 1/2 (strong parity-balance) | **Verified, structural mechanism identified** |
| Density zero: Z_m / (4*5^{m-1}) -> 0 | **Follows from weak lemma** |
| S_m = 0.9 | **Follows from strong lemma** |

### Correction to C-series synthesis

The C-series reported:
- E/Z -> 4/9 with constant bias 1/18 (**wrong, artifact of wrong classification**)
- S_m -> 0.911 (**wrong, should be 0.900**)
- 1/18 information constant (**wrong, was the classification error showing through**)

The structural framework (parity decomposition, fiber structure, density-zero reduction) remains valid. Only the even/odd criterion was wrong.

---

## 6. Files

- `exp11_parity_balance.py`: Corrected experiment (u even/odd classification)
- `data/exp11_results.json`: Results with corrected classification (m=1..12)
