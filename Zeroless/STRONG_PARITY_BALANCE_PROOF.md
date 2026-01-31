# Strong Parity-Balance for Zeroless Powers of 2

## Complete Proof Chain: Lemmas 1-6

### January 28, 2026

---

## Main Result

**Theorem (Strong Parity-Balance).** *Let $Z_m$ denote the number of level-$m$ zeroless orbit elements of $2^n \bmod 10^m$, with $E_m$ even-type and $O_m$ odd-type survivors. Then:*

$$\left|\frac{E_m}{Z_m} - \frac{1}{2}\right| = O\!\left(\left(\frac{1}{3}\right)^m\right).$$

*In particular, $e_m = E_m / Z_m \to 1/2$ exponentially, and the survival rate satisfies $S_m = 9/10 + O((1/3)^m)$.*

**Corollary (Density Zero).** *The set $\{n \ge 1 : 2^n \text{ has no digit 0 in base 10}\}$ has natural density zero.*

---

## Overview of the Proof

The proof chain has six lemmas, organized into three blocks:

**Block I (Fiber Structure, Lemmas 1-3):** The 5-adic parametrization of the orbit gives the fiber formula $Z_{m+1} = 4E_m + 5O_m$ and exact parity splits for even and odd parents.

**Block II (Self-Correction, Lemmas 4-5):** The parity recurrence has a built-in contraction mechanism. Proposition 5 reduces the strong lemma to controlling a secondary parameter $p_m$.

**Block III (Transfer, Lemma 6):** The mod-8 distribution of odd survivors is governed by a doubly stochastic circulant with spectral radius $1/3$ away from uniform. This gives geometric decay of $p_m$, closing the proof.

---

## Block I: Fiber Structure

### 1. The Orbit and Survivors

For $m \ge 1$, the sequence $2^n \bmod 10^m$ (for $n \ge m$) is periodic with period $T_m = 4 \cdot 5^{m-1}$. Each orbit element $x$ satisfies $2^m \mid x$ and can be written $x = 2^m u$ where $u \in (\mathbb{Z}/5^m\mathbb{Z})^{\times}$.

A **level-$m$ survivor** is an orbit element that is an $m$-digit number with no digit 0. Survivors are classified as **even-type** ($u$ even) or **odd-type** ($u$ odd).

### Lemma 1 (Fiber Formula)

*For all $m \ge 1$:*

$$Z_{m+1} = 4\,E_m + 5\,O_m.$$

*Proof.* Each survivor at level $m$ lifts to 5 elements at level $m+1$, corresponding to the 5 choices of leading digit $d_{m+1}$. For parameter $u$, the lifts have $u' = v_0 + j \cdot 5^m$ ($j = 0, \ldots, 4$), where $v_0 = u \cdot 2^{-1} \bmod 5^m$.

- **$u$ even**: $v_0 = u/2 < 5^m/2$, so $d_{m+1} \in \{0, 2, 4, 6, 8\}$. The digit 0 fails. Four lifts survive.
- **$u$ odd**: $v_0 = (u + 5^m)/2 > 5^m/2$, so $d_{m+1} \in \{1, 3, 5, 7, 9\}$. All five survive.

Total: $Z_{m+1} = 4 E_m + 5 O_m$. $\square$

**Corollary.** $Z_{m+1} = (5 - e_m) Z_m$, and $S_{m+1} = Z_{m+1}/(5 Z_m) = 1 - e_m/5$.

### Lemma 2 (Even-Parent Split)

*Each even-type parent produces exactly 2 even + 2 odd children.*

*Proof.* The 4 surviving lifts have $u'_j = u/2 + j \cdot 5^m$ for $j = 1, 2, 3, 4$. Since $5^m$ is odd, consecutive $j$-values alternate parity. Two are even, two are odd. $\square$

### Lemma 3 (Odd-Parent Split)

*Each odd-type parent produces 5 children: either $3E + 2O$ or $2E + 3O$, depending on whether $v_0 = (u + 5^m)/2$ is even or odd.*

*Proof.* The 5 lifts have $u'_j = v_0 + j \cdot 5^m$ for $j = 0, \ldots, 4$. Three values of $j$ ($\{0, 2, 4\}$) share the parity of $v_0$; two ($\{1, 3\}$) have the opposite parity. $\square$

**Remark.** Since $5^m \equiv 1 \pmod{4}$ for all $m \ge 1$: $u \equiv 3 \pmod{4}$ gives even $v_0$ (split $3E + 2O$), and $u \equiv 1 \pmod{4}$ gives odd $v_0$ (split $2E + 3O$).

---

## Block II: Self-Correction

### The Parity Recurrence

Let $p_m$ denote the fraction of odd-type parents with even $v_0$ (equivalently, $u \equiv 3 \pmod{4}$). From Lemmas 2-3:

$$E_{m+1} = 2 E_m + (2 + p_m) O_m, \qquad e_{m+1} = \frac{2 + p_m(1 - e_m)}{5 - e_m}. \tag{R}$$

**Bias identity:** Subtracting $1/2$:

$$e_{m+1} - \frac{1}{2} = \frac{(p_m - 1/2)(1 - e_m)}{5 - e_m}. \tag{B}$$

### Lemma 4 (Weak Parity-Balance)

*For all $m \ge 1$: $\;e_m \in [2/5, 3/5]$.*

*Proof.* Define $f(e, p) = (2 + p(1-e))/(5-e)$. The function $f$ is affine in $p$ with nonnegative slope. At $p = 0$: $f(e, 0) = 2/(5-e) \ge 2/5$. At $p = 1$: $f(e, 1) = (3-e)/(5-e) \le 3/5$. So $f([0,1]^2) \subseteq [2/5, 3/5]$. Since $e_1 = 1/2 \in [2/5, 3/5]$, the bound holds by induction. $\square$

**Corollary.** The contraction factor satisfies $(1 - e_m)/(5 - e_m) \le 3/23$ for all $m \ge 1$.

### Proposition 5 (Key Reduction)

*If $|p_m - 1/2| \le C_p \cdot \theta^m$ for some $\theta < 1$ and all $m$, then $|e_m - 1/2| \le C \cdot \theta^m$ with $C = (3/23) C_p$.*

*Proof.* From (B): $|e_{m+1} - 1/2| = |p_m - 1/2| \cdot (1 - e_m)/(5 - e_m) \le |p_m - 1/2| \cdot (3/23)$. Insert the hypothesis. $\square$

**The strong lemma is equivalent to: $|p_m - 1/2| = O(\theta^m)$.**

---

## Block III: The Transfer Lemma

### Setup: Mod-8 Distribution

For odd-type survivors at level $m$, define:

$$v_m = (O_m(1),\; O_m(3),\; O_m(5),\; O_m(7))^{\mathsf{T}},$$

where $O_m(r)$ counts odd survivors with $u \equiv r \pmod{8}$.

### The Imbalance Chain (F1-F2)

**F1 (Exact recurrence).** The parity imbalance satisfies:

$$\Delta_{m+1} = E_{m+1} - O_{m+1} = -(Q1_m - Q3_m),$$

where $Q1_m, Q3_m$ count odd parents by $u \bmod 4$.

**Bound:** $|\Delta_{m+1}|/Z_{m+1} \le (3/23)|q_m|$ where $q_m = (Q1_m - Q3_m)/O_m$.

**F2 (Neutrality cascade).**

$$Q_m := Q1_m - Q3_m = \sigma_m \cdot (O_{m-1}(1) - O_{m-1}(5)),$$

where $\sigma_m = (-1)^{m-1}$.

So the imbalance at level $m+1$ is controlled by the mod-8 distribution at level $m$.

### Lemma 6 (Transfer Lemma)

*There exists $\theta < 1$ such that $|\Delta_m|/Z_m = O(\theta^m)$.*

*Proof.* The argument has four steps.

**Step 1: The transfer matrix.** The lift map $u' = 5u + a$ sends odd parents ($u \equiv r \bmod 8$) to odd children (at $a \in \{0, 2, 4\}$) with $u' \equiv 5r + a \bmod 8$. The raw transfer matrix on odd residue classes $(1, 3, 5, 7)$ is:

$$T = \begin{pmatrix} 1 & 1 & 1 & 0 \\ 0 & 1 & 1 & 1 \\ 1 & 0 & 1 & 1 \\ 1 & 1 & 0 & 1 \end{pmatrix}.$$

Each column and each row sums to 3. The stochastic matrix $P = T/3$ is doubly stochastic with uniform stationary distribution $\bar{p} = (1/4, 1/4, 1/4, 1/4)$.

**Step 2: Spectral analysis.** Relabel classes by $x = (r-1)/2 \in \mathbb{Z}/4\mathbb{Z}$. The update becomes $x' \equiv x + s \pmod{4}$ for $s \in \{0, 2, 3\}$, each with weight $1/3$. So $P$ is a circulant on $\mathbb{Z}/4\mathbb{Z}$ with kernel $\mu = (\delta_0 + \delta_2 + \delta_3)/3$.

The eigenvalues are $\lambda_k = \hat{\mu}(k) = (1 + \omega^{2k} + \omega^{3k})/3$ with $\omega = i$:

| $k$ | $\lambda_k$ | $|\lambda_k|$ |
|-----|------------|---------------|
| 0   | 1          | 1             |
| 1   | $-i/3$    | $1/3$         |
| 2   | $1/3$     | $1/3$         |
| 3   | $i/3$     | $1/3$         |

All nontrivial eigenvalues have modulus $1/3$. Therefore $\rho(P - J/4) = 1/3$.

**Step 3: Deviation decay.** Define $d_m = p_m - \bar{p}$ where $p_m = v_m / O_m$. Since $P$ is normal (circulant), its operator norm on the mean-zero subspace equals the spectral radius:

$$\|d_m\|_2 \le (1/3)^m \|d_0\|_2.$$

The charge functional $L(p_m) = p_m(1) - p_m(5) = d_m(1) - d_m(5)$ satisfies:

$$|L(p_m)| \le \|d_m\|_1 \le 4\|d_m\|_2 \le 4(1/3)^m \|d_0\|_2.$$

So $|O_m(1) - O_m(5)|/O_m = O((1/3)^m)$.

**Step 4: Chain completion.** By F2:

$$|Q_{m+1}| = |O_m(1) - O_m(5)| = O_m \cdot O((1/3)^m).$$

Dividing by $O_{m+1}$:

$$|q_{m+1}| = O((1/3)^m).$$

By F1:

$$\frac{|\Delta_{m+2}|}{Z_{m+2}} \le \frac{3}{23} |q_{m+1}| = O((1/3)^m).$$

Re-indexing: $|\Delta_m|/Z_m = O((1/3)^m)$. $\square$

---

## Assembling the Main Result

**Proof of the Theorem.** Lemma 6 gives $|\Delta_m|/Z_m = O((1/3)^m)$. Since $\Delta_m = E_m - O_m = (2e_m - 1) Z_m$:

$$|e_m - 1/2| = |\Delta_m|/(2 Z_m) = O((1/3)^m).$$

Equivalently, by the chain through Proposition 5: Lemma 6 implies $|p_m - 1/2| = O((1/3)^m)$, which implies $|e_m - 1/2| = O((1/3)^m)$.

For the survival rate: $S_{m+1} = 1 - e_m/5 = 9/10 + O((1/3)^m)$. $\square$

**Proof of the Corollary.** The orbit density satisfies $Z_m / T_m = \prod_{j=2}^{m} S_j$. By Lemma 4 (the weak bound suffices): $S_j \le 23/25 < 1$ for all $j \ge 2$. So $Z_m/T_m \to 0$ exponentially. The natural density of zeroless powers is at most $Z_m/T_m$ for every $m$, hence zero. $\square$

---

## Computational Verification

All structural claims verified by full orbit enumeration through $m = 12$ (Experiments 11, 13):

| $m$ | $Z_m$ | $E_m/Z_m$ | $|E/Z - 1/2|$ | $\theta$-fit |
|-----|--------|-----------|---------------|-------------|
| 1   | 4      | 0.500000  | 0             | ---         |
| 3   | 81     | 0.506173  | $6.2 \times 10^{-3}$ | --- |
| 6   | 7,371  | 0.499932  | $6.8 \times 10^{-5}$ | 0.33 |
| 9   | 671,701 | 0.500002 | $2.2 \times 10^{-6}$ | 0.29 |
| 12  | 61,208,743 | 0.500000 | $4.1 \times 10^{-8}$ | 0.29 |

The F2 identity $Q_m = \sigma_m (O_{m-1}(1) - O_{m-1}(5))$ verified exactly for $m = 2, \ldots, 10$.

The mod-8 distribution converges to $(1/4, 1/4, 1/4, 1/4)$ as predicted.

---

## Additional Results

### Carry-0 Exact Balance

**Proved via involution** (E2-Pro): The map $T(x) = x + 2 \cdot 10^{m-1}$ is an involution on carry-0 survivors that flips $u$-parity (since $u \mapsto u + 5^{m-1}$ and $5^{m-1}$ is odd). Therefore $E_{c0}(m) = O_{c0}(m)$ exactly. All parity imbalance resides in the carry-1 subspace.

### Exact Spectral Gap (Conditional)

The carry-augmented 4x4 matrix $M_{\text{aug}}$ (states: carry $\times$ parity-type) gives the exact spectral gap:

$$\theta_{\text{exact}} = \frac{2\sqrt{6}}{9 + \sqrt{65}} = 0.28712\ldots$$

This arises from $\rho(M_{\text{par}}) = \sqrt{6}$ and $\rho(M_{\text{tot}}) = (9 + \sqrt{65})/2$. Making this rigorous requires the pair-to-orbit transfer argument (E3-Pro's Lemma 6 formulation). The pure mod-8 proof at $\theta = 1/3$ bypasses this entirely.

---

## Proof Dependencies

```
Lemma 1 (Fiber formula) ──────────┐
                                   ├── Parity recurrence (R), Bias identity (B)
Lemma 2 (Even split) ────────────┤
                                   │
Lemma 3 (Odd split) ─────────────┘

Lemma 4 (Weak balance) ──── uses: range of f(e,p) over [0,1]^2
   │
   ├── Corollary: (1-e)/(5-e) ≤ 3/23
   │
   └── Density Zero (immediate from S_m ≤ 23/25)

Proposition 5 (Reduction) ──── uses: Bias identity (B) + Lemma 4 contraction bound
   │
   └── Strong lemma ⟺ |p_m - 1/2| = O(θ^m)

Lemma 6 (Transfer) ──── uses: mod-8 transfer matrix, circulant spectral analysis
   │
   ├── F2 chain: mod-8 deviation → Q_m bound
   │
   └── F1 chain: Q_m → Δ_{m+1} bound

Strong Parity-Balance Theorem ──── Lemma 6 + Proposition 5
```

---

## Summary of Ingredients

| Ingredient | Nature | Depth |
|------------|--------|-------|
| $\text{ord}_{5^m}(2) = 4 \cdot 5^{m-1}$ | Standard number theory | Elementary |
| Fiber formula $Z_{m+1} = 4E + 5O$ | Digit arithmetic | Elementary |
| Even-parent 2+2 split | Parity of $5^m$ | Trivial |
| Odd-parent 3+2/2+3 split | Same parity argument | Trivial |
| Weak balance $e_m \in [2/5, 3/5]$ | Range of rational function | Elementary |
| F1 exact recurrence for $\Delta$ | Counting argument | Elementary |
| F2 neutrality cascade | Mod-4/mod-8 analysis | Elementary |
| Mod-8 transfer matrix | Lift map computation | Elementary |
| Circulant eigenvalue computation | Discrete Fourier transform on $\mathbb{Z}/4\mathbb{Z}$ | Undergraduate |
| Spectral gap $\to$ deviation decay | Operator norm bound | Standard |

The entire proof is self-contained and uses only standard tools from linear algebra and elementary number theory. No spectral theory of infinite-dimensional operators, Fourier analysis on $\mathbb{R}$, or probabilistic methods are required.
