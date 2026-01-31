# Density Zero for Zeroless Powers of 2

## Statement

**Theorem.** *The set $A = \{n \ge 1 : 2^n \text{ contains no digit } 0 \text{ in base } 10\}$ has natural density zero:*

$$\lim_{N \to \infty} \frac{|\{n \le N : n \in A\}|}{N} = 0.$$

The proof is elementary. It uses the 5-adic fiber structure of the orbit $2^n \bmod 10^m$ to establish an exact recurrence for the parity balance among survivors, then bounds the survival rate via a range argument on that recurrence. No spectral theory, Fourier analysis, or probabilistic input is required.

---

## 1. The Orbit and Its Survivors

**Notation.** For $m \ge 1$, write $T_m = 4 \cdot 5^{m-1}$.

The multiplicative order of 2 modulo $5^m$ is $\text{ord}_{5^m}(2) = 4 \cdot 5^{m-1}$ (standard: $\text{ord}_5(2) = 4$, and the order lifts by a factor of 5 at each $p$-adic level). Since $10^m = 2^m \cdot 5^m$ and $\gcd(2^m, 5^m) = 1$, the sequence $2^n \bmod 10^m$ for $n \ge m$ is purely periodic with period $T_m$. Its $T_m$ distinct values form the **level-$m$ orbit**.

Each orbit element $x$ satisfies $2^m \mid x$ (since $n \ge m$), so we can write

$$x = 2^m \cdot u, \qquad u = 2^{n - m} \bmod 5^m.$$

The parameter $u$ ranges over the cyclic subgroup $\langle 2 \rangle \subset (\mathbb{Z}/5^m\mathbb{Z})^\times$, which has order $T_m$.

**Definition.** A **level-$m$ survivor** is an orbit element $x$ that is an $m$-digit number (i.e., $x \ge 10^{m-1}$) with no digit 0 in base 10. Let $Z_m$ denote the total count of survivors.

**Parity classification.** A level-$m$ survivor with parameter $u$ is

- **even-type** if $u$ is even,
- **odd-type** if $u$ is odd.

Let $E_m$ and $O_m$ denote the counts of even-type and odd-type survivors. Then $E_m + O_m = Z_m$. Define $e_m = E_m / Z_m$.

---

## 2. The Fiber Formula

**Lemma 1** (Fiber formula). *For all $m \ge 1$:*

$$Z_{m+1} = 4\,E_m + 5\,O_m.$$

*Proof.* Each level-$m$ survivor lifts to exactly 5 elements of the level-$(m+1)$ orbit. These lifts correspond to the 5 possible values of the leading digit $d_{m+1}$ (the $(m+1)$-th digit from the right).

Given a level-$m$ survivor with parameter $u$, its 5 lifts to level $m+1$ have parameters

$$u' = v_0 + j \cdot 5^m, \qquad j = 0, 1, 2, 3, 4,$$

where $v_0 \equiv u \cdot 2^{-1} \pmod{5^m}$. Since $2^{-1} \equiv (5^m + 1)/2 \pmod{5^m}$, we have:

- $u$ even: $v_0 = u/2$, so $0 \le v_0 < 5^m/2$.
- $u$ odd: $v_0 = (u + 5^m)/2$, so $5^m/2 < v_0 < 5^m$.

The leading digit of the $j$-th lift is

$$d_{m+1} = \left\lfloor \frac{2\,v_0}{5^m} \right\rfloor + 2j.$$

(This follows from $x' = 2^{m+1} u'$ and extracting the $(m+1)$-th digit.) Since $0 \le v_0 < 5^m$, the floor term is 0 or 1:

- **$u$ even** ($v_0 < 5^m/2$): the floor is 0, so $d_{m+1} \in \{0, 2, 4, 6, 8\}$. The lift with $d_{m+1} = 0$ fails the survivorship test. The remaining **4 lifts survive**.

- **$u$ odd** ($v_0 > 5^m/2$): the floor is 1, so $d_{m+1} \in \{1, 3, 5, 7, 9\}$. All digits are nonzero. All **5 lifts survive**.

Every level-$(m+1)$ survivor restricts to a level-$m$ survivor (its last $m$ digits are zeroless and form an $m$-digit number). So the total count at level $m+1$ is $Z_{m+1} = 4\,E_m + 5\,O_m$. $\square$

**Corollary** (Survival rate). $Z_{m+1} = (5 - e_m)\,Z_m$, and the per-level survival rate is

$$S_{m+1} \;=\; \frac{Z_{m+1}}{5\,Z_m} \;=\; 1 - \frac{e_m}{5}.$$

*Proof.* $Z_{m+1} = 4 E_m + 5 O_m = 4 e_m Z_m + 5(1 - e_m) Z_m = (5 - e_m) Z_m$. Divide by $5 Z_m$. $\square$

---

## 3. Parity Splits

**Lemma 2** (Even-parent split). *Each even-type survivor at level $m$ produces exactly 2 even-type and 2 odd-type children at level $m+1$.*

*Proof.* Let $u$ be even. The 4 surviving lifts have parameters $u'_j = u/2 + j \cdot 5^m$ for $j = 1, 2, 3, 4$. Since $5^m$ is odd:

| $j$ | parity of $j \cdot 5^m$ | parity of $u'_j$ |
|-----|------------------------|-------------------|
| 1   | odd                    | $\text{par}(u/2) + 1$ |
| 2   | even                   | $\text{par}(u/2)$     |
| 3   | odd                    | $\text{par}(u/2) + 1$ |
| 4   | even                   | $\text{par}(u/2)$     |

Two children share the parity of $u/2$; two have the opposite parity. The split is 2 even + 2 odd regardless of $\text{par}(u/2)$. $\square$

**Lemma 3** (Odd-parent split). *Each odd-type survivor at level $m$ produces 5 children at level $m+1$. If $v_0 = (u + 5^m)/2$ is even, the split is 3 even + 2 odd. If $v_0$ is odd, the split is 2 even + 3 odd.*

*Proof.* The 5 lifts have parameters $u'_j = v_0 + j \cdot 5^m$ for $j = 0, 1, 2, 3, 4$.

| $j$ | parity of $j \cdot 5^m$ | parity of $u'_j$ |
|-----|------------------------|-------------------|
| 0   | even                   | $\text{par}(v_0)$     |
| 1   | odd                    | $\text{par}(v_0) + 1$ |
| 2   | even                   | $\text{par}(v_0)$     |
| 3   | odd                    | $\text{par}(v_0) + 1$ |
| 4   | even                   | $\text{par}(v_0)$     |

Three children ($j = 0, 2, 4$) share the parity of $v_0$; two ($j = 1, 3$) have the opposite parity. $\square$

**Remark on $v_0$'s parity.** For odd $u$, we have $v_0 = (u + 5^m)/2$. Since $5^m \equiv 1 \pmod{4}$ for all $m \ge 1$:

- $u \equiv 3 \pmod{4}$: $u + 5^m \equiv 0 \pmod{4}$, so $v_0$ is even.
- $u \equiv 1 \pmod{4}$: $u + 5^m \equiv 2 \pmod{4}$, so $v_0$ is odd.

---

## 4. The Parity Recurrence

Among the $O_m$ odd-type parents at level $m$, let $p_m$ denote the fraction with even $v_0$ (equivalently, the fraction with $u \equiv 3 \pmod 4$). Then $p_m \in [0, 1]$.

By Lemmas 2 and 3, the number of even-type children at level $m+1$ is

$$E_{m+1} = 2\,E_m + 3\,p_m\,O_m + 2\,(1 - p_m)\,O_m = 2\,E_m + (2 + p_m)\,O_m.$$

Substituting $E_m = e_m Z_m$ and $O_m = (1 - e_m) Z_m$ into $e_{m+1} = E_{m+1}/Z_{m+1}$:

$$e_{m+1} = \frac{2\,e_m + (2 + p_m)(1 - e_m)}{4\,e_m + 5(1 - e_m)} = \frac{2 + p_m(1 - e_m)}{5 - e_m}. \tag{R}$$

**Bias identity.** Subtracting $1/2$ from both sides of (R):

$$e_{m+1} - \frac{1}{2} = \frac{(p_m - 1/2)(1 - e_m)}{5 - e_m}. \tag{B}$$

The parity bias at level $m+1$ is proportional to the mod-4 bias $p_m - 1/2$, contracted by the factor $(1 - e_m)/(5 - e_m)$.

---

## 5. The Weak Parity-Balance Lemma

**Proposition.** *For all $m \ge 1$, $\;e_m \in [2/5,\; 3/5]$.*

*Proof.* Define $f(e, p) = (2 + p(1 - e))/(5 - e)$ for $(e, p) \in [0, 1]^2$. We show $f$ maps $[0, 1]^2$ into $[2/5, 3/5]$.

The function $f$ is affine in $p$ with slope $(1 - e)/(5 - e) \ge 0$. So the extremes in $p$ are at $p = 0$ and $p = 1$.

**Lower bound** ($p = 0$):

$$f(e, 0) = \frac{2}{5 - e}.$$

This is increasing in $e$, with minimum $f(0, 0) = 2/5$ and maximum $f(1, 0) = 1/2$.

**Upper bound** ($p = 1$):

$$f(e, 1) = \frac{3 - e}{5 - e}.$$

The derivative is $-2/(5 - e)^2 < 0$, so this is decreasing in $e$. Maximum $f(0, 1) = 3/5$; minimum $f(1, 1) = 1/2$.

Therefore $f([0, 1]^2) \subseteq [2/5, 3/5]$.

The initial condition is $e_1 = E_1/Z_1 = 2/4 = 1/2 \in [2/5, 3/5]$. By induction, $e_m \in [2/5, 3/5]$ for all $m \ge 1$ (the recurrence sends any $e_m \in [0, 1]$ into $[2/5, 3/5]$, so the invariant is maintained). $\square$

**Remark.** The bound $e_m \ge 2/5$ is far stronger than needed. Any constant $\delta > 0$ with $e_m \ge \delta$ for all $m$ suffices for density zero.

---

## 6. Density Zero

**Lemma 4** (Survival bound). *For all $m \ge 2$:*

$$S_m = 1 - \frac{e_{m-1}}{5} \le 1 - \frac{2}{25} = \frac{23}{25}.$$

*Proof.* By the Proposition, $e_{m-1} \ge 2/5$ for $m - 1 \ge 1$. Apply the Corollary from Section 2. $\square$

**Proof of the Theorem.** The orbit density at level $m$ is

$$\frac{Z_m}{T_m} = \frac{Z_1}{T_1} \prod_{j=2}^{m} S_j = \prod_{j=2}^{m} S_j,$$

since $Z_1 = T_1 = 4$ (the four 1-digit orbit elements $\{2, 4, 6, 8\}$ are all zeroless). By direct computation, $e_1 = 1/2$, so $S_2 = 1 - 1/10 = 9/10$. Combining with Lemma 4 for $j \ge 3$:

$$\frac{Z_m}{T_m} \le \frac{9}{10} \cdot \left(\frac{23}{25}\right)^{m-2} \quad \text{for all } m \ge 2. \tag{$\star$}$$

Now fix any $m$ and any $N \ge 1$. If $2^n$ is zeroless and has at least $m$ digits, then $2^n \bmod 10^m$ is a level-$m$ survivor: the last $m$ digits are each nonzero (since all digits are), and the $m$-th digit is nonzero, so $2^n \bmod 10^m \ge 10^{m-1}$. Powers $2^n$ with fewer than $m$ digits satisfy $n < m / \log_{10} 2$.

Since the orbit $2^n \bmod 10^m$ has exact period $T_m$, the number of $n \le N$ whose orbit element is a survivor is at most $(\lfloor N/T_m \rfloor + 1)\,Z_m$. Therefore

$$|\{n \le N : 2^n \text{ is zeroless}\}| \;\le\; \left\lceil \frac{m}{\log_{10} 2} \right\rceil + \left(\left\lfloor \frac{N}{T_m} \right\rfloor + 1\right) Z_m.$$

Dividing by $N$ and sending $N \to \infty$:

$$\limsup_{N \to \infty} \frac{|\{n \le N : n \in A\}|}{N} \;\le\; \frac{Z_m}{T_m}.$$

This holds for every $m$. By $(\star)$, $Z_m/T_m \to 0$ exponentially. So the $\limsup$ is zero, and the natural density of $A$ is zero. $\square$

---

## 7. Computational Verification

The following table (from Experiment 11, computed via full orbit enumeration) confirms every structural claim through $m = 12$:

| $m$ | $Z_m$ | $E_m$ | $O_m$ | $e_m$ | $S_{m+1}$ |
|-----|--------|---------|---------|---------|------------|
| 1   | 4      | 2       | 2       | 0.500000 | 0.9000 |
| 2   | 18     | 9       | 9       | 0.500000 | 0.9000 |
| 3   | 81     | 41      | 40      | 0.506173 | 0.8988 |
| 4   | 364    | 182     | 182     | 0.500000 | 0.9000 |
| 5   | 1,638  | 819     | 819     | 0.500000 | 0.9000 |
| 6   | 7,371  | 3,685   | 3,686   | 0.499932 | 0.9000 |
| 7   | 33,170 | 16,582  | 16,588  | 0.499910 | 0.9000 |
| 8   | 149,268 | 74,639 | 74,629  | 0.500033 | 0.9000 |
| 9   | 671,701 | 335,852 | 335,849 | 0.500002 | 0.9000 |
| 10  | 3,022,653 | 1,511,320 | 1,511,333 | 0.499998 | 0.9000 |
| 11  | 13,601,945 | 6,800,982 | 6,800,963 | 0.500001 | 0.9000 |
| 12  | 61,208,743 | 30,604,369 | 30,604,374 | 0.500000 | 0.9000 |

The identity $Z_{m+1} = 4 E_m + 5 O_m$ holds exactly for all $m = 1, \ldots, 11$.

The observed $e_m$ values cluster tightly around $1/2$, well within the proved range $[0.4, 0.6]$. The bias $|e_m - 1/2|$ decays geometrically with fitted rate $\theta \approx 0.29$, consistent with the contraction factor $(1 - e)/(5 - e) \approx 1/9$ from identity (B).

---

## 8. Remarks

### 8.1 What the proof establishes

The bound $S_m \le 23/25 = 0.92$ is unconditional. The orbit density satisfies $Z_m / T_m \le 0.9 \cdot 0.92^{m-2}$, which decays to zero at an exponential rate. The data suggests the true rate is $S_m \approx 0.9$ (i.e., $e_m \approx 0.5$), but even the proved bound $e_m \ge 0.4$ suffices.

### 8.2 The self-correction mechanism

Identity (B) reveals why $e_m$ stays near $1/2$. The bias $e_{m+1} - 1/2$ equals $(p_m - 1/2)(1 - e_m)/(5 - e_m)$. For $e_m \in [0.4, 0.6]$, the contraction factor $(1 - e_m)/(5 - e_m)$ lies in $[1/11.5, 3/23] \approx [0.087, 0.130]$. So even if $p_m$ were maximally biased ($p_m = 0$ or $p_m = 1$), the parity bias would shrink by a factor of at least 7.7 per level. The system is self-correcting.

### 8.3 Ingredients and their provenance

| Ingredient | Status |
|------------|--------|
| $\text{ord}_{5^m}(2) = 4 \cdot 5^{m-1}$ | Standard number theory |
| Fiber formula: $Z_{m+1} = 4 E_m + 5 O_m$ | Proved (Lemma 1) |
| Even-parent 50/50 split | Proved (Lemma 2; uses only: $5^m$ is odd) |
| Odd-parent 3:2 / 2:3 split | Proved (Lemma 3; same parity argument) |
| $e_m \in [2/5, 3/5]$ | Proved (range analysis of rational function) |
| $S_m \le 23/25$ | Proved (immediate from above) |
| Density zero | Proved (exponential decay of $Z_m/T_m$) |

### 8.4 What remains for the 86 Conjecture

Density zero establishes that zeroless powers of 2 are rare. It does not prove they are finite. The proved bound gives $Z_m/T_m \le 0.9 \cdot 0.92^{m-2}$. A power $2^n$ with $k$ digits must survive all levels $m = 1, \ldots, k$. The heuristic probability of survival is roughly $\prod_{m=1}^{k} S_m \approx 0.9^k$, which sums to a finite expected count as $k \to \infty$.

Converting this heuristic into a proof of finiteness requires controlling correlations between levels, a substantially harder problem. The bias identity (B) and the observed decay rate $\theta \approx 0.29$ suggest these correlations are weak, but proving it demands either:

1. A spectral gap for the parity-augmented transfer operator, or
2. A quantitative equidistribution result for the mod-4 residues among survivors.

Either route would strengthen "density zero" to "finitely many."

---

## Appendix: Initial Conditions

At $m = 1$: the orbit is $\{2, 4, 8, 6\}$ (period 4). All four elements are 1-digit zeroless numbers, so $Z_1 = 4 = T_1$. The parameters are $u = x/2$: $u \in \{1, 2, 3, 4\}$. Two are even ($u = 2, 4$), two are odd ($u = 1, 3$). So $E_1 = O_1 = 2$ and $e_1 = 1/2$.

Check: $Z_2 = 4 \cdot 2 + 5 \cdot 2 = 18$. The orbit at $m = 2$ has period $T_2 = 20$, and among its 20 elements, 18 are 2-digit zeroless numbers (all except those ending in a zero or containing a zero). Verified. $\square$
