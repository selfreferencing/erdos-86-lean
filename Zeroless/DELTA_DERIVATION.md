# Derivation of the Exact Spectral Gap theta = 0.2871

## The Question

The Transfer Lemma (Lemma 6) is proved with theta = 1/3 via the pure mod-8 transfer matrix. The empirical decay rate is theta_late ~ 0.289. F5B suggested delta = 3/23 in a "uniform refresh" model. This document analyzes the true mechanism.

---

## 1. The F5B Model and Its Limitations

F5B proposed the effective operator:

$$T_{\text{eff}} = (1 - \delta) P_0 + \delta \Pi,$$

where $P_0$ is the mod-8 stochastic matrix, $\Pi = J/4$ is the uniform projection, and $\delta = 3/23$. This gives:

$$\theta_{\text{eff}} = \frac{1 - \delta}{3} = \frac{20}{69} \approx 0.2899.$$

The value $3/23 = (1 - e_m)/(5 - e_m)$ evaluated at $e_m = 2/5$ is the **worst-case contraction factor** from the bias identity (Lemma 4), not a "refresh fraction" in the combinatorial sense.

---

## 2. The Actual Refresh Fraction

At each level, odd children at level $m+1$ come from two sources:

**Even parents** (refresh channel): Each even parent produces $4$ children, split $2E + 2O$ (Lemma 2). So even parents contribute $2 E_m$ odd children total.

**Odd parents** (transfer channel): Each odd parent produces $5$ children, split either $3E + 2O$ or $2E + 3O$ (Lemma 3). On average (at $p_m = 1/2$), odd parents contribute $2.5 \cdot O_m$ odd children.

The actual refresh fraction is:

$$\delta_{\text{actual}} = \frac{2 E_m}{2 E_m + 2.5 \cdot O_m}.$$

At $e_m = 1/2$ (so $E_m = O_m$):

$$\delta_{\text{actual}} = \frac{2}{2 + 2.5} = \frac{4}{9} \approx 0.444.$$

**Experiment 14 confirms:** $\delta_{\text{empirical}} \approx 0.444$ at every level tested ($m = 2, \ldots, 9$).

This gives $\theta = (1 - 4/9)/3 = 5/27 \approx 0.185$, **not** $0.289$. The simple refresh model fails because:

1. The "refresh" channel (even parents) does **not** produce uniformly distributed odd children mod 8.
2. The signed sum $w^{\mathsf{T}} M_{EO}$ (where $w$ encodes the parity character) is exactly zero, meaning even parents contribute zero to the mod-8 bias. This is **stronger** than uniform mixing, but it means the dilution effect operates differently than the $T_{\text{eff}}$ model assumes.

---

## 3. The Signed Sum Analysis

Define the signed vector $w = (-1, +1, -1, +1)$ on odd residue classes $(1, 3, 5, 7)$, which measures the quantity $O_m(3) + O_m(7) - O_m(1) - O_m(5) = 2 O_m (p_m - 1/2)$.

**Key identity for odd-to-odd channel:**

$$w^{\mathsf{T}} T_{OO} = w^{\mathsf{T}}.$$

Since $P_0 = T_{OO}/3$, we get $w^{\mathsf{T}} P_0 = (1/3) w^{\mathsf{T}}$. So $w$ is a left eigenvector of $P_0$ with eigenvalue $1/3$. The odd-to-odd channel contracts the signed sum by exactly $1/3$ per step.

**Key identity for even-to-odd channel:**

$$w^{\mathsf{T}} M_{EO} = (0, 0, 0, 0).$$

Regardless of even parent distribution, even parents contribute **exactly zero** to the signed sum. The even-to-odd channel is orthogonal to the bias mode.

**Consequence:** In the pure mod-8 model, the signed sum evolves as:

$$S_{m+1} = (1/3) \cdot S_m + 0 = (1/3) \cdot S_m.$$

This gives $\theta = 1/3$ for the mod-8 approximation, recovering the Transfer Lemma.

---

## 4. The True Mechanism: Carry-Matrix Spectral Decomposition

The pure mod-8 model gives $\theta = 1/3$. The improved $\theta = 0.2871$ comes from the **carry-augmented transfer matrix**, which tracks more structure than mod-8 alone.

The 4x4 matrix $M_{\text{aug}}$ with states (carry, parity-type) $\in \{0,1\} \times \{E, O\}$ block-diagonalizes in the $(Z, \Delta) = (E+O, E-O)$ basis:

$$M_{\text{tot}} = \begin{pmatrix} 4 & 4 \\ 4 & 5 \end{pmatrix}, \qquad M_{\text{par}} = \begin{pmatrix} 2 & 2 \\ -2 & 1 \end{pmatrix}.$$

The spectral data:

- $\rho(M_{\text{tot}}) = (9 + \sqrt{65})/2 \approx 8.531$ (Perron-Frobenius)
- $\rho(M_{\text{par}}) = \sqrt{6} \approx 2.449$ (complex eigenvalues with modulus $\sqrt{6}$)

The exact spectral gap:

$$\boxed{\theta = \frac{\rho(M_{\text{par}})}{\rho(M_{\text{tot}})} = \frac{2\sqrt{6}}{9 + \sqrt{65}} = 0.28712\ldots}$$

This is an algebraic number, not $20/69$ or $1/3$.

---

## 5. Why F5B's Approximation Was Close

The near-coincidence $20/69 \approx 0.2899 \approx 0.2871$ is explained by:

$$\frac{20}{69} - \frac{2\sqrt{6}}{9 + \sqrt{65}} \approx 0.0028$$

This $\sim 1\%$ error arises because $3/23$ happens to be numerically close to the value $\delta^*$ that would make the $T_{\text{eff}}$ model exact:

$$\delta^* = 1 - \frac{3 \cdot 2\sqrt{6}}{9 + \sqrt{65}} \approx 0.1387.$$

Compare: $3/23 \approx 0.1304$. The relative error is about $6\%$ in $\delta$, which maps to $\sim 1\%$ error in $\theta$.

The value $3/23$ arises as the contraction factor $(1 - e_m)/(5 - e_m)$ at the boundary $e_m = 2/5$ of the weak-lemma invariant interval. Its proximity to $\delta^*$ is a numerical coincidence without deep combinatorial significance.

---

## 6. The Three Levels of the Result

| Level | $\theta$ | Status | Mechanism |
|-------|----------|--------|-----------|
| **Rigorous** | $1/3$ | **PROVED** | Mod-8 transfer matrix, Fourier diagonalization |
| **Exact (conditional)** | $2\sqrt{6}/(9+\sqrt{65})$ | Needs transfer argument | Carry-matrix $M_{\text{par}}/M_{\text{tot}}$ spectral gap |
| **Approximate** | $20/69$ | Phenomenological | $T_{\text{eff}}$ model with $\delta = 3/23$ |

The rigorous $\theta = 1/3$ suffices for all applications (Lemma 6, strong parity-balance, density zero). The exact $\theta = 0.2871$ provides the sharp asymptotic but requires formalizing the pair-to-orbit transfer argument (conditions from E3-Pro's Lemma 6 formulation).

---

## 7. Conclusion

The F5B claim $\delta = 3/23$ giving $\theta = 20/69$ is a useful approximation but not the correct mechanism. The true spectral gap comes from the carry-augmented transfer matrix, not a "uniform refresh" channel. The proof at $\theta = 1/3$ is fully rigorous and sufficient. The sharper $\theta = 2\sqrt{6}/(9 + \sqrt{65})$ is the exact algebraic answer, confirmed by both D2-Pro matrix constructions and exp11/exp13 numerical data.
