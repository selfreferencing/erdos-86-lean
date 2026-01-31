# Experiment 24 Analysis: The 0.0877 Additive Fourier Plateau

## Key Findings

### 1. Three distinct tiers, not a single plateau

The additive Fourier coefficients max|hat(f_m)(a)|/rho grouped by depth k = m - v_5(a) stabilize into three tiers as m grows:

| Tier | Depth | Stabilized ratio | Approximate value |
|------|-------|------------------|-------------------|
| k=1  | shallowest minor arc | ~0.2154 | 1/sin(pi/5)^2? TBD |
| k=2  | | ~0.0959 | close to but NOT 1/10 |
| k=3  | | ~0.0894 | |
| k=4  | | ~0.0888 | approaching 4/45? |
| k>=5 | deep minor arcs | ~0.0877 | THE plateau |

The k=1 value (0.2154) is the same as the multiplicative max|hat(f)|/rho = 0.12341 scaled by a factor, confirming these are the same dominant mode seen from different bases.

Within the "plateau" region (k>=5), there is actually a finer structure: the values oscillate slightly between ~0.0877 and ~0.0877, converging to a limit as m grows.

### 2. The argmax frequencies have revealing structure

At each depth k, the maximizing frequency a has a very specific 5-adic digit pattern:

- k=2: argmax digits have the form [0,...,0,d1,d2] with specific d1,d2
- k=3: argmax digits have the form [0,...,0,d1,d2,0,...] -- typically a power of 10
- Deep k: argmax is often a = 1, 10, 100, etc. (powers of 10) or a = 5^m - 1 = [4,4,...,4]

The pattern a = 10^j (which has 5-adic digits [0,...,0,2,0,...,0] since 10 = 2*5) and a = 5^m - 1 = [4,4,...,4,4] frequently appear.

### 3. Symmetry: digits 1 and 4 are equivalent, digits 2 and 3 are equivalent

Part E reveals a clean symmetry in the leading nonzero 5-adic digit:

| Leading digit d | Max ratio at k=3 (m=9) | Mean ratio |
|-----------------|-------------------------|------------|
| d=1 | 0.0894 | 0.0229 |
| d=2 | 0.0849 | 0.0263 |
| d=3 | 0.0849 | 0.0263 |
| d=4 | 0.0894 | 0.0229 |

Digits 1 and 4 are exactly equal, as are digits 2 and 3. This is the symmetry d <-> 5-d, which corresponds to a <-> -a mod 5^m. This makes sense: hat(f)(-a) = conjugate(hat(f)(a)) since f is real-valued, so |hat(f)(a)| = |hat(f)(-a)|.

The maximum is always achieved at d=1 or d=4 (equivalently), never at d=2 or d=3.

### 4. The plateau is NOT 4/45

4/45 = 0.08888... The plateau at k>=5 is ~0.0877, which is about 1.4% below 4/45. Close but definitively different. None of the tested closed forms match.

The best candidate from the data: the plateau appears to be approaching a limit from above as k increases, with the sequence:
- k=3: 0.0894
- k=4: 0.0888
- k=5: 0.0878
- k=6: 0.0877
- k=7: 0.0877

The limit may be irrational or involve transcendental constants.

### 5. The Riesz product structure DOES NOT explain the plateau

Part G shows that the product of individual max|hat(g_r)|/rho_r decays as 0.2^m (each factor contributes ~0.2), but the actual max|hat(f_m)|/rho stabilizes at 0.2154. The ratio between actual and product grows as 5^m, meaning the convolution structure creates massive CONSTRUCTIVE interference at the dominant frequency.

Individual max ratios: [0.2000, 0.2114, 0.2005, 0.2000, 0.2000, ...] for digits 1,2,3,...

The fact that each g_r contributes max ratio ~0.2 = 1/5 while the product stabilizes at 0.2154 means the argmax frequencies for different g_r are ALIGNED (they point in the same direction in Fourier space), creating coherent addition rather than random-walk-style cancellation.

### 6. Transfer matrix max ratios are very large but means are small

Part D reveals that the transfer ratios |phi_r(d*5^{r-1}+a')|/|phi_{r-1}(a')| have:
- Max ratios up to 35.8 (at d=4, r=5)
- Mean ratios of 0.3-0.7 (contractive on average)

The max ratios being >> 1 means that for SOME frequencies, the next digit AMPLIFIES the Fourier coefficient. This is why the plateau exists: there are special frequency directions where each successive digit condition reinforces rather than weakens the Fourier mode.

The mean ratio < 1 explains why most coefficients are small, but the max ratio >> 1 explains why the plateau doesn't decay to 0.

### 7. The dominant mode at k=1 (max ratio ~0.2154)

Across all m >= 3, the overall max|hat(f)(a)|/rho stabilizes at exactly 0.21536... This is the "true" spectral constant of the zeroless digit problem in the additive basis. It occurs at depth k=1 (a = multiple of 5^{m-1} but not 5^m).

The value 0.21536... does not match simple fractions. It may relate to:
- The digit-2 indicator (since the leading nonzero digits in the argmax are often 2 or 3)
- A product of sin values at 5th roots of unity

## Connection to Finiteness

The plateau analysis confirms that the additive Fourier approach cannot prove finiteness through magnitude bounds alone, since:
1. max|hat(f)(a)|/rho = 0.2154 (constant, not decaying)
2. The plateau at ~0.0877 for deep minor arcs is also constant
3. The l^1 norm still grows because there are 5^m coefficients each contributing ~0.0877 * rho

The phase structure (not just magnitudes) determines whether the sum over minor arcs cancels. The next step should focus on understanding WHY the error is O(1) despite the magnitude bounds failing, perhaps through the Dumitru/Diophantine perspective.

## Technical Value

The key structural insight: the additive Fourier spectrum of f_m has a HIERARCHICAL structure indexed by 5-adic depth, with the d <-> 5-d symmetry and specific maximizing frequencies. This structure is determined by the interaction between multiplication by 2^m (the orbit generator) and the decimal digit test (which is additive in 5-adic coordinates).
