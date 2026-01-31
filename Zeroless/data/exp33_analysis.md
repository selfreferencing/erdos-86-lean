# Experiment 33 Analysis: Ostrowski Renormalization Test

## Central Question

Can the Birkhoff sum N_m(L) be controlled via Ostrowski decomposition of L into convergent blocks, with Denjoy-Koksma applied to a J-digit coarse approximation of F_m? This tests the quantitative viability of the Ostrowski renormalization route from Conclusion 26.

## Part A: Continued Fraction of theta = log10(2)

CF expansion: [0; 3, 3, 9, 2, 2, 4, 6, 2, 1, 1, 3, 1, 18, 1, 6, 1, 2, 9, 117]

Convergent denominators:
| j | q_j | ||q_j*theta|| |
|---|-----|--------------|
| 0 | 1 | 0.301 |
| 1 | 3 | 0.097 |
| 2 | 10 | 0.0103 |
| 3 | 93 | 0.00042 |
| 4 | 196 | 0.00020 |
| 5 | 485 | 0.000060 |
| 6 | 2136 | 0.000014 |

The transition zone L_m = ceil(m/theta) ~ 3.32m stays below q_3 = 93 for all m <= 27 (L_27 = 90 < 93). The Ostrowski decomposition of L_m therefore uses blocks of size q_0 = 1, q_1 = 3, and q_2 = 10 only.

## Part C: J-digit Approximation Error

The J-digit approximation replaces f_m (checking all m digits for zeros) with f_{m,J} (checking only the first J digits). The difference is the survival rate contribution from digits J+1 through m.

**Key pattern: the excess rho_J - rho_m grows with m - J.**

| m | rho_m | rho_J=2 | rho_J=3 | rho_J=4 | rho_J=5 |
|---|-------|---------|---------|---------|---------|
| 2 | 0.900 | 0.900 | 0.900 | 0.900 | 0.900 |
| 5 | 0.655 | 0.900 | 0.810 | 0.728 | 0.655 |
| 8 | 0.478 | 0.900 | 0.810 | 0.728 | 0.655 |
| 10 | 0.387 | 0.900 | 0.810 | 0.728 | 0.655 |

When J < m, rho_J / rho_m = 0.9^{-(m-J)} grows exponentially. The "excess" hits from the coarse approximation overwhelm the actual count. At m=10, J=2: S_full = 9 but S_J = 30, a 3.3x overcount.

The Birkhoff sum error |S_L(f_m) - S_L(f_{m,J})| is therefore O(L * (rho_J - rho_m)) = O(L * 0.9^J * (1 - 0.9^{m-J})). For this to be small, we need J close to m.

## Denjoy-Koksma Bounds

The DK bound on each q_j-block of f_{m,J} is V(f_{m,J}) ~ 2 * 9^J (the total variation of the J-digit indicator on the circle). At m=8, J=2: DK bound ~ 162, while actual block discrepancy ~ 0.01. The DK bounds are 10,000x too conservative.

## Verdict

**The Ostrowski route requires J(m) ~ m** to keep the approximation error small. But J ~ m means V(f_{m,J}) ~ 9^m, recovering the useless circle variation. There is no asymptotic savings.

The fundamental issue: the Ostrowski route decomposes the Birkhoff sum into blocks where Denjoy-Koksma can be applied, but Denjoy-Koksma uses the CIRCLE variation of f, which is 9^m. The coarse approximation reduces this to 9^J but introduces an approximation error of order 0.9^J * L. For the product to vanish, we need 9^J * (1/q_{j+1}) * (0.9^J * L) -> 0, which requires J + m - J to be small, i.e., there is no degree of freedom to optimize.

**The Ostrowski renormalization strategy (Conclusion 26) is NOT asymptotically viable.** The route is "correct" in the sense that Denjoy-Koksma applies, but the bounds it produces grow exponentially rather than shrinking.

## Comparison with Other Strategies

The failure of the Ostrowski route strengthens the case for the two remaining viable strategies:
1. **Cluster forcing + Baker (Strategy E):** Bypasses Denjoy-Koksma entirely. Uses pigeonhole on component positions, not Birkhoff sum bounds.
2. **Zero-crossing geometric argument (from Exp 26):** Uses the direct counting of O(1) orbit transitions rather than circle variation.

## New Conclusion

**Conclusion 33.** The Ostrowski renormalization route for controlling N_m(L) is not asymptotically viable. The J-digit approximation of F_m by f_{m,J} requires J ~ m to keep approximation error small, but this makes the Denjoy-Koksma bound 9^J ~ 9^m, providing no savings over the direct circle variation. The DK bounds are 10,000x too conservative compared to actual block discrepancies. The Ostrowski route (Conclusion 26) is formally correct but quantitatively useless (Exp 33).
