# Erdos 86 Conjecture: Strategy Status and Handoff

*January 29, 2026. For use by fresh Claude threads continuing this work.*

## The Conjecture

The set {n >= 1 : 2^n has no digit 0 in base 10} is finite, with max element n = 86.

Equivalently: for all sufficiently large m, no n with D(2^n) = m produces a zeroless power. Let N_m count the m-digit zeroless powers. Prove N_m = 0 for large m.

## What Is Proved

1. **Density zero.** The set has natural density zero. Elementary proof using parity-balance. File: `DENSITY_ZERO_PROOF.md`.

2. **Step B.** max_component(F_m) < theta = log10(2) for all m >= 2. No single component of F_m spans two consecutive orbit points. Proof is elementary (F_m subset of F_2, max component of F_2 is log10(20/11) = 0.2596 < 0.3010). File: `CONDITIONAL_PROOF_OUTLINE.md`, Section 5.

3. **Step B+ (m >= 4).** max_component(F_m) < min_{1<=k<=L_m} ||k*theta|| for all m >= 4. Every orbit hit is isolated in a distinct component, regardless of lag. Proven with ratio decaying as ~0.34 * 10^{-(m-4)}. File: Exp 34.

4. **Quasi-independence.** mu(F_m cap (F_m - h*theta)) / mu(F_m)^2 <= 1.58 for all tested lags and m values. Var(N_m)/E[N_m] ~ 1.26. File: Exp 32.

5. **Metric finiteness (Borel-Cantelli).** sum_m L_m * mu(F_m) < infinity. For a.e. theta, N_m = 0 for all large m. The entire difficulty is certifying theta = log10(2) is not exceptional.

## What Is Eliminated (with reasons)

| Strategy | Why it fails | Evidence |
|----------|-------------|----------|
| Fourier magnitude (L1, pointwise, l^p, additive) | Magnitudes don't decay; cancellation is in phases | Exps 20-22, 24 |
| Sieve methods | Short-interval equidistribution fails for upper digits | GPT 2A/2B |
| Thread-to-approximation (B) | Trailing digits independent of leading digits | Exp 27 |
| Resonance template + boundary Baker (D) | 95% of boundary integers non-smooth | Exps 30-31 |
| **Cluster forcing + pigeonhole + Baker (E)** | **Pigeonhole step is WRONG** (see below) | Exp 35, corrected |
| Ostrowski renormalization (C) | J-digit approx requires J ~ m; DK bounds useless | Exp 33 |

### Strategy E Postmortem

The proposed argument was:
1. Step B+ proves each hit in a distinct component.
2. If N_m >= 2, pigeonhole forces ||h*theta|| <= rho_m for some h.
3. Baker gives ||h*theta|| >= c/h^A.
4. Exponential vs polynomial contradiction.

**Step 2 is wrong.** Having N_m points in a set of total measure rho_m does NOT force any pair within distance rho_m. The 9^{m-1} components of F_m are scattered across [0,1). Hits can be in components far apart on the circle. Exp 35 data confirms: minimum pairwise gaps are O(1) constants (0.0969, 0.0103), not shrinking.

Three rescue attempts all fail:
- Baker on boundary positions: boundary integers aren't smooth (Exp 31)
- Baker on theta directly: orbit well-spacing != avoidance of F_m
- Effective equidistribution with error << 0.9^m: open problem in analytic number theory

## Two Surviving Strategies

### Strategy C': o(1) Coboundary (PRIMARY)

**The target estimate:**

S_m := sum_{k != 0} |hat{1_{F_m}}(k)| / ||k*theta|| = o(1) as m -> infinity

This gives |N_m - L_m*rho_m| < 1/2 for large m, forcing N_m = 0 since L_m*rho_m -> 0.

**What Baker provides:** ||k*theta|| >= C_0/|k|^lambda with lambda = 1 (for two logarithms). So the denominators contribute at most poly(m) growth.

**What's needed:** |hat{1_{F_m}}(k)| ~ rho_m = 0.9^{m-1} for |k| <= poly(m). This would give S_m ~ 0.9^m * poly(m) -> 0.

**Why this is plausible:** F_m is defined by m-1 "independent" digit conditions. Low-frequency k cannot resolve individual digit positions (which operate at frequencies ~10^j). The product structure should force |hat{1_{F_m}}(k)| ~ rho_m for low k.

**What's untested:**
- The Fourier coefficient bound for the continuous circle basis (not the 5-adic basis)
- Whether the product structure argument can be made rigorous (Mauduit-Rivat framework?)
- GPT Prompt 6 (`GPT_PROMPTS/APPROACH6_COBOUNDARY.md`) targets this question

### Strategy F: Second Moment (SECONDARY)

**The argument:** Quasi-independence (Exp 32) gives Var(N_m) ~ E[N_m]. With E[N_m] -> 0, P(N_m >= 1) -> 0 for each m. Borel-Cantelli (sum P < infinity) gives finiteness for a.e. theta.

**The gap:** This gives finiteness for a.e. theta, not for theta = log10(2) specifically. Needs Diophantine input to certify theta is not in the measure-zero exceptional set.

**Connection to C':** If the coboundary estimate works, it simultaneously proves finiteness for the specific theta = log10(2), making Strategy F unnecessary. Strategy F is the fallback if C' fails.

## Key Files

| File | Contents |
|------|----------|
| `CONDITIONAL_PROOF_OUTLINE.md` | Master proof document, 35 conclusions, all strategy analyses |
| `EXP20_SYNTHESIS.md` | Detailed conclusions 1-35 |
| `DENSITY_ZERO_PROOF.md` | Complete density zero proof |
| `METAPROMPT_SYNTHESIS.md` | "Two-axis obstruction" diagnostic |
| `GPT_PROMPTS/APPROACH6_COBOUNDARY.md` | GPT prompt for Strategy C' |
| `data/exp{N}_analysis.md` | Analysis documents for experiments 1-35 |
| `data/exp{N}_results.json` | Raw data for experiments |

## Key Constants

- theta = log10(2) = 0.30102999566398...
- CF: [0; 3, 3, 9, 2, 2, 4, 6, 2, 1, 1, 3, 1, 18, 1, 6, 1, 2, 9, 117, ...]
- Convergent denominators: q_0=1, q_1=3, q_2=10, q_3=93, q_4=196
- rho_m = mu(F_m) ~ (9/10)^{m-1}
- L_m = ceil(m/theta) ~ ceil(3.32*m)
- T_m = 4 * 5^{m-1} (period of 2^n mod 10^m)
- max_comp(F_m) = log10(1 + 81/(10^m - 1)) ~ 3.5 * 10^{-(m-1)}
- F_m has 9^{m-1} components, Cantor-dust topology

## Experiment Summary

35 experiments total (plus 29b correction). Key ones:
- Exp 20-22, 24: Fourier analysis exhausted
- Exp 25-26: O(1) discrepancy in transition zone, low orbit variation
- Exp 27: Thread-to-approximation fails
- Exp 28, 29b: Step B proved, F_m is Cantor dust
- Exp 30: O(1) danger cylinders, persistence is relay effect
- Exp 31: Boundary integers not smooth (blocks Strategy D)
- Exp 32: Quasi-independence confirmed (enables Strategy F)
- Exp 33: Ostrowski route quantitatively useless
- Exp 34: Step B+ verified for m >= 4
- Exp 35: Cluster forcing data, pigeonhole gap discovered

## Immediate Next Steps

1. **Run GPT Prompt 6** (`GPT_PROMPTS/APPROACH6_COBOUNDARY.md`) on GPT-o3 or GPT-4-Pro. Get assessment of the Fourier coefficient bound and the product structure argument.

2. **Exp 36 (optional):** Compute |hat{1_{F_m}}(k)| for the continuous circle Fourier basis for small |k| (1 through ~100) and m = 2..10. Verify whether these are ~ rho_m or something else. This is the empirical test of the heuristic.

3. **Literature check:** Mauduit-Rivat (JEMS 2010), Maynard (Annals 2019), and Drmota-Mauduit-Rivat on Fourier transforms of restricted-digit sets.
