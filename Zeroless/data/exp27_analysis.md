# Experiment 27 Analysis: Thread-to-Approximation Test

## Central Question

Does survival of a thread to depth m in the 5-adic tree force an exponentially good rational approximation to log10(2)? If yes, Baker's theorem would kill survival for large m.

## Verdict: NO. Strategy B fails in its naive form.

The data decisively shows that **survival does NOT force good rational approximation** to theta = log10(2). The approximation quality of surviving n values is indistinguishable from generic n values. The irrationality exponent never exceeds 1.3, far below the Roth bound of 2. The thread-to-approximation bridge, as conceived, does not exist.

However, the data reveals something else that is important: the 5-adic congruence chain imposes structural constraints on n that operate in a different way than Diophantine approximation quality.

## Part A: Approximation Quality

The approximation quality |n*theta - round(n*theta)| for survivors ranges from 0.02 to 0.49, with no systematic pattern. The quality ratio (survivor / generic median 0.25) ranges from 0.08 to 1.98. Some survivors are better-than-average approximators (n=20 at m=5 has quality 0.021, ratio 0.08), but others are worse-than-average (n=15 at m=4 has quality 0.485, ratio 1.94).

**The survivor n values are simply the n with D(n) = m whose fractional part frac(n*theta) lands in F_m.** This constrains frac(n*theta) to a specific subset of [0,1), but does NOT force |n*theta - p| to be small. The fractional part can be anywhere within F_m, which occupies measure ~0.9^m but is spread across [0,1) in many small intervals.

## Part B: Congruence Chains

The congruence chains reveal a striking structural feature. At each level j, the thread survives if 2^n mod 10^j has all j digits nonzero. The chain is uniquely determined (0-or-1 branching past level 3).

Notable observation: **the same n values appear as survivors across multiple m values.** For example:
- n=86 is a survivor for m=20, 21, 22, 23, 24, 25, 26 (7 levels)
- n=67 is a survivor for m=16, 17, 18, 19, 20, 21 (6 levels)
- n=49 is a survivor for m=13, 14, 15 (3 levels)

This is because if 2^n has m digits and all are nonzero, then looking at just the last j digits (for j < m) also gives all nonzero digits. Survivors "persist downward" through levels.

The congruence chain for n=86 (the last zeroless power) at m=26 shows:
- 2^86 mod 10^1 = 4 (nonzero)
- 2^86 mod 10^2 = 64 (both nonzero)
- 2^86 mod 10^3 = 264 (all nonzero)
- ...continuing through all 26 levels, each adding one more nonzero digit from the right

## Part C: Statistical Comparison

**Survivors are NOT systematically better approximators.** The ratio of survivor mean to generic mean:

| m range | typical ratio | verdict |
|---------|--------------|---------|
| 2-5 | 0.95-1.37 | NO systematic advantage |
| 6-10 | 0.92-1.37 | NO systematic advantage |
| 11-15 | 0.84-1.21 | slight MARGINAL at m=11 |
| 16-21 | 0.88-1.01 | slight MARGINAL |
| 22-25 | 0.91-0.99 | MARGINAL but within noise |
| 26 | 0.44 | one data point (n=86) |

Only m=18 and m=26 show a ratio below 0.5, but m=26 has only one survivor (n=86), making this statistically meaningless. The m=18 case has 4 survivors with mean quality 0.199, which is within normal variation.

**Conclusion: survival is not correlated with approximation quality.** The thread-to-approximation bridge does not exist in the naive form.

## Part D: Convergent Denominator Proximity

**All entries show k=0, nearest_q=1, distance=0.** This is a code artifact: since q_0 = 1, every integer n is exactly a multiple of q_0 = 1. The Part D output is uninformative because all n < q_2 = 10 use q_0 = 1, and larger n still find q_0 = 1 gives |n - n*1| = 0.

The correct question would be: are survivors close to multiples of HIGHER convergent denominators (q_2 = 10, q_3 = 93, etc.)? Since max survivor n = 95, and q_3 = 93, we should check if any survivors are near 93. Indeed, n=95 (a survivor at m=22,23) satisfies |95 - 93| = 2, which is close to q_3. But n=86 satisfies |86 - 93| = 7, not particularly close. The data doesn't show a pattern.

## Part E: 5-adic Structure (THE KEY FINDING)

This is the most important part of the experiment. Every survivor at level m survives through ALL m levels of the 5-adic filtration (max_surv_j = m). This confirms the 0-or-1 branching: if a thread survives to the end, it survives at every intermediate level.

The 5-adic valuation v_5(T_j) = j-1 grows linearly with the depth. At m=26, the surviving thread for n=86 has:
- T_26 = 4 * 5^25 ~ 1.19 * 10^18
- n mod T_26 = 86

This means n=86 is determined modulo a number of size ~10^18. But this does NOT force a good rational approximation to theta. The constraint is:
- 2^86 mod 10^26 has all 26 digits nonzero

This is a constraint on 2^86 in the 10-adic integers, not a constraint on log10(2) in the reals. The 5-adic chain constrains the MULTIPLICATIVE structure of 2^n mod 10^m, not the ADDITIVE structure of n*theta mod 1.

**The gap in Strategy B:** The thread survival constrains 2^n (mod 10^m), which is a 10-adic statement. Converting this to a constraint on log10(2) (an archimedean quantity) requires comparing 10-adic and archimedean absolute values. This is exactly the product formula / global-to-local comparison that Baker's theorem provides. But the constraint is on 2^n, not on n*theta. The relationship is:

2^n mod 10^m = 2^n mod 2^m * 2^n mod 5^m

The constraint "all digits nonzero" is on the combined 10-adic expansion, which involves BOTH the 2-adic and 5-adic parts. It does NOT reduce to a single linear form in logarithms.

## Part F: Irrationality Exponent

**No survivor achieves mu > 1.3.** The maximum irrationality exponent observed:

| n | mu | note |
|---|------|------|
| 20 | 1.296 | best among all survivors |
| 40 | 0.865 | decent but still < 1 |
| 30 | 1.022 | n=30 has frac(30*theta) ~ 0.031, close to 0 |

The Roth bound (mu <= 2 for all but finitely many n) is never even approached. Baker-type bounds would require mu > ~3.57 to be violated. The actual mu values are all below 1.3, indicating that survivor n values produce approximations of quality ~ n^{-1.3} at best, compared to the generic quality ~ n^{-1}.

**Conclusion: The irrationality exponent is far from the Baker threshold.** The thread-to-approximation strategy cannot produce a contradiction with known irrationality measure bounds.

## Why Strategy B Fails

The core issue is a **category error**. Thread survival constrains 2^n in the 10-adic integers (a multiplicative/digit condition), while rational approximation quality measures n*theta in the reals (an additive/metric condition). These are related but not equivalent:

1. **Thread survival says:** 2^n mod 10^m avoids the "zero-digit set" at every level
2. **Good approximation says:** n*theta is very close to an integer

Connection: n*theta = log10(2^n), so frac(n*theta) = frac(log10(2^n)). This tells us the LEADING digits of 2^n (via Benford's law), not the TRAILING digits. Thread survival constrains trailing digits (mod 10^m), while approximation quality constrains leading digits (frac of log).

These are essentially independent constraints. Knowing all trailing digits of 2^n tells you nothing about how close n*log10(2) is to an integer.

## What DOES Thread Survival Force?

Thread survival at depth m forces:
1. 2^n mod 10^m is in a specific set S_m of size |S_m| = 9^m (zeroless m-digit numbers)
2. n ≡ r_m (mod T_m) for a specific residue r_m (the unique thread that survives)
3. The fractional part frac(n*theta) lies in F_m (the zeroless set on the circle)

Condition 3 constrains frac(n*theta) to a set of measure ~0.9^m, but this set is spread across [0,1) in ~9^m tiny intervals. Landing in this set does not require n*theta to be close to an integer, just to avoid certain thin strips.

## Implications for the Proof Strategy

**Strategy B (thread-to-approximation) is dead in its naive form.** Survival does not force exceptional rational approximation. The bridge from 10-adic constraints to archimedean approximation quality does not exist at the level of individual survivor n values.

**What remains viable:**
- **Strategy C (coboundary/bounded remainder):** Still supported by Exp 25-26. The O(1) discrepancy in the transition zone is explained by low orbit variation, not by approximation quality.
- **Exp 26's zero-boundary-crossing argument:** For large m, the orbit in the transition zone crosses zero boundaries of F_m. This is a GEOMETRIC statement about the orbit, not an approximation-quality statement about individual n.
- **A modified Strategy B:** Instead of asking whether individual survivor n force good approximation, ask whether the EXISTENCE of ANY survivor in [m, m+L) forces a structural constraint. The constraint is not on |n*theta - p| but on the JOINT distribution of trailing and leading digits of 2^n.
