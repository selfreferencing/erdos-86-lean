# GPT Prompt: Sieve-Theoretic Upper Bound for Zeroless Powers of 2

## Role

You are a research mathematician specializing in sieve methods, combinatorial number theory, and the Selberg/Brun sieve. I need your help applying sieve theory to prove finiteness in the Erdos 86 conjecture.

## Problem Background

**The Conjecture.** The set A = {n >= 1 : 2^n has no digit 0 in base 10} is finite. Computationally, A has 35 elements with largest element 86.

**What We Have Proved.** (Full details below.) The set A has natural density zero, via the 5-adic orbit structure of 2^n mod 10^m.

**The remaining step.** Prove that for large m, the "small survivor count" |S_m intersect [0, C*m]| = 0, where S_m is the set of level-m survivors (orbit positions whose last m digits are all nonzero), C = 1/log10(2) ~ 3.322, and m is the digit count. This implies finiteness.

## The Sieve Setup

Here is the precise sieve formulation.

**The ambient set.** Fix m. The "population" is the set of orbit indices {0, 1, 2, ..., T_m - 1} where T_m = 4 * 5^{m-1}. We want to sieve down to the survivor set S_m, counting how many survivors fall in a short initial interval [0, L) where L = ceil(C * m).

**The sieve conditions.** For each digit position j = 1, 2, ..., m, define the "killed set":

K_j = {i in Z/T_m Z : the j-th digit of the orbit element at index i is 0}

The survivor set is:

S_m = {0, 1, ..., T_m - 1} \ (K_1 union K_2 union ... union K_m)

or equivalently S_m = intersection of the complements of all K_j.

**The sieve parameters:**

- Population: N = T_m = 4 * 5^{m-1}
- Number of sieve conditions: m
- Size of each killed set: |K_j| = T_m / 10 (exactly 1/10 of the orbit has digit j equal to 0)
  - More precisely, |K_j| = T_m * (1/10) because there are exactly T_j/10 values of n mod T_j that give the j-th digit = 0, and each such residue class has T_m/T_j representatives in [0, T_m)
- The sieve density per condition: omega_j = 1/10

**The divisibility chain.** The periods T_1 | T_2 | ... | T_m form a strict divisibility chain:
- T_1 = 4
- T_j = 5 * T_{j-1} for j >= 2
- So T_j | T_{j+1} | ... | T_m

The killed set K_j is periodic with period T_j (the j-th digit depends only on n mod T_j). So K_j is a union of T_m / T_j cosets of the subgroup T_j * Z in Z/T_m Z.

**This is a nested sieve:** The conditions refine each other. K_j is periodic with period T_j, and T_j | T_{j+1}, so K_{j+1} refines K_j in the sense that K_{j+1}'s periodicity is a multiple of K_j's.

## Pairwise Densities (The "Level of Distribution")

For a sieve to work, we need to know the pairwise intersection sizes |K_j intersect K_k|. If the conditions were independent, we'd have |K_j intersect K_k| = N * (1/10)^2 = N/100.

**Empirical data (Experiment 19).** We computed joint/(marginal * marginal) ratios for digit conditions in the generic zone (past the transition zone):

For m = 7, scanning 999 orbit elements:

| Pair      | Joint/Product | Comment                     |
|-----------|---------------|-----------------------------|
| (d_j, d_j)  | ~1.11      | Self-correlation = 1/0.9    |
| (d_j, d_{j+1}) | ~1.00  | Adjacent: independent       |
| (d_j, d_{j+2}) | ~1.00  | Skip-1: independent         |
| (d_j, d_{j+k}) for k>=2 | ~1.00 | All non-adjacent: independent |

The pairwise independence is remarkably clean. The only deviation from independence is the trivial self-correlation.

**Why near-independence holds.** Digit j depends on n mod T_j. Digit j+1 depends on n mod T_{j+1} = 5*T_j. By CRT, specifying n mod T_j constrains n mod T_{j+1} to one of 5 cosets. Within each coset, digit j+1 takes each value with equal probability (since the multiplicative structure of 2 mod 5 is a primitive root). So conditional on digit j, digit j+1 is uniformly distributed over {0,1,...,9}, making the conditions independent.

**This is not quite exact** because the condition "digit j nonzero" (not just "digit j = specific value") introduces a mild correlation. The killed set K_{j+1} intersected with K_j^c (survivors of digit j) has size exactly |K_{j+1} intersect K_j^c| = (T_m/T_{j+1}) * |{residues mod T_{j+1} with digit j nonzero and digit j+1 = 0}|. Since digit j+1 = 0 is independent of digit j's value (by the primitive root argument), this equals (9/10) * (1/10) * T_m = 9*T_m/100.

## What I Need from Sieve Theory

### The Upper Bound Problem

I want to prove:

|S_m intersect [0, L)| <= C_1 * L * (9/10)^m + error

where C_1 is an absolute constant and error is o(1) as m -> infinity, for L = ceil(3.322 * m).

Since L * (9/10)^m = 3.322 * m * 0.9^m -> 0 exponentially, this gives |S_m intersect [0, L)| = 0 for large m.

### The Sieve Framework

**Selberg sieve setup.** We want to estimate from above:

S([0,L), K_1, ..., K_m) = |{i in [0,L) : i not in K_j for j = 1,...,m}|

The standard Selberg upper bound sieve gives:

S <= L * Product(1 - 1/10) + error from pairwise terms

where the error involves the "remainder terms" R_d = |A_d| - (omega(d)/d) * L, summed over squarefree products of the sieve primes.

### Specific Questions

1. **Does the Selberg sieve apply here?** The sieve conditions are not indexed by actual primes but by digit positions. The "moduli" are T_1, T_2, ..., T_m with the divisibility chain T_j | T_{j+1}. Can the Selberg or Brun sieve be adapted to this chain structure?

2. **What is the "dimension" of this sieve?** In classical sieve theory, the dimension kappa is defined by sum_{p < z} omega(p)/p ~ kappa * log(log z). Here, the "primes" are the digit positions j = 1, ..., m, each with density 1/10. The sum is sum_{j=1}^{m} 1/10 = m/10, which grows linearly. This seems like a high-dimensional sieve. Is Brun's combinatorial sieve or the Selberg sieve more appropriate?

3. **The short interval problem.** We're sieving [0, L) with L = O(m), while the moduli T_j can be as large as T_m ~ 5^m. So L << T_m for large m. The sieve remainder terms involve |{i in [0,L) : i in K_j}| vs the expected count L/10. For the last few digits (j close to m), the period T_j is much larger than L, so the actual count could deviate significantly from the expected value. How does sieve theory handle moduli larger than the sieving range?

4. **Can we use the pairwise independence?** The empirical data shows near-perfect pairwise independence of the digit conditions. Classical sieves (Brun, Selberg) use pairwise (or higher-order) correlations to bound the sifted set. Since our pairwise correlations are ~1.0, the "level of distribution" should be excellent. Can you quantify this?

5. **The Rosser-Iwaniec sieve?** For sieve problems where the moduli form a chain (or more generally have restricted factorization), the Rosser-Iwaniec linear sieve gives sharper bounds. Is our chain T_1 | T_2 | ... | T_m amenable to this approach?

## Key Data

**Survivor counts and densities:**

| m  | T_m           | Z_m       | Z_m/T_m     | (9/10)^m   |
|----|---------------|-----------|-------------|------------|
| 1  | 4             | 4         | 1.000       | 0.900      |
| 2  | 20            | 18        | 0.900       | 0.810      |
| 3  | 100           | 81        | 0.810       | 0.729      |
| 4  | 500           | 364       | 0.728       | 0.656      |
| 5  | 2,500         | 1,638     | 0.655       | 0.590      |
| 6  | 12,500        | 7,371     | 0.590       | 0.531      |
| 7  | 62,500        | 33,170    | 0.531       | 0.478      |
| 8  | 312,500       | 149,268   | 0.478       | 0.430      |
| 9  | 1,562,500     | 671,701   | 0.430       | 0.387      |

Note: Z_m/T_m converges to (9/10)^m from above, with ratio Z_m/(T_m * 0.9^m) -> constant ~ 1.10.

**Exact counts of small survivors (i < C*m, where C = 3.322):**

| m  | L = ceil(C*m) | |S_m intersect [0,L)| | Main term L*rho |
|----|---------------|----------------------|-----------------|
| 1  | 4             | 4                    | 4.000           |
| 2  | 7             | 5                    | 6.300           |
| 3  | 10            | 3                    | 8.100           |
| 4  | 14            | 4                    | 10.192          |
| 5  | 17            | 7                    | 11.138          |
| 6  | 20            | 4                    | 11.794          |
| 7  | 24            | 5                    | 12.737          |
| 8  | 27            | 9                    | 12.897          |
| 9  | 30            | 9                    | 12.897          |

The exact count fluctuates between 3 and 9 while the main term (L * Z_m/T_m) stabilizes near 13. The exact count is ALWAYS well below the main term.

**Transition zone data (Experiment 19).** For each m, there are only 3-4 candidate exponents n with D(n) = m:

| m  | Width | Candidates and outcomes               |
|----|-------|---------------------------------------|
| 4  | 4     | n=10(x), 11(x), 12(x), 13(Z)        |
| 7  | 4     | n=20(x), 21(x), 22(x), 23(x) [gap]  |
| 10 | 4     | n=30(x), 31(Z), 32(Z), 33(Z)        |
| 12 | 3     | n=37(Z), 38(x), 39(Z)               |

(Z = zeroless/survivor, x = has a zero digit, x@k = first zero at digit k)

## What I Am Looking For

1. A sieve-theoretic upper bound for |S_m intersect [0, C*m]| that goes to zero as m -> infinity.
2. Identification of which sieve method (Brun's combinatorial, Selberg quadratic, Rosser-Iwaniec linear, or other) is most appropriate for the chain structure T_1 | T_2 | ... | T_m.
3. The key obstacle: how to handle "large moduli" (T_j >> L for j close to m) in the sieve remainder terms.
4. Whether the near-perfect pairwise independence gives a sufficient "level of distribution" to close the argument.
5. If the standard sieve gives a bound that is too large (e.g., O(m * 0.9^m) with a constant too big), what refinements would help?
