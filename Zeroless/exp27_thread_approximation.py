#!/usr/bin/env python3
"""
Experiment 27: Thread-to-Approximation Test

GPT 4A's Strategy B: does survival of a thread to depth m in the 5-adic tree
force an exponentially good rational approximation to log10(2)?

If so, Baker's theorem on linear forms in logarithms would kill survival at
large m, completing the finiteness proof.

Parts:
  A) Basic approximation quality |n*theta - round(n*theta)| for survivors
  B) 5-adic congruence chain from thread survival
  C) Survivor approximation quality vs generic (statistical comparison)
  D) Convergent denominator proximity
  E) 5-adic valuation of implied approximation denominators
  F) Critical threshold: when does implied irrationality exponent exceed bounds?
"""

import numpy as np
from mpmath import mp, mpf, log, frac as mpfrac
import random

mp.dps = 80  # 80 decimal digits of precision
theta_mp = log(2, 10)  # high-precision log10(2)
theta = float(theta_mp)  # double-precision for fast computation

C_const = 1.0 / theta  # ~ 3.3219

def is_zeroless(x, m):
    """Check if x has no zero digit in its m-digit representation."""
    for _ in range(m):
        if x % 10 == 0:
            return False
        x //= 10
    return True

def digits_zero_free(x, num_digits):
    """Check if the last num_digits digits of x are all nonzero."""
    for _ in range(num_digits):
        if x % 10 == 0:
            return False
        x //= 10
    return True

def find_survivors(m, L=None):
    """Find all surviving orbit indices i < L where 2^{m+i} is m-digit zeroless."""
    if L is None:
        L = int(np.ceil(C_const * m))
    mod_m = 10**m
    survivors = []
    x = pow(2, m, mod_m)
    for i in range(L):
        if is_zeroless(x, m):
            survivors.append(i)
        x = (2 * x) % mod_m
    return survivors

def cf_expansion(x, n_terms=25):
    """Compute continued fraction expansion using mpmath."""
    terms = []
    for _ in range(n_terms):
        a = int(x)
        terms.append(a)
        x = x - a
        if abs(x) < mpf('1e-60'):
            break
        x = 1 / x
    return terms

def convergents(cf):
    """Compute convergents p_n/q_n from continued fraction."""
    convs = []
    p_prev, p_curr = 0, 1
    q_prev, q_curr = 1, 0
    for a in cf:
        p_prev, p_curr = p_curr, a * p_curr + p_prev
        q_prev, q_curr = q_curr, a * q_curr + q_prev
        convs.append((p_curr, q_curr))
    return convs


print("=" * 70)
print("EXPERIMENT 27: THREAD-TO-APPROXIMATION TEST")
print("=" * 70)

# Precompute continued fraction and convergents of theta
cf = cf_expansion(theta_mp, 25)
convs = convergents(cf)
print(f"\nContinued fraction of log10(2): [{cf[0]}; {', '.join(str(a) for a in cf[1:15])}, ...]")
print(f"Convergent denominators: {', '.join(str(q) for _, q in convs[:15])}")

# =====================================================================
# Part A: Basic approximation quality for survivors
# =====================================================================
print("\n### Part A: Approximation quality |n*theta - p| for survivors ###\n")
print("For each m with survivors, compute how well n approximates theta.\n")

print(f"{'m':>3s}  {'n':>4s}  {'i':>3s}  {'|n*th-p|':>12s}  {'frac(n*th)':>12s}  "
      f"{'generic_med':>12s}  {'quality_ratio':>14s}")
print("-" * 80)

all_survivors_by_m = {}

for m in range(2, 28):
    L = int(np.ceil(C_const * m))
    survivors = find_survivors(m, L)
    all_survivors_by_m[m] = survivors

    for i in survivors:
        n = m + i
        # High precision computation
        n_theta = n * theta_mp
        p = int(round(float(n_theta)))
        approx_quality = abs(float(n_theta - p))
        frac_n_theta = float(n_theta - int(n_theta))

        # Generic median: for uniform distribution on [0,0.5], median = 0.25
        generic_med = 0.25
        quality_ratio = approx_quality / generic_med

        print(f"{m:3d}  {n:4d}  {i:3d}  {approx_quality:12.8f}  {frac_n_theta:12.8f}  "
              f"{generic_med:12.8f}  {quality_ratio:14.4f}")

    if len(survivors) == 0:
        print(f"{m:3d}  {'---':>4s}  {'---':>3s}  {'(no survivors)':>12s}")


# =====================================================================
# Part B: 5-adic congruence chain from thread survival
# =====================================================================
print("\n\n### Part B: 5-adic congruence chain for surviving threads ###\n")
print("For each surviving orbit index, trace its residue class through levels.\n")

for m in [6, 10, 15, 20, 26]:
    L = int(np.ceil(C_const * m))
    survivors = find_survivors(m, L)
    if not survivors:
        print(f"m={m}: no survivors")
        continue

    for i in survivors[:3]:  # show up to 3 survivors per m
        n = m + i
        print(f"m={m}, i={i}, n={n}:")
        print(f"  {'j':>3s}  {'T_j':>12s}  {'r_j mod T_j':>12s}  {'2^n mod 10^j':>14s}  "
              f"{'digits':>10s}  {'admissible':>10s}")

        for j in range(1, min(m+1, 20)):
            T_j = 4 * 5**(j-1)
            r_j = i % T_j
            mod_j = 10**j
            val = pow(2, n, mod_j)
            digits_str = str(val).zfill(j)
            admissible = digits_zero_free(val, j)

            print(f"  {j:3d}  {T_j:12d}  {r_j:12d}  {val:14d}  "
                  f"{digits_str:>10s}  {'YES' if admissible else 'NO':>10s}")

            if not admissible:
                print(f"  >>> Thread dies at level {j} <<<")
                break
        print()


# =====================================================================
# Part C: Survivor approximation quality vs generic
# =====================================================================
print("\n### Part C: Survivor vs generic approximation quality ###\n")
print("Statistical comparison: do survivors achieve better-than-random")
print("rational approximation to theta?\n")

random.seed(42)

print(f"{'m':>3s}  {'n_surv':>7s}  {'surv_mean|n*th-p|':>20s}  {'generic_mean':>14s}  "
      f"{'ratio':>8s}  {'surv_better?':>12s}")
print("-" * 75)

for m in range(2, 28):
    L = int(np.ceil(C_const * m))
    survivors = all_survivors_by_m[m]

    if not survivors:
        print(f"{m:3d}  {'0':>7s}  {'---':>20s}")
        continue

    # Survivor approximation qualities
    surv_quals = []
    for i in survivors:
        n = m + i
        n_theta = n * theta_mp
        p = int(round(float(n_theta)))
        surv_quals.append(abs(float(n_theta - p)))

    surv_mean = np.mean(surv_quals)

    # Generic: random n values in the same range [m, m+L)
    generic_quals = []
    for _ in range(200):
        n_rand = m + random.randint(0, max(L-1, 1))
        n_theta = n_rand * theta_mp
        p = int(round(float(n_theta)))
        generic_quals.append(abs(float(n_theta - p)))

    generic_mean = np.mean(generic_quals)
    ratio = surv_mean / generic_mean
    better = "YES" if ratio < 0.8 else ("MARGINAL" if ratio < 1.0 else "NO")

    print(f"{m:3d}  {len(survivors):7d}  {surv_mean:20.8f}  {generic_mean:14.8f}  "
          f"{ratio:8.4f}  {better:>12s}")


# =====================================================================
# Part D: Convergent denominator proximity
# =====================================================================
print("\n\n### Part D: Proximity to convergent denominators ###\n")
print("For each surviving n, how close is it to a multiple of a convergent q_k?\n")

conv_qs = [q for _, q in convs[:15]]

print(f"{'m':>3s}  {'n':>4s}  {'nearest_q_k':>12s}  {'k':>3s}  {'|n - a*q_k|':>14s}  "
      f"{'a':>4s}  {'n mod q_k':>10s}")
print("-" * 65)

for m in range(2, 28):
    survivors = all_survivors_by_m[m]
    for i in survivors:
        n = m + i
        # Find nearest convergent denominator
        best_dist = n
        best_k = 0
        best_a = 0
        best_q = 1
        for k, q in enumerate(conv_qs):
            if q > 2 * n:
                break
            a = round(n / q)
            dist = abs(n - a * q)
            if dist < best_dist:
                best_dist = dist
                best_k = k
                best_a = a
                best_q = q

        print(f"{m:3d}  {n:4d}  {best_q:12d}  {best_k:3d}  {best_dist:14d}  "
              f"{best_a:4d}  {n % best_q:10d}")


# =====================================================================
# Part E: 5-adic valuation of implied approximation
# =====================================================================
print("\n\n### Part E: 5-adic structure of surviving n values ###\n")
print("The thread at level j gives n ≡ m+r_j (mod T_j = 4*5^{j-1}).")
print("At the deepest level j_max where the thread survives, this constrains n")
print("modulo T_{j_max}. What is the 5-adic valuation of this modulus?\n")

def v5(n):
    """5-adic valuation of n."""
    if n == 0:
        return float('inf')
    v = 0
    while n % 5 == 0:
        n //= 5
        v += 1
    return v

print(f"{'m':>3s}  {'n':>4s}  {'max_surv_j':>10s}  {'T_j':>14s}  {'v5(T_j)':>8s}  "
      f"{'n mod T_j':>12s}  {'frac(n*th)':>12s}")
print("-" * 75)

for m in range(2, 28):
    L = int(np.ceil(C_const * m))
    survivors = find_survivors(m, L)

    for i in survivors[:5]:  # up to 5 survivors per m
        n = m + i

        # Find the deepest level at which this thread survives
        max_surv_j = 0
        for j in range(1, m+1):
            T_j = 4 * 5**(j-1)
            mod_j = 10**j
            val = pow(2, n, mod_j)
            if digits_zero_free(val, j):
                max_surv_j = j
            else:
                break

        T_max = 4 * 5**(max_surv_j - 1)
        v5_T = max_surv_j - 1  # v_5(4 * 5^{j-1}) = j-1
        frac_n = float(n * theta_mp - int(n * theta_mp))

        print(f"{m:3d}  {n:4d}  {max_surv_j:10d}  {T_max:14d}  {v5_T:8d}  "
              f"{n % T_max:12d}  {frac_n:12.8f}")


# =====================================================================
# Part F: Implied irrationality exponent
# =====================================================================
print("\n\n### Part F: Implied irrationality exponent ###\n")
print("If |n*theta - p| = n^{-mu}, then mu = -log|n*theta-p|/log(n).")
print("Roth's theorem: mu <= 2 for all but finitely many n.")
print("Baker-type effective bounds give computable thresholds.\n")

print(f"{'m':>3s}  {'n':>4s}  {'|n*th-p|':>14s}  {'-log/log(n)':>14s}  {'mu':>8s}  "
      f"{'exceeds_Roth?':>14s}")
print("-" * 75)

for m in range(2, 28):
    survivors = all_survivors_by_m[m]
    for i in survivors:
        n = m + i
        n_theta = n * theta_mp
        p = int(round(float(n_theta)))
        quality = abs(float(n_theta - p))

        if quality > 0 and n > 1:
            mu = -np.log(quality) / np.log(n)
        else:
            mu = float('inf')

        exceeds = "YES" if mu > 2.0 else "NO"

        print(f"{m:3d}  {n:4d}  {quality:14.10f}  {mu:14.6f}  {mu:8.4f}  "
              f"{exceeds:>14s}")

# Summary
print("\n\n### Summary ###\n")
print("Survivor counts by m:")
for m in range(2, 28):
    surv = all_survivors_by_m[m]
    L = int(np.ceil(C_const * m))
    if surv:
        ns = [m + i for i in surv]
        print(f"  m={m:2d}: {len(surv)} survivors, n = {ns}, L = {L}")
    else:
        print(f"  m={m:2d}: 0 survivors, L = {L}")


print("\n" + "=" * 70)
print("EXPERIMENT 27 COMPLETE")
print("=" * 70)
