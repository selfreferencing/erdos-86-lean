#!/usr/bin/env python3
"""
Experiment 24: Investigating the 0.0877 Additive Fourier Plateau

Exp 22 found that max|hat(f_m)(a)| / rho_m plateaus at ~0.0877 for depth
k = m - v_5(a) >= 3. This experiment investigates:

  A) High-precision measurement of the plateau constant across m
  B) Which specific frequency a achieves the maximum? Structure of argmax.
  C) Does the constant relate to known constants? (4/45, 2/5*1/9, etc.)
  D) Transfer matrix analysis: compute the 5x5 matrices for each digit
     and check if operator norms explain the plateau
  E) Does the plateau depend on the 5-adic digits of a?
     (e.g., does a with digits [1,0,...,0] differ from [3,2,...,1]?)
"""

import numpy as np
from collections import defaultdict
from fractions import Fraction

def v5(n):
    """5-adic valuation of n."""
    if n == 0:
        return float('inf')
    v = 0
    while n % 5 == 0:
        n //= 5
        v += 1
    return v

def digits_5adic(a, m):
    """Return the 5-adic digits of a mod 5^m (least significant first)."""
    digits = []
    for _ in range(m):
        digits.append(a % 5)
        a //= 5
    return digits

print("=" * 70)
print("EXPERIMENT 24: INVESTIGATING THE 0.0877 PLATEAU CONSTANT")
print("=" * 70)

# =====================================================================
# Part A: High-precision plateau measurement
# =====================================================================
print("\n### Part A: High-precision plateau constant across m ###\n")

C_const = 1 / np.log10(2)

plateau_data = {}

for m in range(2, 11):
    mod5 = 5**m
    T = 4 * 5**(m-1)

    # Build f on Z/5^m Z
    f = np.zeros(mod5)
    twom = pow(2, m)
    mod10 = 10**m
    survivor_count = 0
    for u in range(mod5):
        if u % 5 == 0:
            continue
        x = (twom * u) % mod10
        zeroless = True
        xx = x
        for _ in range(m):
            if xx % 10 == 0:
                zeroless = False
                break
            xx //= 10
        f[u] = 1.0 if zeroless else 0.0
        if zeroless:
            survivor_count += 1

    rho = survivor_count / T

    F_hat = np.fft.fft(f) / mod5

    # Group by depth k = m - v_5(a)
    max_by_k = defaultdict(float)
    argmax_by_k = defaultdict(int)

    for a in range(1, mod5):
        v = min(v5(a), m)
        k = m - v
        mag = abs(F_hat[a])
        if mag > max_by_k[k]:
            max_by_k[k] = mag
            argmax_by_k[k] = a

    plateau_data[m] = {}
    print(f"m={m} (rho={rho:.8f}):")
    for k in sorted(max_by_k.keys()):
        ratio = max_by_k[k] / rho
        plateau_data[m][k] = (max_by_k[k], ratio, argmax_by_k[k])
        if k >= 2 and k <= 8:
            print(f"  k={k}: max|hat(f)|/rho = {ratio:.10f}  (argmax a={argmax_by_k[k]})")
    print()

# Extract the plateau values for k >= 3
print("\nPlateau values for k >= 3 across m:\n")
print(f"{'m':>3s}  {'k=3':>14s}  {'k=4':>14s}  {'k=5':>14s}  {'k=6':>14s}  {'k=7':>14s}")
print("-" * 80)
for m in range(5, 11):
    line = f"{m:3d}  "
    for k in range(3, 8):
        if k in plateau_data[m]:
            _, ratio, _ = plateau_data[m][k]
            line += f"{ratio:14.10f}  "
        else:
            line += f"{'---':>14s}  "
    print(line)

# =====================================================================
# Part B: Structure of argmax frequency
# =====================================================================
print("\n### Part B: Structure of the argmax frequency ###\n")
print("For each (m, k), what are the 5-adic digits of the frequency achieving the max?\n")

for m in range(4, 10):
    print(f"m={m}:")
    for k in sorted(plateau_data[m].keys()):
        if k < 2 or k > m:
            continue
        _, ratio, a_max = plateau_data[m][k]
        digits = digits_5adic(a_max, m)
        v = m - k
        # The first v digits should be 0 (since v_5(a) = v)
        print(f"  k={k} (v_5={v}): a={a_max}, digits={digits}, ratio={ratio:.8f}")
    print()

# =====================================================================
# Part C: Test candidate closed forms for the plateau
# =====================================================================
print("\n### Part C: Candidate closed forms for 0.0877... ###\n")

# Collect the best plateau value
plateau_values = []
for m in range(6, 11):
    for k in range(3, min(m, 8)):
        if k in plateau_data[m]:
            _, ratio, _ = plateau_data[m][k]
            plateau_values.append(ratio)

if plateau_values:
    best = max(plateau_values)
    print(f"Best plateau value: {best:.12f}\n")

    # Test various candidates
    candidates = [
        ("4/45", 4/45),
        ("2/23", 2/23),
        ("1/11.4", 1/11.4),
        ("(9/10)^m * C for various C", None),
        ("2/(5*sqrt(5))", 2/(5*np.sqrt(5))),
        ("1/(2*pi*sqrt(5/3))", 1/(2*np.pi*np.sqrt(5/3))),
        ("4/(5*9)", 4/45),
        ("(1-1/10)*(1-1/5)/5", 0.9*0.8/5),
        ("sin(pi/5)/(5*pi/5)", np.sin(np.pi/5)/(np.pi)),
        ("2*sin(pi/10)/pi", 2*np.sin(np.pi/10)/np.pi),
        ("1/(4*sqrt(pi))", 1/(4*np.sqrt(np.pi))),
        ("(2/pi)*sin(pi/10)", (2/np.pi)*np.sin(np.pi/10)),
        ("1/sqrt(130)", 1/np.sqrt(130)),
        ("(4/5)*(1/9)", (4/5)*(1/9)),
        ("2/(9*sqrt(5))", 2/(9*np.sqrt(5))),
        ("4/(9*5)", 4/45),
    ]

    print(f"{'candidate':>30s}  {'value':>14s}  {'ratio to plateau':>16s}  {'diff':>14s}")
    print("-" * 80)
    for name, val in candidates:
        if val is not None:
            r = val / best
            d = val - best
            print(f"{name:>30s}  {val:14.10f}  {r:16.10f}  {d:14.10f}")

# =====================================================================
# Part D: Transfer matrix analysis
# =====================================================================
print("\n\n### Part D: 5x5 Transfer matrices per digit ###\n")
print("For digit position r (1-indexed), define the digit test:")
print("  d_r(u) = floor(2^{m-r} * u / 5^{r-1}) mod 10")
print("  g_r(u) = 1 if d_r != 0, else 0")
print("")
print("The additive Fourier transform hat(f)(a) factors through the digits of a.")
print("For each 5-adic digit d of a, there is a transfer matrix M_d such that")
print("hat(f)(a) relates to the product of M_{a_r} across r.\n")

# For a single digit position r, the digit condition is:
# g_r(u) = 1 if floor((2^{m-r} * u mod 5^r) / 5^{r-1}) is in {1,..,9} as a digit of 2^m*u
#
# Actually, let's compute this more directly.
# The product structure: f_m(u) = prod_{r=1}^{m} g_r(u)
# where g_r(u) depends on u mod 5^r (the r-th 5-adic "layer").
#
# The Fourier transform of a product that layers in this way can be computed
# recursively: going from 5^{r-1} to 5^r (one 5-adic digit at a time).
#
# Define phi_r(a) = (1/5^r) * sum_{u mod 5^r} [prod_{s=1}^r g_s(u)] * e(-au/5^r)
#
# Then phi_r(a) relates to phi_{r-1}(a') via a transfer matrix when a' = a mod 5^{r-1}.
#
# Let's compute this directly.

for m in [5, 6, 7, 8]:
    print(f"\nm={m}:")
    mod5m = 5**m
    twom = pow(2, m)
    mod10m = 10**m

    # Compute phi_r for r = 1, ..., m
    # phi_r(a) = (1/5^r) * sum_{u=0}^{5^r-1, gcd(u,5)=1} [prod_{s=1}^r g_s(u)] * omega^{-au}
    # where omega = e(1/5^r)

    # We compute this by building up the product iteratively
    for r in range(1, min(m+1, 6)):
        mod5r = 5**r

        # Compute prod_{s=1}^r g_s(u) for each u mod 5^r
        indicator = np.zeros(mod5r)
        for u in range(mod5r):
            if u % 5 == 0:
                continue
            # Check digits 1 through r of 2^m * u
            x = (twom * u) % (10**r)
            ok = True
            xx = x
            for _ in range(r):
                if xx % 10 == 0:
                    ok = False
                    break
                xx //= 10
            indicator[u] = 1.0 if ok else 0.0

        # DFT of indicator on Z/5^r Z
        phi_r = np.fft.fft(indicator) / mod5r

        # For the transfer interpretation, group by the leading 5-adic digit of a
        # a = a_{r-1} * 5^{r-1} + a' where a' = a mod 5^{r-1}
        # For each leading digit d = 0,1,2,3,4, define:
        # M_d[a'] = phi_r(d * 5^{r-1} + a')

        if r >= 2:
            mod5r1 = 5**(r-1)

            # Compute "transfer ratio": for each a mod 5^r with v_5(a) = r-1,
            # compare |phi_r(a)| to |phi_{r-1}(a mod 5^{r-1})|

            # phi_{r-1}
            indicator_prev = np.zeros(mod5r1)
            for u in range(mod5r1):
                if u % 5 == 0:
                    continue
                x = (twom * u) % (10**(r-1))
                ok = True
                xx = x
                for _ in range(r-1):
                    if xx % 10 == 0:
                        ok = False
                        break
                    xx //= 10
                indicator_prev[u] = 1.0 if ok else 0.0

            phi_r1 = np.fft.fft(indicator_prev) / mod5r1

            # For each nonzero digit d, compute the operator norm of the transfer
            transfer_norms = []
            for d in range(1, 5):  # digits 1,2,3,4
                ratios = []
                for aprime in range(mod5r1):
                    if aprime == 0:
                        continue
                    a_full = d * mod5r1 + aprime
                    if abs(phi_r1[aprime]) > 1e-15:
                        r_val = abs(phi_r[a_full]) / abs(phi_r1[aprime])
                        ratios.append(r_val)
                if ratios:
                    transfer_norms.append((d, max(ratios), np.mean(ratios)))

            if transfer_norms:
                print(f"  r={r}: transfer |phi_r(d*5^{{r-1}}+a')|/|phi_{{r-1}}(a')|:")
                for d, mx, mn in transfer_norms:
                    print(f"    digit d={d}: max ratio={mx:.6f}, mean ratio={mn:.6f}")

# =====================================================================
# Part E: Dependence on 5-adic digit pattern of a
# =====================================================================
print("\n\n### Part E: Does max|hat(f)(a)|/rho depend on the digit PATTERN of a? ###\n")
print("For depth k >= 3, do all nonzero digit patterns give the same max ratio,")
print("or does the specific choice of nonzero digits matter?\n")

for m in [7, 8, 9]:
    mod5 = 5**m
    T = 4 * 5**(m-1)

    f = np.zeros(mod5)
    twom = pow(2, m)
    mod10 = 10**m
    survivor_count = 0
    for u in range(mod5):
        if u % 5 == 0:
            continue
        x = (twom * u) % mod10
        zeroless = True
        xx = x
        for _ in range(m):
            if xx % 10 == 0:
                zeroless = False
                break
            xx //= 10
        f[u] = 1.0 if zeroless else 0.0
        if zeroless:
            survivor_count += 1

    rho = survivor_count / T
    F_hat = np.fft.fft(f) / mod5

    print(f"m={m} (rho={rho:.8f}):")

    # For depth k = m (all digits nonzero, i.e., v_5(a) = 0),
    # group by the leading nonzero digit
    for k in [3, 4, m]:
        if k > m:
            continue
        v = m - k

        # Collect all a with v_5(a) = v
        by_leading_digit = defaultdict(list)
        for a in range(1, mod5):
            if v5(a) != v:
                continue
            # The first nonzero digit (from least significant) is at position v
            d_leading = (a // (5**v)) % 5
            by_leading_digit[d_leading].append(abs(F_hat[a]) / rho)

        print(f"  k={k} (v_5={v}):")
        for d in sorted(by_leading_digit.keys()):
            vals = by_leading_digit[d]
            print(f"    leading nonzero digit={d}: count={len(vals):6d}, "
                  f"max={max(vals):.8f}, mean={np.mean(vals):.8f}")

    # Also check: for k=3, what's the structure of the argmax?
    k = 3
    v = m - k
    best_a = None
    best_val = 0
    for a in range(1, mod5):
        if v5(a) != v:
            continue
        mag = abs(F_hat[a]) / rho
        if mag > best_val:
            best_val = mag
            best_a = a

    if best_a is not None:
        digits = digits_5adic(best_a, m)
        print(f"  argmax at k=3: a={best_a}, digits={digits}, ratio={best_val:.10f}")
    print()

# =====================================================================
# Part F: Exact rational computation for small m
# =====================================================================
print("\n### Part F: Exact computation for m=2,3 ###\n")
print("Can we compute hat(f)(a) exactly (as rational/algebraic) for small m?")
print("This might reveal the exact plateau value.\n")

for m in [2, 3, 4]:
    mod5 = 5**m
    twom = 2**m
    mod10 = 10**m
    T = 4 * 5**(m-1)

    # Build f exactly
    f_exact = {}
    survivors = 0
    for u in range(mod5):
        if u % 5 == 0:
            continue
        x = (twom * u) % mod10
        ok = True
        xx = x
        for _ in range(m):
            if xx % 10 == 0:
                ok = False
                break
            xx //= 10
        f_exact[u] = 1 if ok else 0
        if ok:
            survivors += 1

    rho_exact = Fraction(survivors, T)

    # For the maximum: compute |hat(f)(a)|^2 as sum of cos and sin parts
    # hat(f)(a) = (1/5^m) * sum_u f(u) * e(-2*pi*i*a*u/5^m)
    # = (1/5^m) * [sum_u f(u)*cos(2*pi*a*u/5^m) - i*sum_u f(u)*sin(2*pi*a*u/5^m)]

    print(f"m={m}: 5^m={mod5}, T={T}, survivors={survivors}, rho={float(rho_exact):.6f}")

    max_ratio = 0
    best_a = 0
    for a in range(1, mod5):
        re_part = sum(f_exact.get(u, 0) * np.cos(2*np.pi*a*u/mod5) for u in range(mod5))
        im_part = sum(f_exact.get(u, 0) * np.sin(2*np.pi*a*u/mod5) for u in range(mod5))
        mag = np.sqrt(re_part**2 + im_part**2) / mod5
        ratio = mag / float(rho_exact)
        if ratio > max_ratio:
            max_ratio = ratio
            best_a = a

    print(f"  max|hat(f)(a)|/rho = {max_ratio:.12f} at a={best_a}")

    # Check: survivors * max_ratio / 5^m
    print(f"  |hat(f)(a_max)| = {max_ratio * float(rho_exact):.12f}")
    print(f"  |hat(f)(a_max)| * 5^m = {max_ratio * float(rho_exact) * mod5:.6f}")
    print(f"  This equals |sum_u f(u) * e(-2pi*i*a*u/5^m)| = {max_ratio * float(rho_exact) * mod5:.6f}")
    print()

# =====================================================================
# Part G: The Riesz product connection
# =====================================================================
print("\n### Part G: Riesz product structure and plateau ###\n")
print("f_m = g_1 * g_2 * ... * g_m, so hat(f_m) = hat(g_1) * hat(g_2) * ... * hat(g_m)")
print("(convolution on Z/5^m Z)")
print("Each g_r(u) depends on u mod 5^r, so hat(g_r) is supported on multiples of 5^{m-r}")
print("")
print("The plateau may come from the PRODUCT of individual max|hat(g_r)|.\n")

for m in range(3, 9):
    mod5 = 5**m
    twom = pow(2, m)
    mod10 = 10**m
    T = 4 * 5**(m-1)

    # Compute individual digit indicators g_r on Z/5^m Z
    # g_r(u) = 1 if the r-th digit of 2^m * u mod 10^m is nonzero

    individual_maxes = []
    individual_rhos = []

    for r in range(1, m+1):
        g_r = np.zeros(mod5)
        count_ok = 0
        for u in range(mod5):
            if u % 5 == 0:
                continue
            x = (twom * u) % mod10
            # Extract digit r (1-indexed from right)
            d = (x // (10**(r-1))) % 10
            g_r[u] = 1.0 if d != 0 else 0.0
            if d != 0:
                count_ok += 1

        G_hat = np.fft.fft(g_r) / mod5
        rho_r = count_ok / T

        # Max non-DC coefficient
        max_g = 0
        for a in range(1, mod5):
            mag = abs(G_hat[a])
            if mag > max_g:
                max_g = mag

        individual_maxes.append(max_g / rho_r if rho_r > 0 else 0)
        individual_rhos.append(rho_r)

    # Product of individual max|hat(g_r)|/rho_r
    prod_maxes = 1.0
    for mx in individual_maxes:
        prod_maxes *= mx

    # The full f_m max|hat(f)|/rho
    f_full = np.zeros(mod5)
    surv = 0
    for u in range(mod5):
        if u % 5 == 0:
            continue
        x = (twom * u) % mod10
        ok = True
        xx = x
        for _ in range(m):
            if xx % 10 == 0:
                ok = False
                break
            xx //= 10
        f_full[u] = 1.0 if ok else 0.0
        if ok:
            surv += 1

    rho_full = surv / T
    F_full = np.fft.fft(f_full) / mod5
    max_full = max(abs(F_full[a]) for a in range(1, mod5)) / rho_full

    print(f"m={m}: product of max|hat(g_r)|/rho_r = {prod_maxes:.8f}, "
          f"max|hat(f)|/rho = {max_full:.8f}, "
          f"ratio = {max_full/prod_maxes:.8f}")
    print(f"       individual max ratios: {['%.4f' % x for x in individual_maxes]}")

print("\n" + "=" * 70)
print("EXPERIMENT 24 COMPLETE")
print("=" * 70)
