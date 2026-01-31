#!/usr/bin/env python3
"""
Experiment 22: Additive Fourier Transform and Minor-Arc Decay Test

Tests GPT Approach 3B's key prediction:
  In ADDITIVE Fourier on Z/5^m Z, the coefficients hat(f_m)(a) decay
  exponentially in (m - v_5(a)), i.e., in the number of nonzero 5-adic
  digits of the frequency a.

This is the "Mauduit-Rivat minor-arc decay" prediction.

Parts:
  A) Compute additive Fourier transform of f_m on Z/5^m Z
  B) Group |hat(f_m)(a)| by v_5(a) and check for exponential decay
  C) Check whether the additive Fourier approach gives a useful error bound
  D) Compare additive vs multiplicative Fourier spectra
  E) 5x5 transfer matrix extraction (if feasible)
"""

import numpy as np
from collections import defaultdict

def compute_orbit_5adic(m):
    """Compute the full orbit of 2^n mod 5^m, starting at 2^m mod 5^m."""
    mod5 = 5**m
    T = 4 * 5**(m-1)
    orbit = [0] * T
    u = pow(2, m, mod5)  # 2^m mod 5^m
    for i in range(T):
        orbit[i] = u
        u = (2 * u) % mod5
    return orbit, T, mod5

def is_zeroless_via_10m(u, m):
    """Check if 2^m * u mod 10^m has no zero digit."""
    mod10 = 10**m
    x = (pow(2, m, mod10) * u) % mod10  # need u mod 5^m -> x mod 10^m via CRT
    # Actually, x = 2^m * u. But u is mod 5^m, and 2^m * u mod 10^m
    # We need to be careful: 2^m * u mod 10^m depends on u mod 5^m (since 2^m mod 2^m = 0)
    # By CRT: x mod 2^m = 0, x mod 5^m = 2^m * u mod 5^m
    # So x = CRT(0 mod 2^m, 2^m*u mod 5^m) mod 10^m
    # But 2^m * u mod 10^m = 2^m * u (if we take u to be the rep in [0, 5^m))
    # This works since 2^m * u < 2^m * 5^m = 10^m when u < 5^m
    # Wait, u can be up to 5^m - 1, so 2^m * (5^m - 1) = 10^m - 2^m < 10^m. OK.
    x = (pow(2, m) * u) % (10**m)
    for _ in range(m):
        if x % 10 == 0:
            return False
        x //= 10
    return True

def v5(n):
    """5-adic valuation of n."""
    if n == 0:
        return float('inf')
    v = 0
    while n % 5 == 0:
        n //= 5
        v += 1
    return v

print("=" * 70)
print("EXPERIMENT 22: ADDITIVE FOURIER TRANSFORM ON Z/5^m Z")
print("=" * 70)

# =====================================================================
# Part A: Compute additive Fourier transform of f_m
# =====================================================================
print("\n### Part A: Additive Fourier transform ###\n")

C_const = 1 / np.log10(2)

for m in range(2, 10):
    mod5 = 5**m
    T = 4 * 5**(m-1)  # orbit period = phi(5^m)

    # Build f_m on Z/5^m Z
    # f_m(u) = 1 if 2^m * u mod 10^m has all digits nonzero, 0 otherwise
    # We only define f_m on (Z/5^m Z)^* (the orbit covers exactly these elements)
    # For u not coprime to 5, f_m(u) = 0 (or undefined; set to 0)

    f = np.zeros(mod5)
    twom = pow(2, m)
    mod10 = 10**m
    survivor_count = 0
    for u in range(mod5):
        if u % 5 == 0:
            continue  # u not in (Z/5^m Z)^*
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
    phi_5m = T  # phi(5^m) = 4 * 5^{m-1}

    # Additive Fourier transform: hat(f)(a) = (1/5^m) * sum_u f(u) * e(-au/5^m)
    # Use FFT on Z/5^m Z
    F_hat = np.fft.fft(f) / mod5  # DFT normalized by 5^m

    # F_hat[0] = mean of f over Z/5^m Z = survivor_count / 5^m = rho * phi(5^m) / 5^m
    # = rho * (4/5)
    print(f"m={m}: 5^m={mod5}, T={T}, survivors={survivor_count}, rho={rho:.6f}, "
          f"hat(f)(0)={F_hat[0].real:.6f}, rho*4/5={rho*4/5:.6f}")

print("\n(hat(f)(0) should equal rho * phi(5^m) / 5^m = rho * 4/5)")

# =====================================================================
# Part B: Group by v_5(a) and check for exponential decay
# =====================================================================
print("\n### Part B: |hat(f_m)(a)| / rho grouped by v_5(a) ###\n")

results_by_m = {}

for m in range(2, 10):
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

    # Group non-DC coefficients by v_5(a)
    bands = defaultdict(list)
    for a in range(1, mod5):
        v = min(v5(a), m)
        bands[v].append(abs(F_hat[a]))

    results_by_m[m] = {}
    print(f"m={m} (rho={rho:.6f}):")
    print(f"  {'v_5':>4s}  {'count':>8s}  {'max|F|':>12s}  {'max/rho':>10s}  {'mean|F|':>12s}  {'l1':>12s}")
    for v in sorted(bands.keys()):
        coeffs = np.array(bands[v])
        mx = np.max(coeffs)
        mn = np.mean(coeffs)
        l1 = np.sum(coeffs)
        k = m - v  # number of nonzero 5-adic digits
        results_by_m[m][v] = (len(coeffs), mx, mx/rho, mn, l1)
        print(f"  {v:4d}  {len(coeffs):8d}  {mx:12.8f}  {mx/rho:10.6f}  {mn:12.8f}  {l1:12.6f}  [k={k}]")
    print()

# =====================================================================
# Part B2: Decay rate analysis
# =====================================================================
print("\n### Part B2: Exponential decay analysis ###\n")
print("For each v_5 = v, the 'depth' k = m - v counts nonzero 5-adic digits.")
print("GPT predicts: max|hat(f)(a)|/rho ~ C * 5^{-delta*k}\n")

# For each m, extract max|hat(f)(a)|/rho at each depth k = m - v
# Then look at how this ratio depends on k (should decay exponentially)
print(f"{'m':>3s}  {'k=1':>10s}  {'k=2':>10s}  {'k=3':>10s}  {'k=4':>10s}  {'k=5':>10s}  {'k=6':>10s}")
print("-" * 75)

for m in range(2, 10):
    line = f"{m:3d}  "
    for k in range(1, 7):
        v = m - k
        if v >= 0 and v in results_by_m[m]:
            _, mx, ratio, _, _ = results_by_m[m][v]
            line += f"{ratio:10.6f}  "
        else:
            line += f"{'---':>10s}  "
    print(line)

print("\nIf decay exists, each column should stabilize and columns further right should be smaller.")

# =====================================================================
# Part C: Additive Fourier error bound for transition zone
# =====================================================================
print("\n### Part C: Additive Fourier error bound ###\n")

print("N_m(L) = sum_a hat(f)(a) * S_L(a), where S_L(a) = sum_{i<L} e(a*2^i/5^m)")
print("Main term: hat(f)(0) * L = rho * (4/5) * L")
print("Error = sum_{a!=0} hat(f)(a) * S_L(a)\n")

print(f"{'m':>3s}  {'L':>4s}  {'actual_N':>10s}  {'main':>10s}  {'actual_err':>12s}  "
      f"{'triv_bnd':>12s}  {'ratio':>8s}")
print("-" * 80)

for m in range(2, 9):
    mod5 = 5**m
    T = 4 * 5**(m-1)
    L = int(np.ceil(C_const * m))

    # Build f on orbit (need to know orbit order)
    orbit, _, _ = compute_orbit_5adic(m)
    mod10 = 10**m
    twom = pow(2, m)

    # f_m on the orbit
    f_orbit = []
    for u in orbit:
        x = (twom * u) % mod10
        zl = True
        xx = x
        for _ in range(m):
            if xx % 10 == 0:
                zl = False
                break
            xx //= 10
        f_orbit.append(1.0 if zl else 0.0)

    actual_N = sum(f_orbit[:L])
    rho = sum(f_orbit) / T

    # Build f on Z/5^m Z (same as before)
    f = np.zeros(mod5)
    for u in range(mod5):
        if u % 5 == 0:
            continue
        x = (twom * u) % mod10
        zl = True
        xx = x
        for _ in range(m):
            if xx % 10 == 0:
                zl = False
                break
            xx //= 10
        f[u] = 1.0 if zl else 0.0

    F_hat = np.fft.fft(f) / mod5

    # Compute S_L(a) = sum_{i=0}^{L-1} e(a * 2^i / 5^m)
    # The orbit elements are u_i = 2^{m+i} mod 5^m = 2^m * 2^i mod 5^m
    # So a * u_i / 5^m mod 1 = a * 2^m * 2^i / 5^m mod 1
    # S_L(a) with the right phase: sum_{i<L} e(a * 2^m * 2^i / 5^m)
    # But in our additive formulation: N_m(L) = sum_{i<L} f(u_i) where u_i = orbit[i]
    # = sum_a hat(f)(a) * sum_{i<L} e(a * orbit[i] / 5^m)

    # Compute S_L(a) for each a
    S_L = np.zeros(mod5, dtype=complex)
    for i in range(L):
        u_i = orbit[i]
        phases = np.exp(2j * np.pi * np.arange(mod5) * u_i / mod5)
        S_L += phases

    # Error using additive decomposition
    main_term = F_hat[0].real * L  # This equals rho * (4/5) * L ... or does it?
    # Actually: sum_a hat(f)(a) * S_L(a) should equal sum_{i<L} f(orbit[i]) = actual_N
    recon = np.sum(F_hat * S_L).real
    additive_error = recon - F_hat[0].real * S_L[0].real

    # Trivial bound: sum_{a!=0} |hat(f)(a)| * |S_L(a)|
    triv = np.sum(np.abs(F_hat[1:]) * np.abs(S_L[1:]))

    actual_err = actual_N - rho * L  # using orbit rho, not additive rho

    print(f"{m:3d}  {L:4d}  {actual_N:10.1f}  {rho*L:10.4f}  {actual_err:12.4f}  "
          f"{triv:12.4f}  {triv/max(abs(actual_err),0.01):8.1f}")

# =====================================================================
# Part D: Compare additive vs multiplicative spectra
# =====================================================================
print("\n### Part D: Additive vs multiplicative spectrum comparison ###\n")

for m in [4, 6, 8]:
    mod5 = 5**m
    T = 4 * 5**(m-1)

    # Multiplicative DFT (on orbit)
    orbit, _, _ = compute_orbit_5adic(m)
    mod10 = 10**m
    twom = pow(2, m)

    f_orbit = []
    for u in orbit:
        x = (twom * u) % mod10
        zl = True
        xx = x
        for _ in range(m):
            if xx % 10 == 0:
                zl = False
                break
            xx //= 10
        f_orbit.append(1.0 if zl else 0.0)

    F_mult = np.fft.fft(f_orbit) / T  # multiplicative DFT

    # Additive DFT (on Z/5^m Z)
    f_add = np.zeros(mod5)
    for u in range(mod5):
        if u % 5 == 0:
            continue
        x = (twom * u) % mod10
        zl = True
        xx = x
        for _ in range(m):
            if xx % 10 == 0:
                zl = False
                break
            xx //= 10
        f_add[u] = 1.0 if zl else 0.0

    F_addit = np.fft.fft(f_add) / mod5  # additive DFT

    # Compare key statistics
    mult_l1 = np.sum(np.abs(F_mult[1:]))
    mult_max = np.max(np.abs(F_mult[1:]))
    mult_l2 = np.sqrt(np.sum(np.abs(F_mult[1:])**2))

    add_l1 = np.sum(np.abs(F_addit[1:]))
    add_max = np.max(np.abs(F_addit[1:]))
    add_l2 = np.sqrt(np.sum(np.abs(F_addit[1:])**2))

    rho = sum(f_orbit) / T
    print(f"m={m}: rho={rho:.6f}")
    print(f"  Multiplicative: l1={mult_l1:.4f}, l2={mult_l2:.6f}, max={mult_max:.6f}, max/rho={mult_max/rho:.4f}")
    print(f"  Additive:       l1={add_l1:.4f}, l2={add_l2:.6f}, max={add_max:.6f}, max/rho={add_max/rho:.4f}")
    print(f"  Ratio l1(add/mult): {add_l1/mult_l1:.4f}")
    print()

# =====================================================================
# Part E: Minor arc decay rate fit
# =====================================================================
print("\n### Part E: Fit decay rate delta for minor-arc bound ###\n")
print("Model: max|hat(f)(a)|/rho <= C * 5^{-delta*k} where k = m - v_5(a)\n")

# Collect (k, max_ratio) pairs across all m
all_data = defaultdict(list)
for m in range(2, 10):
    for v, (count, mx, ratio, mn, l1) in results_by_m[m].items():
        k = m - v
        if k >= 1:
            all_data[k].append(ratio)

print(f"{'k':>3s}  {'n_obs':>6s}  {'max_ratio':>12s}  {'mean_ratio':>12s}  {'log5(ratio)':>12s}")
print("-" * 55)
ks = []
log_ratios = []
for k in sorted(all_data.keys()):
    ratios = all_data[k]
    mx = max(ratios)
    mn = np.mean(ratios)
    lr = np.log(mx) / np.log(5)
    ks.append(k)
    log_ratios.append(lr)
    print(f"{k:3d}  {len(ratios):6d}  {mx:12.6f}  {mn:12.6f}  {lr:12.4f}")

# Fit delta from log5(max_ratio) = log5(C) - delta * k
if len(ks) >= 3:
    x = np.array(ks, dtype=float)
    y = np.array(log_ratios)
    n = len(x)
    sx, sy, sxx, sxy = np.sum(x), np.sum(y), np.sum(x*x), np.sum(x*y)
    b = (n*sxy - sx*sy) / (n*sxx - sx*sx)
    a = (sy - b*sx) / n
    r2 = 1 - np.sum((y - (a + b*x))**2) / np.sum((y - np.mean(y))**2)
    delta = -b
    C_fit = 5**a

    print(f"\nFitted: max|hat(f)(a)|/rho ~ {C_fit:.4f} * 5^({-delta:+.4f} * k)")
    print(f"delta = {delta:.4f}")
    print(f"R^2 = {r2:.4f}")

    if delta > 0:
        print(f"\n>>> MINOR-ARC DECAY CONFIRMED: delta = {delta:.4f} <<<")
        print(f">>> Additive Fourier coefficients decay at rate 5^(-{delta:.3f} * k) per nonzero 5-adic digit <<<")
    else:
        print(f"\n>>> MINOR-ARC DECAY FAILS: delta = {delta:.4f} (not positive) <<<")

print("\n" + "=" * 70)
print("EXPERIMENT 22 COMPLETE")
print("=" * 70)
