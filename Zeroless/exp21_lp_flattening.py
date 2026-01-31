#!/usr/bin/env python3
"""
Experiment 21: l^p Flattening Test for the Bottleneck Lemma

Tests GPT Approach 3A's key prediction:
  ||hat(b_m)||_{l^p} << 5^{-kappa*m} for some p in (1,2) and kappa > 0

If confirmed, this + Holder inequality would close the finiteness gap.

Parts:
  A) Compute ||hat(b_m)||_p for p = 1.0, 1.1, 1.2, 1.5, 2.0 across m = 2..10
  B) Fit kappa(p) from log-linear regression on ||hat(b_m)||_p vs m
  C) Check the critical condition: kappa(p) > 1/q = 1 - 1/p
  D) Multiscale decomposition: l^p norms by v_5 band
  E) The actual Holder bound: ||hat(b_m)||_p * ||D_L||_q vs actual error
"""

import numpy as np
from collections import defaultdict

def compute_orbit(m):
    """Compute the full orbit of 2^n mod 10^m."""
    mod = 10**m
    T = 4 * 5**(m-1)
    orbit = [0] * T
    x = pow(2, m, mod)  # start at 2^m
    for i in range(T):
        orbit[i] = x
        x = (2 * x) % mod
    return orbit, T, mod

def is_zeroless(x, m):
    """Check if x has no zero digit in its m-digit representation."""
    for _ in range(m):
        if x % 10 == 0:
            return False
        x //= 10
    return True

def compute_survivor_indicator(orbit, m):
    """Compute f_m(i) = 1 if orbit[i] is zeroless, 0 otherwise."""
    return np.array([1.0 if is_zeroless(x, m) else 0.0 for x in orbit])

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
print("EXPERIMENT 21: l^p FLATTENING TEST (BOTTLENECK LEMMA)")
print("=" * 70)

# =====================================================================
# Part A: Compute ||hat(b_m)||_p for various p across m = 2..10
# =====================================================================
print("\n### Part A: l^p norms of hat(b_m) ###\n")

p_values = [1.0, 1.1, 1.2, 1.5, 2.0]
results = {}  # results[m] = {p: norm_value}

for m in range(2, 11):
    orbit, T, mod = compute_orbit(m)
    f = compute_survivor_indicator(orbit, m)
    rho = np.mean(f)
    b = f - rho  # mean-zero part

    # DFT of b
    B_hat = np.fft.fft(b) / T  # normalized so hat(b)(0) = 0

    # Non-DC coefficients only
    B_nondc = np.abs(B_hat[1:])

    norms = {}
    for p in p_values:
        if p == float('inf'):
            lp = np.max(B_nondc)
        else:
            lp = np.sum(B_nondc**p) ** (1.0/p)
        norms[p] = lp

    results[m] = norms
    print(f"m={m:2d}  T={T:>10d}  rho={rho:.6f}", end="  ")
    for p in p_values:
        print(f"||b||_{p:.1f}={norms[p]:.6f}", end="  ")
    print()

# =====================================================================
# Part B: Fit kappa(p) from log-linear regression
# =====================================================================
print("\n### Part B: Exponential decay fit: ||hat(b_m)||_p ~ C * 5^{-kappa*m} ###\n")

print(f"{'p':>5s}  {'kappa':>8s}  {'R^2':>8s}  {'C':>10s}  {'Verdict':>20s}")
print("-" * 60)

kappa_results = {}
for p in p_values:
    ms = list(range(2, 11))
    log_norms = [np.log(results[m][p]) for m in ms]

    # Fit: log(norm) = log(C) - kappa * m * log(5)
    # i.e. y = a + b*x where x = m, y = log(norm), b = -kappa*log(5)
    x = np.array(ms, dtype=float)
    y = np.array(log_norms)

    # Linear regression
    n = len(x)
    sx = np.sum(x)
    sy = np.sum(y)
    sxx = np.sum(x*x)
    sxy = np.sum(x*y)

    b = (n*sxy - sx*sy) / (n*sxx - sx*sx)
    a = (sy - b*sx) / n

    # R^2
    y_pred = a + b*x
    ss_res = np.sum((y - y_pred)**2)
    ss_tot = np.sum((y - np.mean(y))**2)
    r2 = 1 - ss_res/ss_tot

    kappa = -b / np.log(5)
    C = np.exp(a)

    q = p / (p - 1) if p > 1 else float('inf')
    threshold = 1 - 1/p if p > 1 else 0

    if p > 1:
        verdict = f"need kappa>{threshold:.3f}, {'YES' if kappa > threshold else 'NO'}"
    else:
        verdict = "l^1 (reference)"

    kappa_results[p] = (kappa, r2, C, threshold)
    print(f"{p:5.1f}  {kappa:8.4f}  {r2:8.4f}  {C:10.4f}  {verdict}")

# =====================================================================
# Part C: The critical condition kappa(p) > 1/q
# =====================================================================
print("\n### Part C: Critical condition analysis ###\n")

print("For the Holder bound to work, we need kappa(p) > 1/q = 1 - 1/p")
print("i.e., the l^p decay must outpace the l^q growth of the Dirichlet kernel.\n")

best_margin = -float('inf')
best_p = None

for p in p_values:
    if p <= 1:
        continue
    kappa, r2, C, threshold = kappa_results[p]
    margin = kappa - threshold
    if margin > best_margin:
        best_margin = margin
        best_p = p

    print(f"p={p:.1f}: kappa={kappa:.4f}, threshold={threshold:.4f}, margin={margin:+.4f}",
          "PASS" if margin > 0 else "FAIL")

print(f"\nBest p: {best_p:.1f} with margin {best_margin:+.4f}")

if best_margin > 0:
    print(">>> BOTTLENECK LEMMA IS EMPIRICALLY SUPPORTED <<<")
    print(f">>> At p={best_p}, the l^p norm decays faster than required.")
else:
    print(">>> BOTTLENECK LEMMA FAILS EMPIRICALLY <<<")
    print(">>> No p in the tested range gives kappa > threshold.")

# =====================================================================
# Part D: Multiscale decomposition by v_5 band
# =====================================================================
print("\n### Part D: l^p norms by 5-adic valuation band ###\n")

for m in [5, 7, 9]:
    orbit, T, mod = compute_orbit(m)
    f = compute_survivor_indicator(orbit, m)
    rho = np.mean(f)
    b = f - rho
    B_hat = np.fft.fft(b) / T

    # Group by v_5(j)
    bands = defaultdict(list)
    for j in range(1, T):
        v = min(v5(j), m)  # cap at m
        bands[v].append(abs(B_hat[j]))

    print(f"m={m}, T={T}:")
    print(f"  {'v_5':>4s}  {'count':>8s}  {'l^1':>10s}  {'l^1.5':>10s}  {'l^2':>10s}  {'max':>10s}")
    for v in sorted(bands.keys()):
        coeffs = np.array(bands[v])
        l1 = np.sum(coeffs)
        l15 = np.sum(coeffs**1.5)**(1/1.5)
        l2 = np.sqrt(np.sum(coeffs**2))
        lmax = np.max(coeffs)
        count = len(coeffs)
        print(f"  {v:4d}  {count:8d}  {l1:10.6f}  {l15:10.6f}  {l2:10.6f}  {lmax:10.6f}")
    print()

# =====================================================================
# Part E: The actual Holder bound vs actual error
# =====================================================================
print("\n### Part E: Holder bound vs actual error ###\n")

C_const = 1 / np.log10(2)

print(f"{'m':>3s}  {'L':>4s}  {'actual_err':>12s}  ", end="")
for p in [1.2, 1.5, 2.0]:
    print(f"{'Holder_'+str(p):>12s}  ", end="")
print(f"{'best_ratio':>12s}")
print("-" * 80)

for m in range(2, 11):
    orbit, T, mod = compute_orbit(m)
    f = compute_survivor_indicator(orbit, m)
    rho = np.mean(f)
    b = f - rho
    B_hat = np.fft.fft(b) / T

    L = int(np.ceil(C_const * m))

    # Actual error
    actual_count = sum(f[:L])
    actual_error = actual_count - L * rho

    # Dirichlet kernel
    D = np.zeros(T, dtype=complex)
    for j in range(T):
        if j == 0:
            D[j] = L
        else:
            # D_L(j) = sum_{i=0}^{L-1} exp(2*pi*i*j*i/T)
            omega = np.exp(2j * np.pi * j / T)
            if abs(omega - 1) < 1e-15:
                D[j] = L
            else:
                D[j] = (omega**L - 1) / (omega - 1)

    holder_bounds = {}
    for p in [1.2, 1.5, 2.0]:
        q = p / (p - 1)
        # l^p norm of hat(b_m) (non-DC)
        lp_b = np.sum(np.abs(B_hat[1:])**p)**(1/p)
        # l^q norm of D_L (non-DC)
        lq_D = np.sum(np.abs(D[1:])**q)**(1/q)
        holder = lp_b * lq_D
        holder_bounds[p] = holder

    best_ratio = min(holder_bounds[p] / max(abs(actual_error), 1e-10) for p in [1.2, 1.5, 2.0])

    print(f"{m:3d}  {L:4d}  {actual_error:12.4f}  ", end="")
    for p in [1.2, 1.5, 2.0]:
        print(f"{holder_bounds[p]:12.4f}  ", end="")
    print(f"{best_ratio:12.2f}")

# =====================================================================
# Summary
# =====================================================================
print("\n" + "=" * 70)
print("SUMMARY")
print("=" * 70)

print("""
Key questions answered:

1. Does ||hat(b_m)||_p decay like 5^{-kappa*m}?
   See Part B for fitted kappa values and R^2 goodness of fit.

2. Is kappa(p) > 1/q = 1 - 1/p for some p?
   See Part C. This is the critical condition for the Holder strategy.

3. How does the Holder bound compare to the l^1 bound?
   See Part E. If Holder bounds are tighter, the strategy has legs.

4. Where is the l^p mass concentrated in frequency space?
   See Part D. If low v_5 bands dominate, the major/minor arc decomposition works.
""")
