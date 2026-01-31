#!/usr/bin/env python3
"""
Experiment 25: Bounded Discrepancy and Coboundary Structure Test

GPT 4B's key insight: the O(1) error we observe is the signature of 1_{F_m}
being approximately a coboundary for the rotation by theta = log10(2).

If 1_{F_m}(x) - mu(F_m) = g_m(x) - g_m(x + theta) + epsilon_m(x),
then telescoping gives bounded Birkhoff sums, and once L*mu(F_m) < 1/2,
the sum must be exactly 0 (finiteness).

This experiment tests:

  A) Bounded discrepancy: is sup_L |sum_{j<L} f_m(j*theta) - L*rho_m|
     uniformly bounded in m? (We've seen this for the transition zone;
     now test across ALL L up to T_m.)

  B) Coboundary test: can we solve g_m(x) - g_m(x+theta) = f_m(x) - rho_m
     in Fourier space, and is |g_m|_inf bounded?

  C) Small divisor analysis: for the frequencies k that appear in the
     digit-filter decomposition, how small is |k*theta mod 1|?

  D) Martingale decomposition: express f_m as product of (1-xi_r) and
     check if each increment is approximately a coboundary.

  E) Restricted frequency set: identify K_m and check small divisor bounds.
"""

import numpy as np
from collections import defaultdict

theta = np.log10(2)  # 0.30102999566...

# =====================================================================
# Part A: Bounded discrepancy for Birkhoff sums of 1_{F_m}
# =====================================================================
print("=" * 70)
print("EXPERIMENT 25: COBOUNDARY / BOUNDED DISCREPANCY TEST")
print("=" * 70)

print("\n### Part A: Bounded discrepancy of Birkhoff sums ###\n")
print("For each m, compute D_m(L) = |sum_{j<L} f_m(j*theta mod 1) - L*rho_m|")
print("for L = 1, ..., N_max. Check if sup_L D_m(L) is bounded uniformly in m.\n")

def is_zeroless_real(x, m):
    """Check if a real number x in [10^{m-1}, 10^m) has all digits nonzero."""
    # x should be an integer (or close to one)
    x = int(round(x))
    for _ in range(m):
        if x % 10 == 0:
            return False
        x //= 10
    return True

# For each m, the orbit is 2^n for n in [m, m+T_m).
# frac(n*theta) = frac(n*log10(2)) determines the significand.
# 2^n has D(2^n) = m iff n*theta in [m-1, m), i.e., frac(n*theta) in [1-theta, 1)
# wait, more carefully: D(2^n) = floor(n*theta) + 1 = m means n*theta in [m-1, m)
# So n in [ceil((m-1)/theta), ceil(m/theta))

# Actually, let's work directly with the orbit mod 10^m.
# The orbit element at index i is 2^{m+i} mod 10^m, for i = 0, 1, ..., T_m-1.
# f_m(i) = 1 if 2^{m+i} mod 10^m is zeroless.
# The Birkhoff sum is sum_{i<L} f_m(i).

# But GPT's formulation is on the circle: f_m(x) = 1 if 10^x * 10^{m-1}
# has all digits nonzero as an m-digit number.
# The orbit of x=0 under rotation by theta: x_j = j*theta mod 1.
# Then 2^{m+j} = 10^{m-1+frac((m+j)*theta)} and frac((m+j)*theta) = frac(j*theta + m*theta)
# = frac(j*theta + frac(m*theta))

# For the orbit-based computation, it's simpler to just compute 2^{m+i} mod 10^m directly.

for m in range(2, 28):
    mod10 = 10**m
    T_m = 4 * 5**(m-1)

    # Compute Birkhoff sums
    x = pow(2, m, mod10)
    running_sum = 0
    running_expected = 0.0

    # First pass: compute rho_m
    survivor_count = 0
    xx = x
    check_limit = min(T_m, 50000)  # cap for large m
    orbit_vals = []
    for i in range(check_limit):
        zl = True
        y = xx
        for _ in range(m):
            if y % 10 == 0:
                zl = False
                break
            y //= 10
        orbit_vals.append(1 if zl else 0)
        if zl:
            survivor_count += 1
        xx = (2 * xx) % mod10

    if check_limit == T_m:
        rho = survivor_count / T_m
    else:
        rho = survivor_count / check_limit  # approximate

    # Compute discrepancy
    max_disc = 0.0
    max_disc_L = 0
    min_disc = 0.0
    running = 0.0

    discs_at_checkpoints = []

    for i in range(check_limit):
        running += orbit_vals[i] - rho
        disc = abs(running)
        if disc > max_disc:
            max_disc = disc
            max_disc_L = i + 1
        if running < min_disc:
            min_disc = running

        # Record at specific L values
        if (i+1) in [10, 50, 100, 500, 1000, 5000, 10000, 50000]:
            discs_at_checkpoints.append((i+1, running))

    L_trans = int(np.ceil(m / np.log10(2)))  # transition zone length

    # Discrepancy in transition zone
    trans_disc = sum(orbit_vals[:min(L_trans, check_limit)]) - rho * min(L_trans, check_limit)

    print(f"m={m:2d}: rho={rho:.6f}, L_trans={L_trans:4d}, "
          f"trans_disc={trans_disc:+.2f}, "
          f"sup|disc|={max_disc:.2f} (at L={max_disc_L}), "
          f"checked L up to {check_limit}")

# =====================================================================
# Part B: Coboundary test in Fourier space
# =====================================================================
print("\n### Part B: Coboundary test - solving g - g*T = f - rho ###\n")
print("In Fourier: hat(g)(k) = hat(f-rho)(k) / (1 - e^{2*pi*i*k*theta})")
print("Check if |g|_inf = sup|sum hat(g)(k) e^{2*pi*i*k*x}| is bounded.\n")

# We work on the finite orbit: f_m defined on Z/T_m Z with rotation T: i -> i+1.
# The cohomological equation: g(i) - g(i+1) = f(i) - rho
# In orbit-Fourier: hat(g)(k) = hat(f-rho)(k) / (1 - omega^k) where omega = e^{2pi*i/T}
#
# BUT this is the wrong framing! The rotation on the circle by theta is NOT
# the same as the shift by 1 on the orbit Z/T_m Z.
#
# The orbit shift i -> i+1 corresponds to multiplication by 2 in (Z/5^m Z)^*.
# The rotation on [0,1) by theta corresponds to a DIFFERENT map.
#
# Actually, for the coboundary test, we should work on the CIRCLE.
# f_m is a function on [0,1): f_m(x) = 1 if the number with significand 10^x
# (as an m-digit number) is zeroless.
#
# For computational feasibility, discretize [0,1) into N points and compute
# the Birkhoff sum / coboundary.

# Let's work with a finer discretization.
# f_m(x) = 1 iff floor(10^{m-1+x}) has all digits nonzero, where x in [0,1).

for m in [3, 5, 7, 9]:
    N_disc = 10**m  # discretize [0,1) into 10^m points

    # Build f_m on the discretized circle
    # f_m(j/N) = 1 iff the m-digit number floor(10^{m-1} * 10^{j/N}) is zeroless
    # = 1 iff the integer in [10^{m-1}, 10^m) closest to 10^{m-1} * 10^{j/N} is zeroless

    # Actually, a cleaner approach: the m-digit numbers are k = 10^{m-1}, ..., 10^m - 1.
    # k is zeroless iff all digits are in {1,...,9}.
    # k corresponds to x = log10(k) - (m-1) in [0, 1).
    # So f_m(x) = 1 iff the integer 10^{m-1+x} is zeroless.

    # For the Fourier/coboundary computation, it's easier to work with the
    # indicator on integers: f(k) = 1 if k in [10^{m-1}, 10^m) is zeroless.
    # There are 9^m zeroless numbers among 9*10^{m-1} total m-digit numbers.
    # rho_m = 9^m / (9*10^{m-1}) = (9/10)^{m-1}

    # But the rotation corresponds to multiplication by 2 (or equivalently,
    # the shift n -> n+1 in the exponent of 2^n).

    # Let me think about this differently. On the orbit:
    # f_m(i) = 1 if 2^{m+i} mod 10^m is zeroless.
    # The "rotation" is the shift i -> i+1.
    # The cohomological equation ON THE ORBIT: g(i) - g(i+1) = f(i) - rho.
    # This is solvable iff the sum over a full period is 0, which it is
    # (since sum f(i) = rho * T by definition).
    #
    # Solution: g(i) = sum_{j=0}^{i-1} (rho - f(j)) (partial sums of rho - f)
    # Then g(i) - g(i+1) = -(rho - f(i)) = f(i) - rho. Correct.
    #
    # So |g|_inf = max_i |sum_{j<i} (rho - f(j))| = max discrepancy!

    # This means: the coboundary IS the partial sum function, and |g|_inf IS
    # the max discrepancy from Part A.
    # If max discrepancy is bounded uniformly in m, then g_m is bounded.

    # BUT WAIT: this is for the orbit shift i -> i+1, NOT for the circle rotation
    # x -> x + theta. The orbit shift on Z/T_m Z corresponds to the multiplication
    # x -> 2x on (Z/5^m Z)^*, NOT to an additive shift.

    # The circle rotation x -> x + theta on [0,1) is a different dynamical system
    # from the orbit shift. The orbit of 0 under x -> x + theta gives the
    # fractional parts {n*theta}, and the m-digit-zeroless condition applies to
    # 2^n = 10^{m-1+frac(n*theta)}.

    # For the ORBIT shift, the coboundary is the partial sum = discrepancy.
    # For the CIRCLE rotation, the coboundary would need a different construction.

    # Let's compute both and compare.

    # ORBIT COBOUNDARY (g_orbit: the partial sum function)
    T_m = 4 * 5**(m-1)
    mod10 = 10**m
    check = min(T_m, 20000)

    x = pow(2, m, mod10)
    f_vals = []
    for i in range(check):
        zl = True
        y = x
        for _ in range(m):
            if y % 10 == 0:
                zl = False
                break
            y //= 10
        f_vals.append(1 if zl else 0)
        x = (2 * x) % mod10

    rho = sum(f_vals) / len(f_vals)

    # Coboundary = partial sum of (rho - f)
    g_vals = [0.0]
    s = 0.0
    for i in range(check):
        s += rho - f_vals[i]
        g_vals.append(s)

    g_max = max(abs(v) for v in g_vals)

    print(f"m={m}: orbit coboundary |g|_inf = {g_max:.4f} "
          f"(= max discrepancy over {check} steps)")

print("\n(If |g|_inf is bounded uniformly in m, the coboundary mechanism works.)")
print("(Note: this is for the orbit shift, not the circle rotation.)")

# =====================================================================
# Part C: Small divisor analysis
# =====================================================================
print("\n### Part C: Small divisors |k*theta mod 1| for orbit frequencies ###\n")
print("In the orbit DFT on Z/T_m Z, the rotation corresponds to the shift.")
print("The cohomological equation hat(g)(k) = hat(f-rho)(k) / (1-omega^k)")
print("where omega = e^{2*pi*i/T_m}.")
print("Small divisors occur when k/T_m is close to 0 (or equivalently, k is small).\n")

# For the orbit shift on Z/T_m Z:
# omega = e^{2*pi*i/T_m}
# 1 - omega^k = 1 - e^{2*pi*i*k/T_m}
# |1 - omega^k| = 2*|sin(pi*k/T_m)| >= 2*|sin(pi*||k/T_m||)|
# where ||x|| = min(x mod 1, 1 - x mod 1)
#
# The smallest |1 - omega^k| occurs for k = 1 (or T_m - 1), giving
# |1 - omega^1| ~ 2*pi/T_m.
#
# So the "small divisor" is of size ~1/T_m, and the coboundary g has
# |hat(g)(k)| ~ T_m * |hat(f)(k)| for k near 0.
#
# But |hat(f)(k)| ~ rho/T_m for most k (flat part of spectrum),
# so |hat(g)(k)| ~ rho for k=1, which is O(1). Good!
#
# The question: do any hat(f)(k) values at k near 0 have |hat(f)(k)| >> rho/T_m?

for m in [4, 6, 8]:
    T_m = 4 * 5**(m-1)
    mod10 = 10**m

    x = pow(2, m, mod10)
    f_vals = []
    for i in range(T_m):
        zl = True
        y = x
        for _ in range(m):
            if y % 10 == 0:
                zl = False
                break
            y //= 10
        f_vals.append(1.0 if zl else 0.0)
        x = (2 * x) % mod10

    rho = sum(f_vals) / T_m
    b_vals = np.array([v - rho for v in f_vals])

    # DFT
    B_hat = np.fft.fft(b_vals) / T_m  # hat(b)(k)

    # Small divisor denominators
    denominators = np.array([abs(1 - np.exp(2j*np.pi*k/T_m)) for k in range(T_m)])
    denominators[0] = 1.0  # DC term, not used

    # Coboundary Fourier coefficients
    G_hat = np.zeros(T_m, dtype=complex)
    for k in range(1, T_m):
        G_hat[k] = B_hat[k] / (1 - np.exp(2j*np.pi*k/T_m))

    # Reconstruct g and check sup norm
    g_recon = np.fft.ifft(G_hat * T_m).real

    print(f"m={m}: T_m={T_m}, rho={rho:.6f}")
    print(f"  |g|_inf (from Fourier) = {np.max(np.abs(g_recon)):.4f}")
    print(f"  max|hat(b)(k)|/rho = {np.max(np.abs(B_hat[1:]))/rho:.6f}")

    # Show the small-k behavior
    print(f"  Small-k analysis (k, |hat(b)(k)|, |1-omega^k|, |hat(g)(k)|):")
    for k in [1, 2, 3, 5, 10, T_m//5, T_m//4]:
        if k < T_m:
            bk = abs(B_hat[k])
            dk = abs(1 - np.exp(2j*np.pi*k/T_m))
            gk = abs(G_hat[k])
            print(f"    k={k:8d}: |hat(b)|={bk:.8f}, |1-w^k|={dk:.8f}, |hat(g)|={gk:.8f}")
    print()

# =====================================================================
# Part D: Circle rotation version
# =====================================================================
print("\n### Part D: Circle rotation coboundary ###\n")
print("The CIRCLE rotation by theta = log10(2) is different from the orbit shift.")
print("Test: compute Birkhoff sums of 1_{F_m}({n*theta}) for n = 1, 2, ..., N.\n")

# For the circle rotation:
# 1_{F_m}(x) = 1 iff 10^{m-1+x} has all digits nonzero
# The orbit is x_n = frac(n*theta) = frac(n*log10(2))
# 2^n = 10^{floor(n*theta)} * 10^{frac(n*theta)}
# D(2^n) = floor(n*theta) + 1

# For a FIXED m, the n's with D(2^n) = m satisfy floor(n*theta) = m-1,
# i.e., n in [ceil((m-1)/theta), floor(m/theta)].
# But we want to test the general circle coboundary across ALL n.

# Let's compute: for each m, is the function 1_{F_m} on [0,1) approximately
# a coboundary for x -> x + theta?

# Discretize [0,1) into 10^m points: x_j = j/10^m, j = 0, ..., 10^m - 1
# f_m(x_j) = 1 iff the m-digit number (10^{m-1} + j) is zeroless
# Wait: 10^{m-1+x_j} = 10^{m-1} * 10^{j/10^m} which for j << 10^m is approximately
# 10^{m-1} * (1 + j*ln(10)/10^m).
# This isn't the right discretization.

# Better: the m-digit number corresponding to x in [0,1) is floor(10^{m-1+x}).
# For x = j/10^m, this is floor(10^{m-1} * 10^{j/10^m}).
# For large 10^m, 10^{j/10^m} ~ 1 + j*ln(10)/10^m, so the integer is
# approximately 10^{m-1} + j * (10^{m-1} * ln(10)) / 10^m.

# Actually, let's just use the orbit directly.
# The orbit 2^n mod 10^m for n = m, m+1, ... visits the elements of
# (Z/10^m Z) that are divisible by 2^m.
# The "circle coordinate" of orbit element i is frac((m+i)*theta).
# The zeroless condition on 2^{m+i} mod 10^m corresponds to f_m(frac((m+i)*theta)) = 1.

# So the Birkhoff sum is: sum_{i=0}^{L-1} f_m(frac((m+i)*theta))
# = #{i in [0,L) : 2^{m+i} is zeroless at digit count m}

# This is what we already computed in Part A! The orbit-based computation
# IS the circle rotation computation, because the orbit visits elements
# in the order determined by the rotation.

# BUT there's a subtlety: the orbit on Z/T_m Z (the shift by 1) corresponds
# to the rotation by theta on the circle ONLY approximately (they have the
# same equidistribution properties but different orderings).

# Actually, no. The orbit element at index i is u_i = 2^i mod 5^m.
# The circle coordinate is frac((m+i)*theta) = frac(i*theta + m*theta).
# The shift i -> i+1 on the orbit corresponds to x -> x + theta on the circle.
# So the orbit shift IS the circle rotation (restricted to the orbit).

# Therefore, Part A already IS the circle rotation test.
# The max discrepancy from Part A is |g_m|_inf for the circle rotation coboundary.

print("The orbit shift i -> i+1 corresponds EXACTLY to the circle rotation")
print("x -> x + theta (since orbit index i corresponds to 2^{m+i}, and")
print("frac((m+i)*theta) = frac(i*theta + m*theta) advances by theta per step).")
print("")
print("Therefore, Part A already computes the circle rotation coboundary.")
print("The max discrepancy from Part A = |g_m|_inf for the coboundary.")

# =====================================================================
# Part E: Restricted frequency set and small divisor bounds
# =====================================================================
print("\n### Part E: Digit-filter frequencies and small divisor bounds ###\n")
print("For the Fourier expansion of 1_{F_m}, which frequencies k appear?")
print("The digit-cylinder structure means hat(f_m) is supported on")
print("specific structured frequencies. Check |k*theta mod 1| for these.\n")

# The frequencies that matter are those where hat(f_m)(k) is large.
# From the Riesz product structure, the dominant frequencies have
# v_5(k) = m-2 (the k's that are multiples of 5^{m-2} but not 5^{m-1}).

# For the circle rotation, the relevant small divisor is:
# |1 - e^{2*pi*i*k*theta}| = 2*|sin(pi*k*theta)|
# This is small when k*theta is close to an integer.

# For the orbit on Z/T_m Z, the shift is i -> i+1, and the frequencies
# are k = 0, 1, ..., T_m-1. The rotation on the circle by theta means
# the "true" circle frequency of orbit-frequency k is k*theta/T_m... no.

# Actually: the orbit DFT decomposes f into orbit-eigenfunctions
# phi_k(i) = omega^{ik} where omega = e^{2*pi*i/T_m}.
# The shift eigenvalue is omega^k = e^{2*pi*i*k/T_m}.
# So the "small divisor" is |1 - e^{2*pi*i*k/T_m}|, which is small for
# k near 0 or T_m.

# The circle interpretation: the orbit visits the circle at positions
# frac(i*theta + c), and orbit-frequency k corresponds to the circle frequency
# such that e^{2*pi*i*k*frac(i*theta)} = e^{2*pi*i*k*i*theta}.
# So orbit-frequency k corresponds to circle frequency k*theta (roughly).
# The small divisor |k*theta mod 1| controls the coboundary.

# But k ranges in {1, ..., T_m-1} which grows as 5^m. The question is:
# how small can |k*theta mod 1| be for small k (the dangerous regime)?

print("Small divisor |k*theta mod 1| for small k:\n")
print(f"{'k':>8s}  {'k*theta':>14s}  {'frac(k*theta)':>14s}  {'||k*theta||':>14s}")
print("-" * 55)

for k in list(range(1, 30)) + [100, 1000, 10000, 100000]:
    kt = k * theta
    frac_kt = kt - int(kt)
    dist = min(frac_kt, 1 - frac_kt)
    print(f"{k:8d}  {kt:14.8f}  {frac_kt:14.8f}  {dist:14.8f}")

print("\n\nContinued fraction convergents of theta = log10(2):")
print("(These give the best rational approximations, hence smallest ||k*theta||)\n")

# Compute continued fraction
from fractions import Fraction

def cf_expansion(x, n_terms=20):
    """Compute continued fraction expansion of x."""
    terms = []
    for _ in range(n_terms):
        a = int(x)
        terms.append(a)
        x = x - a
        if abs(x) < 1e-14:
            break
        x = 1.0 / x
    return terms

def convergents(cf):
    """Compute convergents from continued fraction."""
    convs = []
    p_prev, p_curr = 0, 1
    q_prev, q_curr = 1, 0
    for a in cf:
        p_prev, p_curr = p_curr, a * p_curr + p_prev
        q_prev, q_curr = q_curr, a * q_curr + q_prev
        convs.append((p_curr, q_curr))
    return convs

cf = cf_expansion(theta, 25)
print(f"CF = [{cf[0]}; {', '.join(str(a) for a in cf[1:])}]")

convs = convergents(cf)
print(f"\n{'n':>3s}  {'p_n':>12s}  {'q_n':>12s}  {'|q_n*theta - p_n|':>20s}  "
      f"{'1/(q_n*q_{n+1})':>18s}")
print("-" * 70)

for n, (p, q) in enumerate(convs):
    err = abs(q * theta - p)
    if n + 1 < len(convs):
        q_next = convs[n+1][1]
        bound = 1.0 / (q * q_next)
    else:
        bound = float('nan')
    print(f"{n:3d}  {p:12d}  {q:12d}  {err:20.15f}  {bound:18.15f}")

# Check: which convergent denominators are in the "dangerous" range for each m?
print("\n\nFor each m, the orbit period T_m = 4*5^{m-1}.")
print("The dangerous frequencies are convergent denominators q_n that are")
print("much smaller than T_m (giving small divisors).\n")

print(f"{'m':>3s}  {'T_m':>12s}  {'largest q_n < T_m':>18s}  "
      f"{'||q_n*theta||':>18s}  {'|hat(f)(q_n)|/rho':>20s}")
print("-" * 80)

for m in range(2, 16):
    T_m = 4 * 5**(m-1)

    # Find largest convergent denominator < T_m
    best_q = 1
    best_err = abs(theta)
    for p, q in convs:
        if q < T_m and q > best_q:
            best_q = q
            best_err = abs(q * theta - round(q * theta))

    # Compute |hat(f)(q_n)| / rho at that frequency
    if T_m <= 50000:
        mod10 = 10**m
        x = pow(2, m, mod10)
        f_vals = []
        for i in range(T_m):
            zl = True
            y = x
            for _ in range(m):
                if y % 10 == 0:
                    zl = False
                    break
                y //= 10
            f_vals.append(1.0 if zl else 0.0)
            x = (2 * x) % mod10

        rho = sum(f_vals) / T_m
        b_arr = np.array(f_vals) - rho
        B_hat = np.fft.fft(b_arr) / T_m

        # Find the orbit frequency closest to the convergent denominator
        # Orbit frequency k corresponds to e^{2*pi*i*k/T_m}
        # The "circle angle" is k/T_m
        # We want k/T_m ~ q*theta mod 1, i.e., k ~ q*theta*T_m mod T_m
        k_target = round(best_q * theta * T_m) % T_m
        if k_target == 0:
            k_target = best_q % T_m

        bk = abs(B_hat[k_target]) / rho if rho > 0 else 0
        print(f"{m:3d}  {T_m:12d}  {best_q:18d}  {best_err:18.15f}  {bk:20.8f}")
    else:
        print(f"{m:3d}  {T_m:12d}  {best_q:18d}  {best_err:18.15f}  {'(too large)':>20s}")

# =====================================================================
# Part F: Discrepancy growth rate
# =====================================================================
print("\n### Part F: Discrepancy growth rate with m ###\n")
print("If the coboundary mechanism works, |g_m|_inf should be O(1).")
print("Plot max discrepancy vs m to check.\n")

max_discs = []
for m in range(2, 25):
    mod10 = 10**m
    T_m = 4 * 5**(m-1)
    check = min(T_m, 100000)

    x = pow(2, m, mod10)
    f_vals = []
    for i in range(check):
        zl = True
        y = x
        for _ in range(m):
            if y % 10 == 0:
                zl = False
                break
            y //= 10
        f_vals.append(1 if zl else 0)
        x = (2 * x) % mod10

    rho = sum(f_vals) / len(f_vals)

    running = 0.0
    max_d = 0.0
    for v in f_vals:
        running += v - rho
        if abs(running) > max_d:
            max_d = abs(running)

    max_discs.append((m, max_d, check))
    print(f"m={m:2d}: max|disc| = {max_d:.4f}  (checked {check} of {T_m})")

print("\nSummary: max discrepancies across m:")
print(f"  m=2-5:  {max(d for m,d,_ in max_discs if m<=5):.4f}")
print(f"  m=6-10: {max(d for m,d,_ in max_discs if 6<=m<=10):.4f}")
print(f"  m=11-15: {max(d for m,d,_ in max_discs if 11<=m<=15):.4f}")
print(f"  m=16-20: {max(d for m,d,_ in max_discs if 16<=m<=20):.4f}")
print(f"  m=21-24: {max(d for m,d,_ in max_discs if 21<=m<=24):.4f}")

# Check if growing or bounded
vals = [d for _,d,_ in max_discs if _ >= 5]
if len(vals) >= 2:
    growth = vals[-1] / vals[0]
    print(f"\n  Growth ratio (m=5 to m={max_discs[-1][0]}): {growth:.2f}")
    if growth < 2.0:
        print("  >>> CONSISTENT WITH BOUNDED DISCREPANCY <<<")
    else:
        print("  >>> DISCREPANCY APPEARS TO GROW <<<")

print("\n" + "=" * 70)
print("EXPERIMENT 25 COMPLETE")
print("=" * 70)
