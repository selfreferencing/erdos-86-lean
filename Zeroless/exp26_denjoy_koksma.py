#!/usr/bin/env python3
"""
Experiment 26: Denjoy-Koksma Analysis of Transition Zone Discrepancy

Exp 25 found: transition zone discrepancy |sum_{i<L} f_m(i) - L*rho| < 11
for all m = 2..27, where L = ceil(C*m) ~ 3.3m.

The standard Denjoy-Koksma inequality on the circle gives:
  |sum f(x+j*alpha) - L*integral(f)| <= V(f)
But V(f_m) ~ O(9^m), giving a terrible bound.

This experiment investigates WHY the transition zone discrepancy is O(1)
despite the function having enormous variation. Possible explanations:

  A) The ORBIT variation (variation of f along the orbit ordering) is O(1),
     even though the CIRCLE variation (variation of f along [0,1)) is O(9^m).

  B) The digit-by-digit structure creates cancellation: each digit contributes
     discrepancy O(1/m), and m digits contribute O(1).

  C) The short-sum regime L << q_3 = 93 puts us in a regime where a
     different (better) estimate applies.

  D) The discrepancy decomposes additively across digits, and each digit's
     contribution is O(1).

Parts:
  A) Compute orbit variation of f_m (variation in orbit ordering)
  B) Per-digit discrepancy decomposition
  C) Short-sum discrepancy vs L for various m
  D) Comparison with random-walk model
  E) The role of the continued fraction structure
"""

import numpy as np
from collections import defaultdict

theta = np.log10(2)
C_const = 1.0 / theta  # ~ 3.3219

print("=" * 70)
print("EXPERIMENT 26: DENJOY-KOKSMA ANALYSIS")
print("=" * 70)

# =====================================================================
# Part A: Orbit variation vs circle variation
# =====================================================================
print("\n### Part A: Orbit variation vs circle variation ###\n")
print("The orbit of 2^n visits residues in a specific order.")
print("The 'orbit variation' counts sign changes of f_m along this ordering.")
print("The 'circle variation' counts sign changes of f_m along [0,1).")
print("Denjoy-Koksma uses circle variation; if orbit variation is smaller,")
print("that could explain the bounded discrepancy.\n")

for m in range(2, 9):  # cap at m=8 (T=312500) for circle variation
    T_m = 4 * 5**(m-1)
    mod10 = 10**m

    # Compute f_m along orbit
    x = pow(2, m, mod10)
    f_orbit = []
    for i in range(T_m):
        zl = True
        y = x
        for _ in range(m):
            if y % 10 == 0:
                zl = False
                break
            y //= 10
        f_orbit.append(1 if zl else 0)
        x = (2 * x) % mod10

    rho = sum(f_orbit) / T_m

    # Orbit variation: number of transitions 0->1 or 1->0
    orbit_transitions = sum(1 for i in range(T_m-1) if f_orbit[i] != f_orbit[i+1])
    # Add wrap-around
    orbit_transitions += (1 if f_orbit[-1] != f_orbit[0] else 0)

    # For circle variation, we'd need to sort by the fractional parts
    # frac((m+i)*theta). But frac((m+i)*theta) = frac(i*theta + m*theta).
    # Sorting by frac(i*theta + c) is the same as sorting by frac(i*theta)
    # (just shifts the origin).

    # The circle ordering: sort orbit elements by frac(i*theta)
    circle_order = sorted(range(T_m), key=lambda i: (i * theta) % 1)
    f_circle = [f_orbit[i] for i in circle_order]
    circle_transitions = sum(1 for i in range(T_m-1) if f_circle[i] != f_circle[i+1])
    circle_transitions += (1 if f_circle[-1] != f_circle[0] else 0)

    # The variation of f as a function on [0,1) = circle_transitions
    # (since f takes values 0,1, each transition contributes variation 1)
    circle_var = circle_transitions
    orbit_var = orbit_transitions

    print(f"m={m:2d}: T={T_m:10d}, rho={rho:.4f}, "
          f"orbit_var={orbit_var:8d}, circle_var={circle_var:8d}, "
          f"ratio={orbit_var/max(circle_var,1):.4f}")

# =====================================================================
# Part B: Per-digit discrepancy decomposition
# =====================================================================
print("\n### Part B: Per-digit discrepancy decomposition ###\n")
print("f_m = prod_{r=1}^m g_r where g_r(i) = 1 if digit r of 2^{m+i} != 0.")
print("How does the transition-zone discrepancy decompose across digits?\n")
print("Idea: N_m(L) = #{i<L : f_m(i)=1} = #{i<L : all g_r(i)=1}")
print("By inclusion-exclusion or sequential filtering:\n")

for m in [5, 8, 10, 15, 20]:
    T_m = 4 * 5**(m-1)
    mod10 = 10**m
    L = int(np.ceil(C_const * m))

    x = pow(2, m, mod10)
    orbit_elements = []
    for i in range(min(T_m, max(L + 100, 50000))):
        orbit_elements.append(x)
        x = (2 * x) % mod10

    # For each digit r, compute g_r(i) for i < L
    digit_zeros = [[] for _ in range(m)]  # digit_zeros[r] = list of i < L where digit r+1 = 0
    for i in range(L):
        x = orbit_elements[i]
        for r in range(m):
            d = (x // (10**r)) % 10
            if d == 0:
                digit_zeros[r].append(i)

    # Sequential survival: how many survive after filtering digit 1, then 2, etc.
    survivors = set(range(L))
    print(f"m={m}, L={L}:")
    print(f"  {'after digit r':>15s}  {'survivors':>10s}  {'expected':>10s}  {'disc':>8s}")

    for r in range(m):
        killed = set(digit_zeros[r]) & survivors
        survivors -= killed
        expected = L * (0.9 ** (r+1))
        disc = len(survivors) - expected
        if r < 5 or r >= m-3:
            print(f"  {r+1:15d}  {len(survivors):10d}  {expected:10.2f}  {disc:+8.2f}")
        elif r == 5:
            print(f"  {'...':>15s}")

    print()

# =====================================================================
# Part C: Short-sum discrepancy profile D_m(L) for L = 1..200
# =====================================================================
print("\n### Part C: Discrepancy profile D_m(L) for L = 1..200 ###\n")
print("For each m, plot D_m(L) = sum_{i<L} f_m(i) - L*rho_m as L varies.\n")

for m in [5, 10, 15, 20, 25]:
    T_m = 4 * 5**(m-1)
    mod10 = 10**m
    L_trans = int(np.ceil(C_const * m))

    x = pow(2, m, mod10)
    f_vals = []
    for i in range(min(T_m, 300)):
        zl = True
        y = x
        for _ in range(m):
            if y % 10 == 0:
                zl = False
                break
            y //= 10
        f_vals.append(1 if zl else 0)
        x = (2 * x) % mod10

    # Compute rho more accurately using larger sample if possible
    if T_m <= 50000:
        xx = pow(2, m, mod10)
        total_surv = 0
        for i in range(T_m):
            zl = True
            y = xx
            for _ in range(m):
                if y % 10 == 0:
                    zl = False
                    break
                y //= 10
            if zl:
                total_surv += 1
            xx = (2 * xx) % mod10
        rho = total_surv / T_m
    else:
        # Use 100k sample
        xx = pow(2, m, mod10)
        total_surv = 0
        sample = 100000
        for i in range(sample):
            zl = True
            y = xx
            for _ in range(m):
                if y % 10 == 0:
                    zl = False
                    break
                y //= 10
            if zl:
                total_surv += 1
            xx = (2 * xx) % mod10
        rho = total_surv / sample

    # Discrepancy profile
    running = 0.0
    checkpoints = [1, 2, 3, 5, 10, 15, 20, 30, 50, 70, 100, 150, 200]

    print(f"m={m} (rho={rho:.6f}, L_trans={L_trans}):")
    print(f"  {'L':>5s}  {'N_m(L)':>8s}  {'L*rho':>10s}  {'disc':>8s}  {'in_trans?':>10s}")

    for L_check in checkpoints:
        if L_check > len(f_vals):
            break
        nm = sum(f_vals[:L_check])
        expected = L_check * rho
        disc = nm - expected
        in_trans = "YES" if L_check <= L_trans else "no"
        print(f"  {L_check:5d}  {nm:8d}  {expected:10.4f}  {disc:+8.4f}  {in_trans:>10s}")
    print()

# =====================================================================
# Part D: Comparison with random walk model
# =====================================================================
print("\n### Part D: Random walk model ###\n")
print("If the f_m(i) were i.i.d. Bernoulli(rho), the discrepancy would be")
print("a random walk with step variance rho*(1-rho).")
print("After L steps, |disc| ~ sqrt(L * rho * (1-rho)).\n")

print(f"{'m':>3s}  {'L_trans':>8s}  {'rho':>8s}  {'actual_disc':>12s}  "
      f"{'RW_expected':>12s}  {'ratio':>8s}")
print("-" * 60)

for m in range(2, 28):
    T_m = 4 * 5**(m-1)
    mod10 = 10**m
    L = int(np.ceil(C_const * m))

    x = pow(2, m, mod10)
    f_vals = []
    for i in range(min(T_m, max(L + 10, 50000))):
        zl = True
        y = x
        for _ in range(m):
            if y % 10 == 0:
                zl = False
                break
            y //= 10
        f_vals.append(1 if zl else 0)
        x = (2 * x) % mod10

    if T_m <= 50000:
        rho = sum(f_vals[:T_m]) / T_m
    else:
        rho = sum(f_vals) / len(f_vals)

    actual_disc = sum(f_vals[:L]) - L * rho
    rw_expected = np.sqrt(L * rho * (1 - rho))

    ratio = abs(actual_disc) / max(rw_expected, 0.01)

    print(f"{m:3d}  {L:8d}  {rho:8.4f}  {actual_disc:+12.4f}  "
          f"{rw_expected:12.4f}  {ratio:8.4f}")

# =====================================================================
# Part E: Role of continued fraction structure
# =====================================================================
print("\n### Part E: Discrepancy at convergent denominators ###\n")
print("The Denjoy-Koksma inequality bounds disc at L = q_n by V(f).")
print("But actually, for our orbit, disc at L = q_n may be small because")
print("the orbit near-repeats at convergent denominators.\n")

# Convergent denominators of theta = log10(2)
cf = [0, 3, 3, 9, 2, 2, 4, 6, 2, 1, 1, 3, 1, 18]
convs = []
p_prev, p_curr = 0, 1
q_prev, q_curr = 1, 0
for a in cf:
    p_prev, p_curr = p_curr, a * p_curr + p_prev
    q_prev, q_curr = q_curr, a * q_curr + q_prev
    convs.append((p_curr, q_curr))

print("Convergents of theta:")
for n, (p, q) in enumerate(convs):
    err = abs(q * theta - p)
    print(f"  n={n}: p/q = {p}/{q}, ||q*theta|| = {err:.12f}")

print("\nDiscrepancy at L near convergent denominators:")
print(f"{'m':>3s}  {'q_n':>6s}  {'L=q_n':>8s}  {'disc':>10s}  {'L=q_n-1':>8s}  {'disc':>10s}")
print("-" * 55)

for m in [5, 8, 10, 12]:
    T_m = 4 * 5**(m-1)
    mod10 = 10**m

    x = pow(2, m, mod10)
    f_vals = []
    limit = min(T_m, 500000)
    for i in range(limit):
        zl = True
        y = x
        for _ in range(m):
            if y % 10 == 0:
                zl = False
                break
            y //= 10
        f_vals.append(1 if zl else 0)
        x = (2 * x) % mod10

    rho = sum(f_vals[:min(T_m, limit)]) / min(T_m, limit)

    for n, (p, q) in enumerate(convs):
        if q > 1 and q < limit - 1:
            disc_at_q = sum(f_vals[:q]) - q * rho
            disc_before = sum(f_vals[:q-1]) - (q-1) * rho
            print(f"{m:3d}  {q:6d}  {q:8d}  {disc_at_q:+10.4f}  "
                  f"{q-1:8d}  {disc_before:+10.4f}")

# =====================================================================
# Part F: Koksma-Hlawka type bound using star discrepancy
# =====================================================================
print("\n### Part F: Star discrepancy of orbit sequence ###\n")
print("The Koksma-Hlawka inequality bounds |sum f(x_j) - L*integral(f)|")
print("by V(f) * D_L* where D_L* is the star discrepancy of the points x_j.")
print("")
print("For L consecutive orbit points under rotation by theta,")
print("the star discrepancy D_L* ~ (log L) / L (Weyl-Ostrowski).\n")

for m in [5, 10, 15, 20]:
    L = int(np.ceil(C_const * m))
    # Star discrepancy of L consecutive points {i*theta mod 1}
    # Upper bound: D_L* <= 1/(2*L) + sum_{k=1}^{K} (1/(pi*k)) * min(1, 1/(L*||k*theta||))
    # Approximate: D_L* ~ (1+log(L)) / L for bounded type alpha

    # Direct computation of star discrepancy for small L
    points = sorted([(i * theta) % 1 for i in range(L)])

    # Star discrepancy: max over t in [0,1) of |#{x_j <= t}/L - t|
    # Check at each point and just after
    max_disc = 0
    for j in range(L):
        # Just below points[j]
        disc = abs(j / L - points[j])
        max_disc = max(max_disc, disc)
        # Just above points[j]
        disc = abs((j+1) / L - points[j])
        max_disc = max(max_disc, disc)

    # Also check at 0 and 1
    max_disc = max(max_disc, points[0])
    max_disc = max(max_disc, 1 - points[-1])

    weyl_bound = (1 + np.log(L)) / L

    print(f"m={m}, L={L}: star_disc D_L* = {max_disc:.6f}, "
          f"Weyl bound ~ {weyl_bound:.6f}, "
          f"D_L* * L = {max_disc * L:.4f}")

print("\nNote: Koksma-Hlawka gives |disc| <= V(f) * D_L*.")
print("With V(f_m) ~ 9^m and D_L* ~ 1/L, this gives ~ 9^m / L = 9^m / (3.3m),")
print("which is TERRIBLE. The bounded discrepancy must come from another mechanism.")

# =====================================================================
# Part G: The key test: is f_m low-variation ON THE ORBIT?
# =====================================================================
print("\n### Part G: Effective orbit variation ###\n")
print("The Denjoy-Koksma bound uses V(f) on the CIRCLE.")
print("But what matters for the orbit is V(f) along the ORBIT ORDERING.")
print("If f_m has low variation along the orbit (few transitions 0<->1"),
print("in the first L steps), then the orbit-Birkhoff sum is naturally bounded.\n")

print(f"{'m':>3s}  {'L':>5s}  {'transitions_in_L':>18s}  {'fraction':>10s}  "
      f"{'max_run_1':>12s}  {'max_run_0':>12s}")
print("-" * 70)

for m in range(2, 28):
    T_m = 4 * 5**(m-1)
    mod10 = 10**m
    L = int(np.ceil(C_const * m))

    x = pow(2, m, mod10)
    f_vals = []
    for i in range(min(T_m, L + 10)):
        zl = True
        y = x
        for _ in range(m):
            if y % 10 == 0:
                zl = False
                break
            y //= 10
        f_vals.append(1 if zl else 0)
        x = (2 * x) % mod10

    # Count transitions in first L values
    transitions = sum(1 for i in range(min(L, len(f_vals))-1) if f_vals[i] != f_vals[i+1])

    # Max run of 1s and 0s
    max_run_1 = 0
    max_run_0 = 0
    current_run = 1
    for i in range(1, min(L, len(f_vals))):
        if f_vals[i] == f_vals[i-1]:
            current_run += 1
        else:
            if f_vals[i-1] == 1:
                max_run_1 = max(max_run_1, current_run)
            else:
                max_run_0 = max(max_run_0, current_run)
            current_run = 1
    if f_vals[min(L, len(f_vals))-1] == 1:
        max_run_1 = max(max_run_1, current_run)
    else:
        max_run_0 = max(max_run_0, current_run)

    frac = transitions / max(L-1, 1)
    print(f"{m:3d}  {L:5d}  {transitions:18d}  {frac:10.4f}  "
          f"{max_run_1:12d}  {max_run_0:12d}")

# =====================================================================
# Part H: The martingale increment view
# =====================================================================
print("\n### Part H: Martingale increment discrepancies ###\n")
print("Define S_r(L) = #{i<L : digits 1..r all nonzero} = sum_{i<L} prod_{s=1}^r g_s(i)")
print("Then S_m(L) = N_m(L) and S_0(L) = L.")
print("The increment: S_r(L) - S_{r-1}(L) * (fraction surviving digit r)")
print("represents the discrepancy contributed by digit r.\n")

for m in [8, 12, 16, 20, 25]:
    T_m = 4 * 5**(m-1)
    mod10 = 10**m
    L = int(np.ceil(C_const * m))

    x = pow(2, m, mod10)
    orbit_elts = []
    for i in range(min(T_m, max(L + 10, 50000))):
        orbit_elts.append(x)
        x = (2 * x) % mod10

    # Compute survival through each digit level
    # prod_r(i) = prod_{s=1}^r g_s(i) = 1 if digits 1..r are all nonzero
    S_prev = L  # S_0 = L
    rho_cumulative = 1.0

    increments = []

    for r in range(1, m+1):
        # Count survivors through digit r in first L orbit elements
        S_r = 0
        for i in range(L):
            x = orbit_elts[i]
            ok = True
            for s in range(1, r+1):
                d = (x // (10**(s-1))) % 10
                if d == 0:
                    ok = False
                    break
            if ok:
                S_r += 1

        # Expected: if digit r independently removes 1/10 of survivors
        # S_r should be ~ S_{r-1} * 0.9
        expected_S_r = S_prev * 0.9
        increment_disc = S_r - expected_S_r

        increments.append(increment_disc)

        if r <= 5 or r >= m-2:
            print(f"m={m}, r={r:2d}: S_r={S_r:5d}, expected={expected_S_r:8.2f}, "
                  f"disc={increment_disc:+8.2f}")
        elif r == 6:
            print(f"  ...")

        S_prev = S_r

    total_disc = sum(increments)
    print(f"  Total increment disc: {total_disc:+.2f}")
    print(f"  Final N_m(L) = {S_r}, rho*L = {rho_cumulative * 0.9**m * L:.2f}")
    print()

print("=" * 70)
print("EXPERIMENT 26 COMPLETE")
print("=" * 70)
