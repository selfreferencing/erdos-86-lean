#!/usr/bin/env python3
"""
Experiment 23: 5-adic Tree / Automaton Analysis

GPT 2B suggested: the chain T_{j+1} = 5*T_j defines a 5-ary refinement tree
of admissible residues. If the survival rate along the "small index" branch
drops below 1/5 at a positive fraction of levels, the minimal survivor index
grows exponentially, eventually exceeding Cm.

This experiment tracks the 5-adic refinement tree for small orbit indices.

Parts:
  A) For each level j (mod 5^j), which residue classes contain orbit indices
     i < L = ceil(C*m)? How many of their 5 children survive at level j+1?
  B) Track survival rate per level for the "small index" branch
  C) Track the minimal survivor index as a function of m
  D) Branching structure: at each node, how many of 5 children are admissible?
  E) Comparison: small-index vs generic branching rates
"""

import numpy as np
from collections import defaultdict

def compute_orbit(m):
    """Compute the full orbit of 2^n mod 10^m."""
    mod = 10**m
    T = 4 * 5**(m-1)
    orbit = [0] * T
    x = pow(2, m, mod)
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

def digits_zero_free(x, num_digits):
    """Check if the last num_digits digits of x are all nonzero."""
    for _ in range(num_digits):
        if x % 10 == 0:
            return False
        x //= 10
    return True

C_const = 1 / np.log10(2)

print("=" * 70)
print("EXPERIMENT 23: 5-ADIC TREE / AUTOMATON ANALYSIS")
print("=" * 70)

# =====================================================================
# Part A: Residue classes containing small orbit indices at each level
# =====================================================================
print("\n### Part A: Small-index residue classes at each 5-adic level ###\n")

# For a given m, look at orbit indices i = 0, 1, ..., L-1
# At each level j (looking at residues mod T_j = 4*5^{j-1}):
#   - Which residue classes mod T_j contain at least one i < L?
#   - Of those, which are "admissible" (the j-th digit is nonzero)?
#   - At the next level j+1 = 5*T_j, each class splits into 5 children.
#     How many children contain an i < L? How many are admissible?

for m in [6, 8, 10, 12, 15, 20]:
    L = int(np.ceil(C_const * m))
    print(f"m={m}, L={L}:")
    print(f"  {'level j':>8s}  {'T_j':>10s}  {'classes w/ small i':>20s}  "
          f"{'admissible':>12s}  {'surv_rate':>10s}  {'children_per_node':>18s}")

    # We track which residue classes mod T_j contain indices < L
    # At level j=1: T_1=4, indices 0..L-1 mod 4
    prev_classes = set()  # residue classes mod T_{j-1} containing small indices

    for j in range(1, min(m+1, 25)):
        T_j = 4 * 5**(j-1)

        # Which residue classes mod T_j contain an index i < L?
        classes_with_small = set()
        for i in range(L):
            classes_with_small.add(i % T_j)

        # How many of these are admissible at level j?
        # A class r mod T_j is admissible at level j if the j-th digit of the
        # orbit element at index r is nonzero.
        # The orbit element at index i is 2^{m+i} mod 10^m.
        # The j-th digit (from right) of x is floor(x / 10^{j-1}) mod 10.
        # But we need to check: is the j-th digit of 2^{m+i} mod 10^j nonzero?

        # Actually, admissibility at level j means: the j-th digit of the orbit
        # element is nonzero. The j-th digit depends only on the orbit element
        # mod 10^j, which depends only on i mod T_j.

        # Let's compute directly: for each residue class r mod T_j that contains
        # a small index, check if the j-th digit of 2^{m+r} mod 10^j is nonzero.
        mod_j = 10**j
        admissible = set()
        for r in classes_with_small:
            x = pow(2, m + r, mod_j)
            # Check if ALL j digits are nonzero (survivor at level j)
            if digits_zero_free(x, j):
                admissible.add(r)

        # Branching: how did we get here from level j-1?
        if j == 1:
            children_info = "-"
        else:
            T_prev = 4 * 5**(j-2)
            # Each class r mod T_prev splits into 5 children: r, r+T_prev, r+2T_prev, ...
            # Count: of the prev_admissible classes, how many children are in classes_with_small AND admissible?
            total_children_possible = len(prev_admissible) * 5
            total_children_occupied = 0
            total_children_admissible = 0
            for r_prev in prev_admissible:
                for c in range(5):
                    child = r_prev + c * T_prev
                    if child % T_j == child:  # make sure it's a valid class mod T_j
                        pass
                    child_mod = child % T_j
                    if child_mod in classes_with_small:
                        total_children_occupied += 1
                    if child_mod in admissible:
                        total_children_admissible += 1

            if len(prev_admissible) > 0:
                avg_children = total_children_admissible / len(prev_admissible)
                children_info = f"{avg_children:.2f}/5 = {avg_children/5:.3f}"
            else:
                children_info = "0/5"

        surv_rate = len(admissible) / max(len(classes_with_small), 1)

        print(f"  {j:8d}  {T_j:10d}  {len(classes_with_small):20d}  "
              f"{len(admissible):12d}  {surv_rate:10.4f}  {children_info:>18s}")

        prev_classes = classes_with_small
        prev_admissible = admissible

        if len(admissible) == 0:
            print(f"  >>> NO ADMISSIBLE CLASSES AT LEVEL {j} -- all small indices eliminated <<<")
            break

    print()

# =====================================================================
# Part B: Survival rate per level (the key question)
# =====================================================================
print("\n### Part B: Survival rate = |admissible & small| / |small classes| ###\n")
print("GPT 2B's condition: if survival rate < 1/5 at positive fraction of levels,")
print("then minimal survivor grows exponentially.\n")

for m in [8, 12, 16, 20, 25, 30]:
    L = int(np.ceil(C_const * m))
    rates = []

    for j in range(1, min(m+1, 35)):
        T_j = 4 * 5**(j-1)

        classes_with_small = set()
        for i in range(L):
            classes_with_small.add(i % T_j)

        mod_j = 10**j
        admissible = 0
        for r in classes_with_small:
            x = pow(2, m + r, mod_j)
            if digits_zero_free(x, j):
                admissible += 1

        rate = admissible / max(len(classes_with_small), 1)
        rates.append(rate)

    below_threshold = sum(1 for r in rates if r < 0.2)
    print(f"m={m:2d}, L={L:3d}: levels below 1/5 survival: {below_threshold}/{len(rates)}  "
          f"rates: {' '.join(f'{r:.2f}' for r in rates[:min(15, len(rates))])}"
          + (" ..." if len(rates) > 15 else ""))

# =====================================================================
# Part C: Minimal survivor index as function of m
# =====================================================================
print("\n### Part C: Minimal survivor index ###\n")
print("For each m, what is the smallest orbit index i such that 2^{m+i} is")
print("an m-digit zeroless number?\n")

print(f"{'m':>3s}  {'L=ceil(Cm)':>10s}  {'min_surv':>10s}  {'min_surv/L':>10s}  {'any_in_[0,L)?':>14s}")
print("-" * 55)

for m in range(2, 35):
    L = int(np.ceil(C_const * m))
    mod_m = 10**m

    # Find minimal survivor index
    min_surv = None
    x = pow(2, m, mod_m)
    T_m = 4 * 5**(m-1)

    # Only need to check up to T_m, but for large m that's huge.
    # Check up to max(L*10, 10000) or T_m, whichever is smaller
    check_limit = min(T_m, max(L * 10, 10000))

    for i in range(check_limit):
        if is_zeroless(x, m):
            min_surv = i
            break
        x = (2 * x) % mod_m

    if min_surv is not None:
        in_range = "YES" if min_surv < L else "NO"
        print(f"{m:3d}  {L:10d}  {min_surv:10d}  {min_surv/L:10.3f}  {in_range:>14s}")
    else:
        print(f"{m:3d}  {L:10d}  {'> '+str(check_limit):>10s}  {'---':>10s}  {'NO':>14s}")

# =====================================================================
# Part D: Branching structure - how many of 5 children are admissible?
# =====================================================================
print("\n### Part D: Branching at each node (small-index branch) ###\n")
print("For each admissible node at level j that contains a small index,")
print("how many of its 5 children at level j+1 are also admissible?\n")

for m in [10, 15, 20]:
    L = int(np.ceil(C_const * m))
    print(f"m={m}, L={L}:")
    print(f"  {'j':>3s}  {'nodes':>6s}  {'0-child':>8s}  {'1-child':>8s}  {'2-child':>8s}  "
          f"{'3-child':>8s}  {'4-child':>8s}  {'5-child':>8s}  {'avg':>6s}")

    prev_admissible = None

    for j in range(1, min(m+1, 25)):
        T_j = 4 * 5**(j-1)
        mod_j = 10**j

        # Find admissible classes with small indices at level j
        classes_with_small = set()
        for i in range(L):
            classes_with_small.add(i % T_j)

        admissible = set()
        for r in classes_with_small:
            x = pow(2, m + r, mod_j)
            if digits_zero_free(x, j):
                admissible.add(r)

        if j >= 2 and prev_admissible is not None:
            T_prev = 4 * 5**(j-2)
            branching_hist = [0] * 6  # count nodes with 0,1,2,3,4,5 admissible children

            for r_prev in prev_admissible:
                n_admissible_children = 0
                for c in range(5):
                    child = (r_prev + c * T_prev) % T_j
                    if child in admissible:
                        n_admissible_children += 1
                branching_hist[n_admissible_children] += 1

            total = sum(branching_hist)
            avg = sum(k * branching_hist[k] for k in range(6)) / max(total, 1)
            print(f"  {j:3d}  {total:6d}  " +
                  "  ".join(f"{branching_hist[k]:8d}" for k in range(6)) +
                  f"  {avg:6.2f}")

        prev_admissible = admissible

        if len(admissible) == 0:
            print(f"  >>> EXTINCT at level {j} <<<")
            break

    print()

# =====================================================================
# Part E: Compare small-index vs generic branching
# =====================================================================
print("\n### Part E: Small-index vs generic branching rates ###\n")
print("Generic rate should be ~4.5/5 = 0.9 (each digit nonzero with prob 9/10).")
print("Small-index rate may be lower due to leading-digit bias.\n")

for m in [8, 10, 12]:
    L = int(np.ceil(C_const * m))

    # Generic branching: pick a random admissible node at level j,
    # count its admissible children at level j+1
    print(f"m={m}, L={L}:")
    print(f"  {'j':>3s}  {'small_rate':>12s}  {'generic_rate':>14s}  {'ratio':>8s}")

    for j in range(2, min(m+1, 15)):
        T_j = 4 * 5**(j-1)
        T_prev = 4 * 5**(j-2)
        mod_j = 10**j
        mod_prev = 10**(j-1)

        # Small-index admissible nodes at level j-1
        small_classes_prev = set()
        for i in range(L):
            small_classes_prev.add(i % T_prev)

        small_admissible_prev = set()
        for r in small_classes_prev:
            x = pow(2, m + r, mod_prev)
            if digits_zero_free(x, j-1):
                small_admissible_prev.add(r)

        # Their children at level j
        small_admissible_children = 0
        small_total_children = len(small_admissible_prev) * 5
        for r_prev in small_admissible_prev:
            for c in range(5):
                child = (r_prev + c * T_prev) % T_j
                x = pow(2, m + child, mod_j)
                if digits_zero_free(x, j):
                    small_admissible_children += 1

        small_rate = small_admissible_children / max(small_total_children, 1)

        # Generic branching: sample some admissible nodes at level j-1
        # (take first 200 admissible classes)
        generic_admissible_prev = []
        for r in range(T_prev):
            x = pow(2, m + r, mod_prev)
            if digits_zero_free(x, j-1):
                generic_admissible_prev.append(r)
                if len(generic_admissible_prev) >= 200:
                    break

        generic_children = 0
        generic_total = len(generic_admissible_prev) * 5
        for r_prev in generic_admissible_prev:
            for c in range(5):
                child = (r_prev + c * T_prev) % T_j
                x = pow(2, m + child, mod_j)
                if digits_zero_free(x, j):
                    generic_children += 1

        generic_rate = generic_children / max(generic_total, 1)
        ratio = small_rate / max(generic_rate, 0.001)

        print(f"  {j:3d}  {small_rate:12.4f}  {generic_rate:14.4f}  {ratio:8.4f}")

    print()

print("=" * 70)
print("EXPERIMENT 23 COMPLETE")
print("=" * 70)
