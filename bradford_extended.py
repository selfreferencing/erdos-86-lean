#!/usr/bin/env python3
"""Extended Bradford analysis on all 750 primes."""
import csv
from math import isqrt
from collections import Counter

def read_certs(path):
    certs = []
    with open(path) as f:
        for row in csv.DictReader(f):
            certs.append((int(row['p']), int(row['offset']),
                          int(row['b']), int(row['c'])))
    return certs

def bradford_search(p):
    """Find all x in [p/4+1, p/2] with delta ≡ 3 mod 4 and Bradford solution."""
    results = []
    lo = p // 4 + 1
    hi = p // 2
    for x in range(lo, hi + 1):
        delta = 4 * x - p
        if delta <= 0 or delta % 4 != 3:
            continue
        x_sq = x * x
        target = (-x) % delta
        for d in range(1, isqrt(x_sq) + 1):
            if x_sq % d == 0:
                if d % delta == target:
                    results.append((x, d, delta))
                    break
                comp = x_sq // d
                if comp % delta == target:
                    results.append((x, comp, delta))
                    break
    return results

certs = read_certs('/Users/kvallie2/Desktop/esc_stage8/witnesses_1000000.csv')
print(f"Analyzing Bradford on first 200 primes (full 750 too slow for exhaustive search)")

smallest_deltas = []
num_solutions = []
smallest_already_proven = 0

# D.6 proven M values in Existence.lean  
proven_Ms = {7, 11, 15, 19, 23}

for i, (p, delta_cert, b, c) in enumerate(certs[:200]):
    results = bradford_search(p)
    if not results:
        print(f"WARNING: No Bradford solution for p={p}")
        continue
    
    deltas = sorted(set(r[2] for r in results))
    smallest = deltas[0]
    smallest_deltas.append(smallest)
    num_solutions.append(len(deltas))
    
    # Check if smallest delta corresponds to an already-proven region
    # The proven M values in D.6 are for modular coverage
    # But here we're checking individual delta values
    if smallest <= 23:
        smallest_already_proven += 1

# Statistics
print(f"\nSmallest delta distribution:")
ctr = Counter(smallest_deltas)
for d, cnt in sorted(ctr.items()):
    print(f"  delta={d}: {cnt} primes ({100*cnt/len(smallest_deltas):.1f}%)")

print(f"\nSmallest delta ≤ 23: {smallest_already_proven}/200 ({100*smallest_already_proven/200:.1f}%)")
print(f"\nNumber of working deltas per prime:")
print(f"  min: {min(num_solutions)}")
print(f"  max: {max(num_solutions)}")
print(f"  mean: {sum(num_solutions)/len(num_solutions):.1f}")
print(f"  median: {sorted(num_solutions)[len(num_solutions)//2]}")

# Key question: can we always find delta ≡ 3 mod 4 with delta < sqrt(p)?
sqrt_solutions = 0
for i, (p, delta_cert, b, c) in enumerate(certs[:200]):
    results = bradford_search(p)
    if not results:
        continue
    smallest = min(r[2] for r in results)
    if smallest < isqrt(p):
        sqrt_solutions += 1

print(f"\nSmallest delta < sqrt(p): {sqrt_solutions}/200 ({100*sqrt_solutions/200:.1f}%)")

# Check: among smallest-delta solutions, what are the b values?
print(f"\nSmallest-delta solutions for first 20 primes:")
for i, (p, delta_cert, b_cert, c_cert) in enumerate(certs[:20]):
    results = bradford_search(p)
    if not results:
        continue
    smallest_d = min(r[2] for r in results)
    # Find the result with smallest delta
    for x, d, delta in sorted(results, key=lambda r: r[2]):
        if delta == smallest_d:
            A = x
            # Reconstruct b, c
            u = d
            v = A * A // d
            b_new = (u + A) // delta
            c_new = (v + A) // delta
            print(f"  p={p}: delta={delta}, x=A={A}, d={d}, b={b_new}, c={c_new} "
                  f"(cert: delta={delta_cert}, b={b_cert}, c={c_cert})")
            break
