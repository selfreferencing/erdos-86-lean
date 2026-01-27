#!/usr/bin/env python3
"""Verify Bradford reduction (L1B Strategy 3) = L4A characterization.

Bradford: find x in [p/4, p/2] with d | x^2, d ≡ -x mod (4x-p)
L4A: find u | A^2 with u ≡ -A mod delta, where A = (p+delta)/4

When x = A: 4x - p = 4A - p = delta, and the conditions are identical.
So Bradford for x=A IS L4A. But Bradford allows varying x.
"""
import csv
from math import isqrt, gcd

def read_certs(path):
    certs = []
    with open(path) as f:
        for row in csv.DictReader(f):
            certs.append((int(row['p']), int(row['offset']),
                          int(row['b']), int(row['c'])))
    return certs

def bradford_search(p, x_max=None):
    """Find all x in [p/4, p/2] with Bradford solution.
    Returns list of (x, d, delta) tuples."""
    results = []
    lo = p // 4 + 1  # x > p/4 so delta > 0
    hi = p // 2
    if x_max is not None:
        hi = min(hi, lo + x_max)
    for x in range(lo, hi + 1):
        delta = 4 * x - p
        if delta <= 0 or delta % 4 != 3:
            continue
        x_sq = x * x
        # Find divisors d of x^2 with d ≡ -x mod delta
        target = (-x) % delta
        for d in range(1, isqrt(x_sq) + 1):
            if x_sq % d == 0:
                if d % delta == target:
                    results.append((x, d, delta))
                    break  # one divisor suffices
                comp = x_sq // d
                if comp % delta == target:
                    results.append((x, comp, delta))
                    break
    return results

def main():
    certs = read_certs('/Users/kvallie2/Desktop/esc_stage8/witnesses_1000000.csv')
    print(f"Loaded {len(certs)} certificates")
    
    # 1. Verify x=A is in [p/4, p/2] for all certs
    in_range = 0
    for p, delta, b, c in certs:
        A = (p + delta) // 4
        if A > p // 4 and A <= p // 2:
            in_range += 1
    print(f"\n1. A in (p/4, p/2]: {in_range}/{len(certs)} ({100*in_range/len(certs):.1f}%)")
    
    # Show a few that might be out of range
    out = []
    for p, delta, b, c in certs:
        A = (p + delta) // 4
        if A <= p // 4 or A > p // 2:
            out.append((p, delta, A, p//4, p//2))
    if out:
        print(f"   Out of range examples: {out[:5]}")
    
    # 2. Verify Bradford condition = L4A for x=A
    # For x=A: 4x-p = delta, and d|x^2 with d ≡ -x mod (4x-p)
    #        = d|A^2 with d ≡ -A mod delta  (= L4A)
    match = 0
    for p, delta, b, c in certs:
        A = (p + delta) // 4
        u_l4 = delta * b - A
        # Check: u_l4 | A^2 and u_l4 ≡ -A mod delta
        if A * A % u_l4 == 0 and u_l4 % delta == (-A) % delta:
            match += 1
    print(f"2. L4A condition verified (u|A^2, u≡-A mod delta): {match}/{len(certs)}")
    
    # 3. For small primes, count ALL working x values
    print(f"\n3. Bradford solution counts for first 50 primes:")
    small_certs = certs[:50]
    for p, delta, b, c in small_certs[:10]:
        A = (p + delta) // 4
        results = bradford_search(p)
        x_values = set(r[0] for r in results)
        delta_values = set(r[2] for r in results)
        print(f"   p={p}: {len(x_values)} working x values, "
              f"{len(delta_values)} working deltas, "
              f"cert A={A} (delta={delta}), "
              f"smallest x={min(x_values) if x_values else 'NONE'}, "
              f"smallest delta={min(delta_values) if delta_values else 'NONE'}")
    
    # 4. For first 50 primes: compare cert delta to smallest Bradford delta
    print(f"\n4. Certificate delta vs smallest Bradford delta (first 50):")
    cert_is_smallest = 0
    total_checked = 0
    total_bradford_solutions = 0
    
    for p, delta, b, c in small_certs:
        results = bradford_search(p)
        if not results:
            continue
        total_checked += 1
        total_bradford_solutions += len(set(r[0] for r in results))
        smallest_delta = min(r[2] for r in results)
        if delta == smallest_delta:
            cert_is_smallest += 1
    
    print(f"   Checked: {total_checked}/50")
    print(f"   Cert uses smallest delta: {cert_is_smallest}/{total_checked}")
    print(f"   Avg Bradford solutions per prime: {total_bradford_solutions/total_checked:.1f}")
    
    # 5. Key structural insight: Bradford = L4A + freedom to vary delta
    print(f"\n5. KEY STRUCTURAL INSIGHT:")
    print(f"   Bradford's x = our A = (p+delta)/4")
    print(f"   Bradford's modulus (4x-p) = our delta")
    print(f"   Bradford condition = L4A for each fixed delta")
    print(f"   Bradford adds: freedom to search over ALL delta ≡ 3 mod 4")
    print(f"   This is exactly what our certificate search does!")
    
    # 6. For a few primes, show detailed Bradford decomposition
    print(f"\n6. Detailed Bradford analysis for selected primes:")
    for p, delta, b, c in certs[:5]:
        A = (p + delta) // 4
        results = bradford_search(p)
        print(f"\n   p={p} (cert: delta={delta}, b={b}, c={c}, A={A}):")
        for x, d, delt in sorted(results)[:5]:
            a_val = x
            # Reconstruct b, c from Bradford: d | A^2, d ≡ -A mod delta
            # u = d, v = A^2/d, b = (u+A)/delta, c = (v+A)/delta
            v = a_val * a_val // d
            b_new = (d + a_val) // delt
            c_new = (v + a_val) // delt
            print(f"     x={x}, delta={delt}, d={d}: "
                  f"b={(d+a_val)/delt:.1f}, c={(v+a_val)/delt:.1f}")

if __name__ == '__main__':
    main()
