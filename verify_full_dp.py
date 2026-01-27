#!/usr/bin/env python3
"""
Full verification: enumerate ALL DP congruences at Q = 857,656,800
and check if D6 + all DP achieves 100% coverage.
"""

import time
from math import gcd
from collections import defaultdict

def lcm2(a, b):
    return a * b // gcd(a, b)

def divisors(n):
    if n <= 0: return []
    small, large = [], []
    i = 1
    while i * i <= n:
        if n % i == 0:
            small.append(i)
            if i != n // i:
                large.append(n // i)
        i += 1
    return small + large[::-1]

def odd_part(n):
    while n % 2 == 0:
        n //= 2
    return n

def get_residues_for_M(M):
    k = (M + 1) // 4
    if 4 * k - 1 != M:
        return set()
    seen = set()
    for a in divisors(k):
        rem = k // a
        for s in divisors(rem):
            res = (-4 * a * s * s) % M
            seen.add(res)
    return seen


def main():
    t0 = time.time()
    Q = 857_656_800
    Q4 = Q // 4
    
    print(f"Q = {Q:,}")
    print(f"Q/4 = {Q4:,}")
    
    # Step 1: Build D6 data
    print(f"\nBuilding D6 data...")
    oQ = odd_part(Q)
    M_values = sorted([d for d in divisors(oQ) if d % 4 == 3 and d >= 3])
    M_data = {}
    for M in M_values:
        res = get_residues_for_M(M)
        if res:
            M_data[M] = res
    print(f"  {len(M_data)} M-values with residues")
    
    # Step 2: Enumerate ALL DP congruences
    print(f"\nEnumerating DP congruences...")
    divs_Q4 = divisors(Q4)
    print(f"  Divisors of Q/4: {len(divs_Q4)}")
    
    dp_congruences = []
    seen = set()
    for u in divs_Q4:
        for v in divs_Q4:
            delta = u + v
            if delta % 4 != 3:
                continue
            L = lcm2(u, v)
            if Q4 % L != 0:
                continue
            modulus = 4 * L
            res = (-delta) % modulus
            g = gcd(modulus, 24)
            if res % g != 1 % g:
                continue
            key = (modulus, res)
            if key not in seen:
                seen.add(key)
                dp_congruences.append((modulus, res))
    
    t1 = time.time()
    print(f"  Found {len(dp_congruences)} DP congruences in {t1-t0:.1f}s")
    
    # Step 3: Iterate targets, check D6 then DP
    print(f"\nChecking coverage (single pass)...")
    
    total_targets = 0
    d6_count = 0
    dp_count = 0
    uncov_count = 0
    uncov_sample = []  # keep first 1000
    
    check_interval = Q // 240
    next_report = check_interval
    
    for x in range(1, Q, 24):
        if gcd(x, Q) != 1:
            continue
        total_targets += 1
        
        # D6 check
        found = False
        for M, residues in M_data.items():
            if x % M in residues:
                found = True
                d6_count += 1
                break
        
        if not found:
            # DP check
            for mod, res in dp_congruences:
                if x % mod == res:
                    found = True
                    dp_count += 1
                    break
        
        if not found:
            uncov_count += 1
            if len(uncov_sample) < 1000:
                uncov_sample.append(x)
        
        if x > next_report:
            pct = 100 * x / Q
            elapsed = time.time() - t0
            print(f"  {pct:.1f}%: {total_targets:,} targets, "
                  f"{d6_count:,} D6, {dp_count:,} DP, {uncov_count} uncov "
                  f"[{elapsed:.0f}s]")
            next_report += check_interval
    
    # Results
    print(f"\n{'='*80}")
    print("RESULTS")
    print(f"{'='*80}")
    print(f"Q = {Q:,}")
    print(f"Targets: {total_targets:,}")
    print(f"D6 covered: {d6_count:,} ({100*d6_count/total_targets:.4f}%)")
    print(f"DP covered: {dp_count:,} ({100*dp_count/total_targets:.4f}%)")
    print(f"Uncovered: {uncov_count}")
    
    if uncov_count == 0:
        print(f"\n*** COMPLETE COVERING VERIFIED! ***")
    else:
        print(f"\n{uncov_count} uncovered:")
        for x in uncov_sample[:30]:
            print(f"  x={x}: mod5={x%5}, mod7={x%7}, mod11={x%11}, "
                  f"mod13={x%13}, mod17={x%17}, mod49={x%49}, mod25={x%25}")
        
        # Residue analysis
        print(f"\nResidue patterns:")
        for p in [5, 7, 11, 13, 17, 25, 49]:
            dist = defaultdict(int)
            for x in uncov_sample:
                dist[x % p] += 1
            print(f"  mod {p}: {dict(sorted(dist.items()))}")
    
    print(f"\nTotal time: {time.time()-t0:.1f}s")


if __name__ == "__main__":
    main()
