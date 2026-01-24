#!/usr/bin/env python3
"""
Fast K13 verification - single-threaded with progress updates.
"""

import sys
import time
from math import gcd, isqrt
from collections import Counter

K13 = [0, 1, 2, 5, 7, 9, 11, 14, 17, 19, 23, 26, 29]
K10 = [5, 7, 9, 11, 14, 17, 19, 23, 26, 29]
MORDELL_HARD = [1, 121, 169, 289, 361, 529]
M_K = {k: 4*k + 3 for k in K13}

def is_prime(n):
    if n < 2: return False
    if n == 2 or n == 3: return True
    if n % 2 == 0 or n % 3 == 0: return False
    i = 5
    while i * i <= n:
        if n % i == 0 or n % (i + 2) == 0: return False
        i += 6
    return True

def x_k(p, k):
    m = M_K[k]
    return (p + m) // 4 if (p + m) % 4 == 0 else None

def has_witness(p, k):
    m = M_K[k]
    x = x_k(p, k)
    if x is None: return False
    target = (-x) % m
    if target == 0: target = m
    x_sq = x * x
    d = target
    while d <= x:
        if d > 0 and x_sq % d == 0:
            return True
        d += m
    return False

def count_working(p, k_set):
    return sum(1 for k in k_set if has_witness(p, k))

def main():
    limit = int(float(sys.argv[1])) if len(sys.argv) > 1 else 10**7

    print(f"K13 Fast Verification up to {limit:,}")
    print("=" * 60)

    # Generate primes
    print("Sieving primes...", flush=True)
    t0 = time.time()
    sieve = [True] * (limit + 1)
    sieve[0] = sieve[1] = False
    for i in range(2, isqrt(limit) + 1):
        if sieve[i]:
            sieve[i*i::i] = [False] * len(sieve[i*i::i])

    primes = [p for p in range(2, limit + 1) if sieve[p] and (p % 840) in MORDELL_HARD]
    print(f"Found {len(primes):,} Mordell-hard primes in {time.time()-t0:.1f}s")

    # Verify
    print("\nVerifying...", flush=True)
    t0 = time.time()

    failures_k13 = []
    failures_k10 = []
    dist_k13 = Counter()
    hard_cases = []
    by_class = {r: 0 for r in MORDELL_HARD}

    for i, p in enumerate(primes):
        n13 = count_working(p, K13)
        n10 = count_working(p, K10)

        dist_k13[n13] += 1
        by_class[p % 840] += 1

        if n13 == 0:
            failures_k13.append(p)
        if n10 == 0:
            failures_k10.append(p)
        if n13 <= 2:
            hard_cases.append((p, n13))

        if (i + 1) % 10000 == 0:
            elapsed = time.time() - t0
            rate = (i + 1) / elapsed
            eta = (len(primes) - i - 1) / rate
            print(f"  {i+1:,}/{len(primes):,} ({100*(i+1)/len(primes):.1f}%) "
                  f"- {rate:.0f}/s - ETA {eta:.0f}s", flush=True)

    elapsed = time.time() - t0
    print(f"\nCompleted in {elapsed:.1f}s ({len(primes)/elapsed:.0f} primes/sec)")

    # Results
    print("\n" + "=" * 60)
    print("RESULTS")
    print("=" * 60)

    print(f"\nK13: {'✓ ALL COVERED' if not failures_k13 else f'✗ {len(failures_k13)} FAILURES'}")
    if failures_k13:
        print(f"  Failures: {failures_k13[:10]}")

    print(f"K10: {'✓ ALL COVERED' if not failures_k10 else f'{len(failures_k10)} primes need K13 backup'}")
    if failures_k10 and len(failures_k10) <= 50:
        print(f"  K10 failures: {failures_k10}")

    print(f"\nDistribution (K13):")
    for n in sorted(dist_k13):
        pct = 100 * dist_k13[n] / len(primes)
        print(f"  {n:>2} working: {dist_k13[n]:>8,} ({pct:>5.1f}%)")

    avg = sum(n * c for n, c in dist_k13.items()) / len(primes)
    print(f"\n  Min: {min(dist_k13)}, Max: {max(dist_k13)}, Avg: {avg:.2f}")

    print(f"\nHard cases (≤2 working): {len(hard_cases)}")
    if hard_cases:
        for p, n in hard_cases[:20]:
            print(f"  p={p} ({n} working)")

    # Save
    outfile = f"/Users/kvallie2/Desktop/esc_stage8/k13_verify_{limit}.txt"
    with open(outfile, 'w') as f:
        f.write(f"K13 Verification up to {limit:,}\n")
        f.write(f"Primes: {len(primes):,}\n")
        f.write(f"K13 failures: {len(failures_k13)}\n")
        f.write(f"K10 failures: {len(failures_k10)}\n")
        f.write(f"Min working: {min(dist_k13)}\n")
        f.write(f"Avg working: {avg:.2f}\n\n")
        f.write(f"Distribution:\n")
        for n in sorted(dist_k13):
            f.write(f"  {n}: {dist_k13[n]}\n")
        f.write(f"\nK10 failures:\n{failures_k10}\n")
        f.write(f"\nHard cases:\n{hard_cases}\n")
    print(f"\nSaved to {outfile}")

if __name__ == "__main__":
    main()
