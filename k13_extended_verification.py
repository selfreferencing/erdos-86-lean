#!/usr/bin/env python3
"""
Extended K13 Coverage Verification for Erdős-Straus Conjecture

Optimized for verifying Mordell-hard primes up to 10^8.
Uses fast witness checking and parallel processing.

Author: Generated for Vallier ESC project
"""

import sys
import time
from math import gcd, isqrt
from collections import defaultdict, Counter
from multiprocessing import Pool, cpu_count

# =============================================================================
# CONSTANTS
# =============================================================================

K13 = [0, 1, 2, 5, 7, 9, 11, 14, 17, 19, 23, 26, 29]
K10 = [5, 7, 9, 11, 14, 17, 19, 23, 26, 29]  # Original K10 for comparison
MORDELL_HARD = [1, 121, 169, 289, 361, 529]
M_K_CACHE = {k: 4*k + 3 for k in K13}

# =============================================================================
# OPTIMIZED UTILITY FUNCTIONS
# =============================================================================

def is_prime(n):
    """Miller-Rabin primality test for efficiency."""
    if n < 2:
        return False
    if n == 2 or n == 3:
        return True
    if n % 2 == 0:
        return False
    if n < 9:
        return True
    if n % 3 == 0:
        return False

    # Write n-1 as 2^r * d
    r, d = 0, n - 1
    while d % 2 == 0:
        r += 1
        d //= 2

    # Witnesses to test (sufficient for n < 3,317,044,064,679,887,385,961,981)
    witnesses = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37]

    for a in witnesses:
        if a >= n:
            continue
        x = pow(a, d, n)
        if x == 1 or x == n - 1:
            continue
        for _ in range(r - 1):
            x = pow(x, 2, n)
            if x == n - 1:
                break
        else:
            return False
    return True

def m_k(k):
    """Return m_k = 4k + 3."""
    return M_K_CACHE[k]

def x_k(p, k):
    """Return x_k = (p + m_k)/4 if divisible, else None."""
    m = M_K_CACHE[k]
    if (p + m) % 4 == 0:
        return (p + m) // 4
    return None

def has_witness_fast(p, k):
    """
    Optimized witness check: only check divisors d where d ≡ -x (mod m).

    Returns (has_witness, smallest_d) or (False, None).
    """
    m = M_K_CACHE[k]
    x = x_k(p, k)
    if x is None:
        return False, None

    target = (-x) % m
    if target == 0:
        target = m

    x_sq = x * x

    # Check d = target, target + m, target + 2m, ... up to x
    d = target
    while d <= x:
        if d > 0 and x_sq % d == 0:
            return True, d
        d += m

    return False, None

def has_witness_any_k(p, k_set=K13):
    """Check if any k in k_set provides a witness for prime p."""
    for k in k_set:
        has_wit, d = has_witness_fast(p, k)
        if has_wit:
            return True, k, d
    return False, None, None

def count_working_ks(p, k_set=K13):
    """Count how many k values provide witnesses for prime p."""
    count = 0
    working = []
    for k in k_set:
        has_wit, d = has_witness_fast(p, k)
        if has_wit:
            count += 1
            working.append((k, d))
    return count, working

# =============================================================================
# PRIME GENERATION
# =============================================================================

def sieve_mordell_hard(limit):
    """
    Generate Mordell-hard primes up to limit using segmented sieve.
    Returns list of primes p where p ≡ r (mod 840) for r in MORDELL_HARD.
    """
    # Simple sieve for moderate limits
    if limit <= 10**7:
        sieve = [True] * (limit + 1)
        sieve[0] = sieve[1] = False
        for i in range(2, isqrt(limit) + 1):
            if sieve[i]:
                for j in range(i*i, limit + 1, i):
                    sieve[j] = False

        mordell_primes = []
        for p in range(2, limit + 1):
            if sieve[p] and (p % 840) in MORDELL_HARD:
                mordell_primes.append(p)
        return mordell_primes

    # For larger limits, use segmented approach
    segment_size = 10**6
    mordell_primes = []

    # First get small primes for sieving
    small_limit = isqrt(limit) + 1
    small_sieve = [True] * (small_limit + 1)
    small_sieve[0] = small_sieve[1] = False
    for i in range(2, isqrt(small_limit) + 1):
        if small_sieve[i]:
            for j in range(i*i, small_limit + 1, i):
                small_sieve[j] = False
    small_primes = [i for i in range(2, small_limit + 1) if small_sieve[i]]

    # Process segments
    for low in range(0, limit + 1, segment_size):
        high = min(low + segment_size - 1, limit)
        segment = [True] * (high - low + 1)

        for p in small_primes:
            if p * p > high:
                break
            start = max(p * p, ((low + p - 1) // p) * p)
            for j in range(start - low, high - low + 1, p):
                segment[j] = False

        for i in range(len(segment)):
            n = low + i
            if n > 1 and segment[i] and (n % 840) in MORDELL_HARD:
                mordell_primes.append(n)

    return mordell_primes

# =============================================================================
# VERIFICATION WORKER
# =============================================================================

def verify_prime(p):
    """
    Verify K13 coverage for a single prime.
    Returns (p, num_working_k13, num_working_k10, has_any_witness, details).
    """
    count_k13, working_k13 = count_working_ks(p, K13)
    count_k10, working_k10 = count_working_ks(p, K10)

    has_witness = count_k13 > 0

    # Only return details for interesting cases
    details = None
    if count_k13 <= 2 or count_k10 == 0:
        details = {
            'p': p,
            'p_mod_840': p % 840,
            'working_k13': working_k13,
            'working_k10': working_k10
        }

    return (p, count_k13, count_k10, has_witness, details)

def verify_batch(primes):
    """Verify a batch of primes."""
    results = []
    for p in primes:
        results.append(verify_prime(p))
    return results

# =============================================================================
# MAIN VERIFICATION
# =============================================================================

def run_verification(limit, use_parallel=True, checkpoint_interval=10**6):
    """
    Run full verification up to limit.

    Returns dict with:
    - total_primes: number of Mordell-hard primes checked
    - failures: list of primes with no K13 witness (should be empty)
    - k10_failures: list of primes with no K10 witness
    - hard_cases: primes with ≤2 working k values
    - distribution: Counter of working k counts
    - by_residue: stats broken down by Mordell-hard residue class
    """
    print(f"K13 Extended Verification up to {limit:,}")
    print("=" * 70)
    print()

    # Generate primes
    print("Generating Mordell-hard primes...")
    start_time = time.time()
    primes = sieve_mordell_hard(limit)
    gen_time = time.time() - start_time
    print(f"Found {len(primes):,} Mordell-hard primes in {gen_time:.1f}s")
    print()

    # Initialize tracking
    failures_k13 = []
    failures_k10 = []
    hard_cases = []
    distribution_k13 = Counter()
    distribution_k10 = Counter()
    by_residue = {r: {'count': 0, 'failures': 0, 'min_k': float('inf')}
                  for r in MORDELL_HARD}

    # Verify
    print("Verifying coverage...")
    start_time = time.time()

    if use_parallel and len(primes) > 10000:
        # Parallel processing for large sets
        num_workers = max(1, cpu_count() - 1)
        batch_size = max(1000, len(primes) // (num_workers * 10))
        batches = [primes[i:i+batch_size] for i in range(0, len(primes), batch_size)]

        print(f"Using {num_workers} workers, {len(batches)} batches of ~{batch_size}")

        processed = 0
        with Pool(num_workers) as pool:
            for batch_results in pool.imap_unordered(verify_batch, batches):
                for p, count_k13, count_k10, has_witness, details in batch_results:
                    distribution_k13[count_k13] += 1
                    distribution_k10[count_k10] += 1

                    residue = p % 840
                    by_residue[residue]['count'] += 1
                    by_residue[residue]['min_k'] = min(by_residue[residue]['min_k'], count_k13)

                    if not has_witness:
                        failures_k13.append(details)
                        by_residue[residue]['failures'] += 1

                    if count_k10 == 0:
                        failures_k10.append(details or {'p': p, 'p_mod_840': residue})

                    if count_k13 <= 2:
                        hard_cases.append(details or {'p': p, 'count': count_k13})

                processed += len(batch_results)
                if processed % checkpoint_interval < batch_size:
                    elapsed = time.time() - start_time
                    rate = processed / elapsed
                    remaining = (len(primes) - processed) / rate
                    print(f"  Processed {processed:,}/{len(primes):,} "
                          f"({100*processed/len(primes):.1f}%) - "
                          f"ETA: {remaining:.0f}s")
    else:
        # Sequential processing
        for i, p in enumerate(primes):
            p, count_k13, count_k10, has_witness, details = verify_prime(p)

            distribution_k13[count_k13] += 1
            distribution_k10[count_k10] += 1

            residue = p % 840
            by_residue[residue]['count'] += 1
            by_residue[residue]['min_k'] = min(by_residue[residue]['min_k'], count_k13)

            if not has_witness:
                failures_k13.append(details)
                by_residue[residue]['failures'] += 1

            if count_k10 == 0:
                failures_k10.append(details or {'p': p, 'p_mod_840': residue})

            if count_k13 <= 2:
                hard_cases.append(details or {'p': p, 'count': count_k13})

            if (i + 1) % checkpoint_interval == 0:
                elapsed = time.time() - start_time
                rate = (i + 1) / elapsed
                remaining = (len(primes) - i - 1) / rate
                print(f"  Processed {i+1:,}/{len(primes):,} - ETA: {remaining:.0f}s")

    verify_time = time.time() - start_time

    # Report results
    print()
    print("=" * 70)
    print("VERIFICATION RESULTS")
    print("=" * 70)
    print()
    print(f"Total Mordell-hard primes verified: {len(primes):,}")
    print(f"Verification time: {verify_time:.1f}s ({len(primes)/verify_time:.0f} primes/sec)")
    print()

    print("K13 COVERAGE:")
    print("-" * 40)
    if failures_k13:
        print(f"  FAILURES: {len(failures_k13)} primes with no K13 witness!")
        for f in failures_k13[:10]:
            print(f"    p = {f['p']}")
    else:
        print("  ✓ ALL PRIMES COVERED by K13")
    print()

    print("K10 COVERAGE:")
    print("-" * 40)
    if failures_k10:
        print(f"  Primes without K10 witness: {len(failures_k10)}")
        for f in failures_k10[:5]:
            print(f"    p = {f['p']} (mod 840 = {f['p_mod_840']})")
        if len(failures_k10) > 5:
            print(f"    ... and {len(failures_k10) - 5} more")
    else:
        print("  ✓ ALL PRIMES COVERED by K10")
    print()

    print("Distribution of working k values (K13):")
    print("-" * 40)
    for n in sorted(distribution_k13.keys()):
        pct = 100 * distribution_k13[n] / len(primes)
        bar = "█" * int(pct / 2)
        print(f"  {n:>2} k's: {distribution_k13[n]:>8,} ({pct:>5.1f}%) {bar}")

    avg_k13 = sum(n * c for n, c in distribution_k13.items()) / len(primes)
    min_k13 = min(distribution_k13.keys())
    max_k13 = max(distribution_k13.keys())
    print()
    print(f"  Min: {min_k13}, Max: {max_k13}, Average: {avg_k13:.2f}")
    print()

    print("Coverage by Mordell-hard residue class:")
    print("-" * 40)
    for r in MORDELL_HARD:
        stats = by_residue[r]
        status = "✓" if stats['failures'] == 0 else "✗"
        print(f"  p ≡ {r:>3} (mod 840): {stats['count']:>8,} primes, "
              f"min_k={stats['min_k']:>2}, failures={stats['failures']} {status}")
    print()

    if hard_cases:
        print(f"Hard cases (≤2 working k values): {len(hard_cases)}")
        print("-" * 40)
        for case in hard_cases[:20]:
            p = case.get('p', case)
            print(f"  p = {p}")
        if len(hard_cases) > 20:
            print(f"  ... and {len(hard_cases) - 20} more")
    print()

    return {
        'limit': limit,
        'total_primes': len(primes),
        'failures_k13': failures_k13,
        'failures_k10': failures_k10,
        'hard_cases': hard_cases,
        'distribution_k13': dict(distribution_k13),
        'distribution_k10': dict(distribution_k10),
        'by_residue': by_residue,
        'avg_working_k13': avg_k13,
        'min_working_k13': min_k13,
        'verify_time': verify_time
    }

def save_results(results, filename):
    """Save results to file."""
    with open(filename, 'w') as f:
        f.write("K13 EXTENDED VERIFICATION RESULTS\n")
        f.write("=" * 70 + "\n\n")
        f.write(f"Limit: {results['limit']:,}\n")
        f.write(f"Total Mordell-hard primes: {results['total_primes']:,}\n")
        f.write(f"Verification time: {results['verify_time']:.1f}s\n\n")

        f.write("K13 COVERAGE\n")
        f.write("-" * 40 + "\n")
        if results['failures_k13']:
            f.write(f"FAILURES: {len(results['failures_k13'])}\n")
            for fail in results['failures_k13']:
                f.write(f"  p = {fail['p']}\n")
        else:
            f.write("ALL PRIMES COVERED\n")
        f.write("\n")

        f.write("K10 COVERAGE\n")
        f.write("-" * 40 + "\n")
        if results['failures_k10']:
            f.write(f"Failures: {len(results['failures_k10'])}\n")
            for fail in results['failures_k10'][:100]:
                f.write(f"  p = {fail['p']}\n")
        else:
            f.write("ALL PRIMES COVERED\n")
        f.write("\n")

        f.write("DISTRIBUTION (K13)\n")
        f.write("-" * 40 + "\n")
        for n in sorted(results['distribution_k13'].keys()):
            count = results['distribution_k13'][n]
            pct = 100 * count / results['total_primes']
            f.write(f"  {n:>2} working k's: {count:>10,} ({pct:>5.1f}%)\n")
        f.write(f"\nMin: {results['min_working_k13']}, Average: {results['avg_working_k13']:.2f}\n\n")

        f.write("BY RESIDUE CLASS\n")
        f.write("-" * 40 + "\n")
        for r in MORDELL_HARD:
            stats = results['by_residue'][r]
            f.write(f"  p ≡ {r:>3} (mod 840): {stats['count']:>8,} primes, "
                   f"min_k={stats['min_k']}, failures={stats['failures']}\n")
        f.write("\n")

        if results['hard_cases']:
            f.write(f"HARD CASES (≤2 working k's): {len(results['hard_cases'])}\n")
            f.write("-" * 40 + "\n")
            for case in results['hard_cases'][:100]:
                f.write(f"  p = {case.get('p', case)}\n")
            if len(results['hard_cases']) > 100:
                f.write(f"  ... and {len(results['hard_cases']) - 100} more\n")

    print(f"Results saved to {filename}")

# =============================================================================
# MAIN
# =============================================================================

if __name__ == "__main__":
    # Default limit
    limit = 10**7  # Start with 10^7, can increase

    if len(sys.argv) > 1:
        try:
            limit = int(float(sys.argv[1]))
        except ValueError:
            print(f"Usage: {sys.argv[0]} [limit]")
            print(f"  limit: upper bound for verification (default: 10^7)")
            sys.exit(1)

    results = run_verification(limit)

    # Save results
    filename = f"/Users/kvallie2/Desktop/esc_stage8/k13_verification_{limit}.txt"
    save_results(results, filename)

    # Summary
    print("=" * 70)
    print("SUMMARY")
    print("=" * 70)
    if not results['failures_k13']:
        print(f"✓ K13 covers ALL {results['total_primes']:,} Mordell-hard primes up to {limit:,}")
    else:
        print(f"✗ K13 FAILED on {len(results['failures_k13'])} primes")

    if not results['failures_k10']:
        print(f"✓ K10 covers ALL {results['total_primes']:,} Mordell-hard primes up to {limit:,}")
    else:
        print(f"  K10 failed on {len(results['failures_k10'])} primes (K13 provides backup)")
