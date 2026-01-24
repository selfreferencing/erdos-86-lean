#!/usr/bin/env python3
"""
ESC Full Analysis - Extended to 1M primes
"""

from math import gcd, isqrt
from collections import Counter
import csv
import time

def sieve_primes(limit):
    """Sieve of Eratosthenes"""
    is_prime = [True] * (limit + 1)
    is_prime[0] = is_prime[1] = False
    for i in range(2, isqrt(limit) + 1):
        if is_prime[i]:
            for j in range(i*i, limit + 1, i):
                is_prime[j] = False
    return [i for i in range(2, limit + 1) if is_prime[i]]

print("Generating primes up to 1,000,000...")
ALL_PRIMES = sieve_primes(1000000)
PRIME_SET = set(ALL_PRIMES)
print(f"Generated {len(ALL_PRIMES)} primes")

def is_prime(n):
    if n <= 1:
        return False
    if n in PRIME_SET:
        return True
    if n <= ALL_PRIMES[-1]:
        return False
    # For larger n, trial division
    if n % 2 == 0:
        return False
    for p in ALL_PRIMES:
        if p * p > n:
            return True
        if n % p == 0:
            return False
    return True

def factorize(n):
    """Return list of (prime, exponent) pairs"""
    if n <= 1:
        return []
    factors = []
    for p in ALL_PRIMES:
        if p * p > n:
            break
        if n % p == 0:
            exp = 0
            while n % p == 0:
                exp += 1
                n //= p
            factors.append((p, exp))
    if n > 1:
        factors.append((n, 1))
    return factors

def prime_factors(n):
    """Return set of distinct prime factors"""
    return {p for p, e in factorize(n)}

def get_divisors(n):
    """Get all divisors of n"""
    if n <= 0:
        return []
    factors = factorize(n)
    if not factors:
        return [1]
    divs = [1]
    for p, e in factors:
        new_divs = []
        pk = 1
        for _ in range(e + 1):
            new_divs.extend([d * pk for d in divs])
            pk *= p
        divs = new_divs
    return sorted(set(divs))

def G(n, m):
    """Count coprime divisor pairs (a, b) with a + b ≡ 0 (mod m)"""
    divs = get_divisors(n)
    count = 0
    for i, a in enumerate(divs):
        for b in divs[i+1:]:
            if gcd(a, b) == 1 and (a + b) % m == 0:
                count += 1
    return count

def legendre_symbol(a, p):
    """Compute Legendre symbol (a/p)"""
    a = a % p
    if a == 0:
        return 0
    ls = pow(a, (p - 1) // 2, p)
    return -1 if ls == p - 1 else ls

def jacobi_symbol(a, n):
    """Compute Jacobi symbol (a/n)"""
    if n <= 0 or n % 2 == 0:
        raise ValueError("n must be positive odd")
    a = a % n
    result = 1
    while a != 0:
        while a % 2 == 0:
            a //= 2
            if n % 8 in [3, 5]:
                result = -result
        a, n = n, a
        if a % 4 == 3 and n % 4 == 3:
            result = -result
        a = a % n
    return result if n == 1 else 0

# QR subgroups
QR_SUBGROUPS = {
    3: {1},
    7: {1, 2, 4},
    11: {1, 3, 4, 5, 9},
    15: {1, 2, 4, 8},
    19: {1, 4, 5, 6, 7, 9, 11, 16, 17},
    23: {1, 2, 3, 4, 6, 8, 9, 12, 13, 16, 18},
}

def get_qr_subgroup(m):
    if m in QR_SUBGROUPS:
        return QR_SUBGROUPS[m]
    if is_prime(m):
        return {x for x in range(1, m) if legendre_symbol(x, m) == 1}
    return {x for x in range(1, m) if gcd(x, m) == 1 and jacobi_symbol(x, m) == 1}

def is_qr_trapped(n, m):
    """All prime factors of n are in QR subgroup mod m"""
    qr_set = get_qr_subgroup(m)
    for p in prime_factors(n):
        if p % m not in qr_set and p != m:
            return False
    return True

def type_i_succeeds(p, k):
    """Check if Type I succeeds at k"""
    if k == 0:
        return False
    N = k * p + 1
    target = (-p) % (4 * k)
    for d in get_divisors(N):
        if d % (4 * k) == target:
            return True
    return False

def type_i_witness(p, k):
    """Find Type I witness"""
    if k == 0:
        return None
    N = k * p + 1
    target = (-p) % (4 * k)
    for d in get_divisors(N):
        if d % (4 * k) == target:
            return d
    return None

def is_dangerous_G(p, max_k=5):
    """Check if Type II (G=0) fails at all k ≤ max_k"""
    for k in range(max_k + 1):
        n_k = (p + 4*k + 3) // 4
        m_k = 4*k + 3
        if G(n_k, m_k) > 0:
            return False
    return True

def is_dangerous_QR(p, max_k=5):
    """Check if Type II (QR-trapped) fails at all k ≤ max_k"""
    for k in range(max_k + 1):
        n_k = (p + 4*k + 3) // 4
        m_k = 4*k + 3
        if not is_qr_trapped(n_k, m_k):
            return False
    return True

def analyze_prime_full(p, max_k=15):
    """Full analysis of a prime"""
    result = {
        'p': p,
        'first_type_i': None,
        'first_type_ii_G': None,
        'first_type_ii_QR': None,
        'type_i_witness': None,
    }

    for k in range(max_k + 1):
        n_k = (p + 4*k + 3) // 4
        m_k = 4*k + 3

        # Type II (G)
        if result['first_type_ii_G'] is None and G(n_k, m_k) > 0:
            result['first_type_ii_G'] = k

        # Type II (QR)
        if result['first_type_ii_QR'] is None and not is_qr_trapped(n_k, m_k):
            result['first_type_ii_QR'] = k

        # Type I
        if k >= 1 and result['first_type_i'] is None and type_i_succeeds(p, k):
            result['first_type_i'] = k
            result['type_i_witness'] = type_i_witness(p, k)

    return result

# Main analysis
print("\n" + "="*70)
print("SCANNING FOR DANGEROUS PRIMES")
print("="*70)

LIMIT = 800000
print(f"\nScanning primes p ≡ 1 (mod 4) up to {LIMIT}...")

dangerous_G = []
dangerous_QR = []
total_checked = 0

start_time = time.time()

for p in ALL_PRIMES:
    if p > LIMIT:
        break
    if p % 4 != 1:
        continue

    total_checked += 1

    if is_dangerous_G(p, max_k=5):
        dangerous_G.append(p)

    if is_dangerous_QR(p, max_k=5):
        dangerous_QR.append(p)

    if total_checked % 5000 == 0:
        print(f"  Checked {total_checked} primes, found {len(dangerous_G)} G-dangerous, {len(dangerous_QR)} QR-dangerous...")

elapsed = time.time() - start_time
print(f"\nCompleted in {elapsed:.1f} seconds")
print(f"Total primes checked: {total_checked}")
print(f"\nDangerous under G=0 criterion: {len(dangerous_G)}")
print(f"Dangerous under QR-trapped criterion: {len(dangerous_QR)}")

print(f"\nG-dangerous primes: {dangerous_G}")
print(f"\nQR-dangerous primes: {dangerous_QR}")

# Detailed analysis
print("\n" + "="*70)
print("DETAILED ANALYSIS OF G-DANGEROUS PRIMES")
print("="*70)

results = []
for p in dangerous_G:
    r = analyze_prime_full(p, max_k=15)
    results.append(r)
    print(f"\np = {p}:")
    print(f"  First Type I success: k={r['first_type_i']}, d={r['type_i_witness']}")
    print(f"  First Type II (G) success: k={r['first_type_ii_G']}")
    print(f"  First Type II (QR) success: k={r['first_type_ii_QR']}")

# Save to CSV
print("\n" + "="*70)
print("SAVING RESULTS")
print("="*70)

with open('/Users/kvallie2/Desktop/esc_stage8/dangerous_primes_G0_full.csv', 'w', newline='') as f:
    writer = csv.writer(f)
    writer.writerow(['p', 'first_type_i_k', 'first_type_ii_G_k', 'first_type_ii_QR_k', 'type_i_witness', 'rescue_method', 'rescue_k'])
    for r in results:
        # Determine rescue
        rescue_k = None
        rescue_method = None
        if r['first_type_i'] is not None:
            rescue_k = r['first_type_i']
            rescue_method = 'Type I'
        if r['first_type_ii_G'] is not None and (rescue_k is None or r['first_type_ii_G'] < rescue_k):
            rescue_k = r['first_type_ii_G']
            rescue_method = 'Type II (G)'
        writer.writerow([
            r['p'], r['first_type_i'], r['first_type_ii_G'], r['first_type_ii_QR'],
            r['type_i_witness'], rescue_method, rescue_k
        ])

print(f"Saved dangerous_primes_G0_full.csv")

# Summary statistics
print("\n" + "="*70)
print("SUMMARY")
print("="*70)
print(f"G-dangerous primes: {len(dangerous_G)}")
print(f"QR-dangerous primes: {len(dangerous_QR)}")
print(f"In both: {len(set(dangerous_G) & set(dangerous_QR))}")
print(f"G-only: {len(set(dangerous_G) - set(dangerous_QR))}")

# Check which primes need k > 5 for rescue
print("\n" + "="*70)
print("PRIMES NEEDING k > 5 FOR RESCUE")
print("="*70)
for r in results:
    rescue_k = min(filter(None, [r['first_type_i'], r['first_type_ii_G']]))
    if rescue_k > 5:
        print(f"p = {r['p']}: rescue at k = {rescue_k}")
