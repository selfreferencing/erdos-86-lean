#!/usr/bin/env python3
"""
ESC Criterion Analysis: G(n,m) = 0 vs QR-Trapping

This script analyzes the exact relationship between:
1. G(n, m) = 0: No coprime divisor pair sums to 0 mod m
2. QR-trapped: All prime factors of n are quadratic residues mod m

For the Erdős-Straus Conjecture with primes p ≡ 1 (mod 4).
"""

from math import gcd, isqrt
from collections import defaultdict
import csv
import time

# Precompute small primes for factorization
def sieve_primes(limit):
    """Sieve of Eratosthenes"""
    is_prime = [True] * (limit + 1)
    is_prime[0] = is_prime[1] = False
    for i in range(2, isqrt(limit) + 1):
        if is_prime[i]:
            for j in range(i*i, limit + 1, i):
                is_prime[j] = False
    return [i for i in range(2, limit + 1) if is_prime[i]]

SMALL_PRIMES = sieve_primes(100000)

def is_prime(n):
    """Check if n is prime"""
    if n < 2:
        return False
    if n < len(SMALL_PRIMES) and n <= SMALL_PRIMES[-1]:
        # Binary search
        lo, hi = 0, len(SMALL_PRIMES)
        while lo < hi:
            mid = (lo + hi) // 2
            if SMALL_PRIMES[mid] < n:
                lo = mid + 1
            else:
                hi = mid
        return lo < len(SMALL_PRIMES) and SMALL_PRIMES[lo] == n
    if n % 2 == 0:
        return False
    for p in SMALL_PRIMES:
        if p * p > n:
            return True
        if n % p == 0:
            return False
    # Miller-Rabin for larger numbers
    return miller_rabin(n)

def miller_rabin(n, witnesses=[2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37]):
    """Miller-Rabin primality test"""
    if n < 2:
        return False
    if n in witnesses:
        return True
    if n % 2 == 0:
        return False

    r, d = 0, n - 1
    while d % 2 == 0:
        r += 1
        d //= 2

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

def factorize(n):
    """Return list of prime factors (with multiplicity)"""
    if n <= 1:
        return []
    factors = []
    for p in SMALL_PRIMES:
        if p * p > n:
            break
        while n % p == 0:
            factors.append(p)
            n //= p
    if n > 1:
        factors.append(n)
    return factors

def prime_factors(n):
    """Return set of distinct prime factors"""
    return set(factorize(n))

def divisors(n):
    """Return all divisors of n"""
    if n <= 0:
        return []
    divs = [1]
    for p in prime_factors(n):
        pk = 1
        new_divs = []
        while n % p == 0:
            pk *= p
            n //= p
            new_divs.extend([d * pk for d in divs])
        divs.extend(new_divs)
    # Recompute properly
    result = set([1])
    temp_n = n
    factors = factorize(temp_n) if temp_n > 1 else []
    # Actually let's do this correctly
    return _divisors_from_factorization(factorize(n * 1))  # hack to get original n

def _divisors_from_factorization(factors):
    """Get divisors from factorization"""
    if not factors:
        return [1]
    from collections import Counter
    factor_counts = Counter(factors)
    divs = [1]
    for p, e in factor_counts.items():
        new_divs = []
        for d in divs:
            pk = 1
            for _ in range(e + 1):
                new_divs.append(d * pk)
                pk *= p
        divs = new_divs
    return sorted(divs)

def get_divisors(n):
    """Get all divisors of n"""
    if n <= 0:
        return []
    factors = factorize(n)
    if not factors:
        return [1]
    from collections import Counter
    factor_counts = Counter(factors)
    divs = [1]
    for p, e in factor_counts.items():
        new_divs = []
        for d in divs:
            pk = 1
            for _ in range(e + 1):
                new_divs.append(d * pk)
                pk *= p
        divs = new_divs
    return sorted(set(divs))

def G(n, m):
    """
    Count unordered coprime divisor pairs (a, b) of n with a + b ≡ 0 (mod m).
    """
    divs = get_divisors(n)
    count = 0
    for i, a in enumerate(divs):
        for b in divs[i+1:]:
            if gcd(a, b) == 1 and (a + b) % m == 0:
                count += 1
    return count

def legendre_symbol(a, p):
    """Compute Legendre symbol (a/p) for odd prime p"""
    if p == 2:
        return 1 if a % 2 == 1 else 0
    a = a % p
    if a == 0:
        return 0
    return pow(a, (p - 1) // 2, p) if pow(a, (p - 1) // 2, p) == 1 else -1

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

# QR subgroups for each m_k
QR_SUBGROUPS = {
    3: {1},
    7: {1, 2, 4},
    11: {1, 3, 4, 5, 9},
    15: {1, 2, 4, 8},  # Jacobi kernel
    19: {1, 4, 5, 6, 7, 9, 11, 16, 17},
    23: {1, 2, 3, 4, 6, 8, 9, 12, 13, 16, 18},
    27: {1, 2, 4, 5, 7, 8, 10, 11, 13, 14, 16, 17, 19, 20, 22, 23, 25, 26},  # Jacobi +1
    31: {1, 2, 4, 5, 7, 8, 9, 10, 14, 16, 18, 19, 20, 25, 28},
    35: {1, 2, 4, 8, 9, 11, 16, 18, 22, 23, 29, 32},  # Jacobi +1
    39: {1, 4, 10, 14, 16, 22, 25, 35, 38},  # Need to verify
}

def get_qr_subgroup(m):
    """Get QR subgroup for modulus m"""
    if m in QR_SUBGROUPS:
        return QR_SUBGROUPS[m]
    # Compute for prime m
    if is_prime(m):
        return {x for x in range(1, m) if legendre_symbol(x, m) == 1}
    # For composite m, use Jacobi symbol
    return {x for x in range(1, m) if gcd(x, m) == 1 and jacobi_symbol(x, m) == 1}

def is_qr_trapped(n, m):
    """
    Check if n is QR-trapped mod m:
    All prime factors of n are in the QR subgroup mod m.
    """
    qr_set = get_qr_subgroup(m)
    for p in prime_factors(n):
        if p % m not in qr_set and p != m:  # p = m means p divides m, handle separately
            return False
    return True

def type_ii_fails_G(n, m):
    """Type II fails iff G(n, m) = 0"""
    return G(n, m) == 0

def type_ii_fails_QR(n, m):
    """Type II fails iff n is QR-trapped"""
    return is_qr_trapped(n, m)

def type_i_succeeds(p, k):
    """Check if Type I succeeds at k: kp+1 has divisor d ≡ -p (mod 4k)"""
    if k == 0:
        return False  # k=0 is Type II only
    N = k * p + 1
    target = (-p) % (4 * k)
    for d in get_divisors(N):
        if d % (4 * k) == target:
            return True
    return False

def type_i_witness(p, k):
    """Find a Type I witness divisor, or None"""
    if k == 0:
        return None
    N = k * p + 1
    target = (-p) % (4 * k)
    for d in get_divisors(N):
        if d % (4 * k) == target:
            return d
    return None

def analyze_prime(p, max_k=10):
    """
    Analyze a prime p ≡ 1 (mod 4).
    Returns dict with analysis results.
    """
    results = {
        'p': p,
        'type_ii_G_fails': [],      # k values where G(n_k, m_k) = 0
        'type_ii_QR_fails': [],     # k values where n_k is QR-trapped
        'type_i_fails': [],         # k values where Type I fails
        'first_type_i_success': None,
        'first_type_ii_G_success': None,
        'first_type_ii_QR_success': None,
        'type_i_witness': None,
        'criterion_differs': [],    # k values where G=0 differs from QR-trapped
    }

    for k in range(max_k + 1):
        n_k = (p + 4*k + 3) // 4
        m_k = 4*k + 3

        g_zero = type_ii_fails_G(n_k, m_k)
        qr_trap = type_ii_fails_QR(n_k, m_k)

        if g_zero:
            results['type_ii_G_fails'].append(k)
        else:
            if results['first_type_ii_G_success'] is None:
                results['first_type_ii_G_success'] = k

        if qr_trap:
            results['type_ii_QR_fails'].append(k)
        else:
            if results['first_type_ii_QR_success'] is None:
                results['first_type_ii_QR_success'] = k

        if g_zero != qr_trap:
            results['criterion_differs'].append({
                'k': k,
                'n_k': n_k,
                'm_k': m_k,
                'G_zero': g_zero,
                'QR_trapped': qr_trap,
                'is_prime': is_prime(n_k),
                'factors': list(prime_factors(n_k))
            })

        if k >= 1:
            if not type_i_succeeds(p, k):
                results['type_i_fails'].append(k)
            else:
                if results['first_type_i_success'] is None:
                    results['first_type_i_success'] = k
                    results['type_i_witness'] = type_i_witness(p, k)

    return results

def find_dangerous_primes(limit, criterion='G', max_k=5):
    """
    Find primes where Type II fails at all k ≤ max_k.
    criterion: 'G' for G(n,m)=0, 'QR' for QR-trapped
    """
    dangerous = []

    for p in SMALL_PRIMES:
        if p > limit:
            break
        if p % 4 != 1:
            continue

        all_fail = True
        for k in range(max_k + 1):
            n_k = (p + 4*k + 3) // 4
            m_k = 4*k + 3

            if criterion == 'G':
                if G(n_k, m_k) > 0:
                    all_fail = False
                    break
            else:  # QR
                if not is_qr_trapped(n_k, m_k):
                    all_fail = False
                    break

        if all_fail:
            dangerous.append(p)

    return dangerous

def main():
    print("=" * 70)
    print("ESC CRITERION ANALYSIS")
    print("=" * 70)

    # First, let's verify the QR subgroups are correct
    print("\n1. Verifying QR subgroups...")
    for m in [3, 7, 11, 19, 23, 31]:
        computed = {x for x in range(1, m) if legendre_symbol(x, m) == 1}
        stored = get_qr_subgroup(m)
        if computed == stored:
            print(f"   m={m}: OK (size {len(stored)})")
        else:
            print(f"   m={m}: MISMATCH!")
            print(f"      Computed: {computed}")
            print(f"      Stored: {stored}")

    # Check Jacobi for m=15
    m = 15
    computed = {x for x in range(1, m) if gcd(x, m) == 1 and jacobi_symbol(x, m) == 1}
    print(f"   m=15 (Jacobi +1): {computed}")

    # 2. Find where G=0 differs from QR-trapped
    print("\n2. Finding criterion differences (G=0 vs QR-trapped)...")
    print("   Scanning primes p ≡ 1 (mod 4) up to 200,000...")

    differences = []
    primes_checked = 0

    for p in SMALL_PRIMES:
        if p > 200000:
            break
        if p % 4 != 1:
            continue
        primes_checked += 1

        for k in range(6):
            n_k = (p + 4*k + 3) // 4
            m_k = 4*k + 3

            g_zero = (G(n_k, m_k) == 0)
            qr_trap = is_qr_trapped(n_k, m_k)

            if g_zero != qr_trap:
                differences.append({
                    'p': p,
                    'k': k,
                    'n_k': n_k,
                    'm_k': m_k,
                    'G_zero': g_zero,
                    'QR_trapped': qr_trap,
                    'n_k_prime': is_prime(n_k),
                    'n_k_factors': list(prime_factors(n_k)),
                    'n_k_mod_m': n_k % m_k
                })

    print(f"   Checked {primes_checked} primes")
    print(f"   Found {len(differences)} cases where criteria differ")

    if differences:
        print("\n   First 20 differences:")
        for i, d in enumerate(differences[:20]):
            print(f"   p={d['p']}, k={d['k']}: n_k={d['n_k']} (mod {d['m_k']})")
            print(f"      G=0: {d['G_zero']}, QR-trapped: {d['QR_trapped']}")
            print(f"      n_k prime: {d['n_k_prime']}, factors: {d['n_k_factors']}")
            print(f"      n_k mod m_k = {d['n_k_mod_m']}")

    # 3. Analyze the pattern of differences
    print("\n3. Analyzing difference pattern...")
    g_but_not_qr = [d for d in differences if d['G_zero'] and not d['QR_trapped']]
    qr_but_not_g = [d for d in differences if d['QR_trapped'] and not d['G_zero']]

    print(f"   G=0 but NOT QR-trapped: {len(g_but_not_qr)} cases")
    print(f"   QR-trapped but NOT G=0: {len(qr_but_not_g)} cases")

    if g_but_not_qr:
        print("\n   Cases where G=0 but NOT QR-trapped (first 10):")
        for d in g_but_not_qr[:10]:
            print(f"      p={d['p']}, k={d['k']}, n_k={d['n_k']}, m_k={d['m_k']}")
            print(f"         n_k prime: {d['n_k_prime']}, n_k mod m_k = {d['n_k_mod_m']}")
            if d['n_k_prime']:
                print(f"         (prime n_k has G=0 iff n_k ≢ -1 mod m_k)")
                print(f"         -1 mod {d['m_k']} = {(-1) % d['m_k']}, n_k mod m_k = {d['n_k_mod_m']}")

    # 4. Find dangerous primes under both criteria
    print("\n4. Finding dangerous primes (Type II fails at all k ≤ 5)...")

    print("   Under G=0 criterion (up to 800,000)...")
    start = time.time()
    dangerous_G = find_dangerous_primes(800000, criterion='G', max_k=5)
    print(f"   Found {len(dangerous_G)} dangerous primes in {time.time()-start:.1f}s")
    print(f"   First 20: {dangerous_G[:20]}")

    print("\n   Under QR-trapped criterion (up to 800,000)...")
    start = time.time()
    dangerous_QR = find_dangerous_primes(800000, criterion='QR', max_k=5)
    print(f"   Found {len(dangerous_QR)} dangerous primes in {time.time()-start:.1f}s")
    print(f"   First 20: {dangerous_QR[:20]}")

    # 5. Compare the lists
    print("\n5. Comparing dangerous prime lists...")
    in_G_not_QR = set(dangerous_G) - set(dangerous_QR)
    in_QR_not_G = set(dangerous_QR) - set(dangerous_G)
    in_both = set(dangerous_G) & set(dangerous_QR)

    print(f"   In G-dangerous but not QR-dangerous: {len(in_G_not_QR)}")
    print(f"   In QR-dangerous but not G-dangerous: {len(in_QR_not_G)}")
    print(f"   In both: {len(in_both)}")

    if in_G_not_QR:
        print(f"\n   Primes in G-dangerous but not QR-dangerous (first 10):")
        for p in sorted(in_G_not_QR)[:10]:
            print(f"      p = {p}")

    # 6. Detailed analysis of first few dangerous primes
    print("\n6. Detailed analysis of dangerous primes...")
    test_primes = dangerous_G[:10] if dangerous_G else [21169, 61681, 66529]

    for p in test_primes:
        print(f"\n   p = {p}:")
        result = analyze_prime(p, max_k=10)
        print(f"      Type II G-fails at k: {result['type_ii_G_fails']}")
        print(f"      Type II QR-fails at k: {result['type_ii_QR_fails']}")
        print(f"      Type I fails at k: {result['type_i_fails'][:6]}...")
        print(f"      First Type I success: k={result['first_type_i_success']}, d={result['type_i_witness']}")
        print(f"      First Type II (G) success: k={result['first_type_ii_G_success']}")
        print(f"      First Type II (QR) success: k={result['first_type_ii_QR_success']}")
        if result['criterion_differs']:
            print(f"      Criteria differ at: {[d['k'] for d in result['criterion_differs']]}")

    # 7. Save results to CSV
    print("\n7. Saving results...")

    # Save dangerous primes under G criterion
    with open('/Users/kvallie2/Desktop/esc_stage8/dangerous_primes_G0.csv', 'w', newline='') as f:
        writer = csv.writer(f)
        writer.writerow(['p', 'first_type_i_k', 'first_type_ii_k', 'type_i_witness'])
        for p in dangerous_G:
            result = analyze_prime(p, max_k=15)
            writer.writerow([
                p,
                result['first_type_i_success'],
                result['first_type_ii_G_success'],
                result['type_i_witness']
            ])
    print(f"   Saved dangerous_primes_G0.csv ({len(dangerous_G)} primes)")

    # Save dangerous primes under QR criterion
    with open('/Users/kvallie2/Desktop/esc_stage8/dangerous_primes_QR.csv', 'w', newline='') as f:
        writer = csv.writer(f)
        writer.writerow(['p', 'first_type_i_k', 'first_type_ii_k', 'type_i_witness'])
        for p in dangerous_QR:
            result = analyze_prime(p, max_k=15)
            writer.writerow([
                p,
                result['first_type_i_success'],
                result['first_type_ii_QR_success'],
                result['type_i_witness']
            ])
    print(f"   Saved dangerous_primes_QR.csv ({len(dangerous_QR)} primes)")

    print("\n" + "=" * 70)
    print("ANALYSIS COMPLETE")
    print("=" * 70)

if __name__ == "__main__":
    main()
