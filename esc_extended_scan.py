#!/usr/bin/env python3
"""
ESC Extended Scan - Check max rescue k for larger primes
"""

from math import gcd, isqrt
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

print("Generating primes...")
LIMIT = 2000000  # 2 million - can increase if needed
ALL_PRIMES = sieve_primes(LIMIT + 100000)
PRIME_SET = set(ALL_PRIMES)
print(f"Generated {len(ALL_PRIMES)} primes")

def is_prime(n):
    if n <= 1:
        return False
    if n in PRIME_SET:
        return True
    if n <= ALL_PRIMES[-1]:
        return False
    if n % 2 == 0:
        return False
    for p in ALL_PRIMES:
        if p * p > n:
            return True
        if n % p == 0:
            return False
    return True

def get_divisors(n):
    """Get all divisors of n"""
    if n <= 0:
        return []
    divs = [1]
    temp = n
    factors = []
    for p in ALL_PRIMES:
        if p * p > temp:
            break
        if temp % p == 0:
            exp = 0
            while temp % p == 0:
                exp += 1
                temp //= p
            factors.append((p, exp))
    if temp > 1:
        factors.append((temp, 1))
    
    for p, e in factors:
        new_divs = []
        pk = 1
        for _ in range(e + 1):
            new_divs.extend([d * pk for d in divs])
            pk *= p
        divs = new_divs
    return divs

def G(n, m):
    """Count coprime divisor pairs with sum ≡ 0 (mod m)"""
    divs = get_divisors(n)
    count = 0
    for i, a in enumerate(divs):
        for b in divs[i+1:]:
            if gcd(a, b) == 1 and (a + b) % m == 0:
                count += 1
    return count

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

def find_rescue_k(p, max_k=20):
    """Find first k where Type I or Type II succeeds"""
    for k in range(max_k + 1):
        n_k = (p + 4*k + 3) // 4
        m_k = 4*k + 3
        
        # Type II check
        if G(n_k, m_k) > 0:
            return k, 'Type II'
        
        # Type I check (k >= 1)
        if k >= 1 and type_i_succeeds(p, k):
            return k, 'Type I'
    
    return None, None

def is_dangerous(p, max_k=5):
    """Check if Type II (G=0) fails at all k ≤ max_k"""
    for k in range(max_k + 1):
        n_k = (p + 4*k + 3) // 4
        m_k = 4*k + 3
        if G(n_k, m_k) > 0:
            return False
    return True

# Main scan
print(f"\nScanning primes p ≡ 1 (mod 4) from 800,001 to {LIMIT}...")
print("Looking for primes requiring k > 12 for rescue...\n")

start_time = time.time()
max_k_found = 12
max_k_prime = 532249
dangerous_count = 0
total_checked = 0
high_k_primes = []

for p in ALL_PRIMES:
    if p <= 800000:
        continue
    if p > LIMIT:
        break
    if p % 4 != 1:
        continue
    
    total_checked += 1
    
    # Quick check: is it dangerous at k ≤ 5?
    if is_dangerous(p, max_k=5):
        dangerous_count += 1
        
        # Find actual rescue k
        rescue_k, method = find_rescue_k(p, max_k=20)
        
        if rescue_k is not None and rescue_k > max_k_found:
            max_k_found = rescue_k
            max_k_prime = p
            print(f"NEW MAX K! p = {p}, rescue k = {rescue_k}, method = {method}")
            high_k_primes.append((p, rescue_k, method))
        elif rescue_k is not None and rescue_k > 10:
            high_k_primes.append((p, rescue_k, method))
        elif rescue_k is None:
            print(f"WARNING: No rescue found for p = {p} up to k = 20!")
    
    if total_checked % 10000 == 0:
        elapsed = time.time() - start_time
        print(f"  Checked {total_checked} primes, {dangerous_count} dangerous, max k = {max_k_found}, time = {elapsed:.1f}s")

elapsed = time.time() - start_time
print(f"\n{'='*60}")
print(f"RESULTS")
print(f"{'='*60}")
print(f"Primes checked (800K to {LIMIT}): {total_checked}")
print(f"Dangerous primes found: {dangerous_count}")
print(f"Maximum rescue k: {max_k_found} (for p = {max_k_prime})")
print(f"Time: {elapsed:.1f} seconds")

if high_k_primes:
    print(f"\nPrimes requiring k > 10:")
    for p, k, method in sorted(high_k_primes, key=lambda x: -x[1])[:20]:
        print(f"  p = {p}, k = {k}, {method}")
