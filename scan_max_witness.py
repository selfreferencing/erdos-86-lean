#!/usr/bin/env python3
"""
Scan Mordell-hard primes for maximum witness d required.
Saves results incrementally.
"""

from math import gcd
import time
import sys

K_COMPLETE = [0, 1, 2, 3, 4, 5, 6, 7, 9, 11, 13, 14, 16, 17, 19, 21, 23, 25, 26, 29, 31, 39, 41]

def is_prime(n):
    if n < 2:
        return False
    if n == 2:
        return True
    if n % 2 == 0:
        return False
    if n < 9:
        return True
    if n % 3 == 0:
        return False
    r, d = 0, n - 1
    while d % 2 == 0:
        r += 1
        d //= 2
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

def factor(n):
    if n <= 1:
        return []
    factors = []
    d = 2
    while d * d <= n:
        if n % d == 0:
            e = 0
            while n % d == 0:
                e += 1
                n //= d
            factors.append((d, e))
        d += 1 if d == 2 else 2
    if n > 1:
        factors.append((n, 1))
    return factors

def divisors_of_square(n):
    facts = factor(n)
    divs = [1]
    for p, e in facts:
        new_divs = []
        for d in divs:
            power = 1
            for i in range(2*e + 1):
                new_divs.append(d * power)
                power *= p
        divs = new_divs
    return sorted(divs)

def find_min_witness(p):
    min_d = float('inf')
    best_k = None

    for k in K_COMPLETE:
        m_k = 4 * k + 3
        if (p + m_k) % 4 != 0:
            continue
        x_k = (p + m_k) // 4
        if gcd(x_k, m_k) > 1:
            continue
        target = (-x_k) % m_k
        divs = divisors_of_square(x_k)
        for d in divs:
            if d % m_k == target and d < min_d:
                min_d = d
                best_k = k
                break

    return (min_d, best_k) if min_d < float('inf') else (None, None)

def main():
    limit = int(sys.argv[1]) if len(sys.argv) > 1 else 10**7
    output_file = f"/Users/kvallie2/Desktop/esc_stage8/max_witness_scan_{limit}.txt"

    resistant = [1, 121, 169, 289, 361, 529]

    print(f'Scanning Mordell-hard primes up to {limit}...')
    print(f'Output: {output_file}')
    print('=' * 60)

    with open(output_file, 'w') as f:
        f.write(f"Max witness scan up to {limit}\n")
        f.write("=" * 60 + "\n\n")
        f.flush()

        start = time.time()

        large_d_primes = []
        max_d_seen = 0
        count = 0
        milestone = 20000

        for r in resistant:
            p = r
            while p < limit:
                if is_prime(p) and p % 4 == 1:
                    count += 1
                    if count % milestone == 0:
                        elapsed = time.time() - start
                        rate = count / elapsed
                        expected_total = 180000 * (limit / 10**8)
                        eta = (expected_total - count) / rate / 60
                        msg = f'Progress: {count} primes, {rate:.0f}/s, ETA ~{eta:.1f}min, max_d={max_d_seen}'
                        print(f'  {msg}')
                        f.write(f"{msg}\n")
                        f.flush()

                    min_d, k = find_min_witness(p)
                    if min_d is not None:
                        if min_d > max_d_seen:
                            max_d_seen = min_d
                            msg = f'New max: p={p}, d={min_d}, k={k}'
                            print(f'  {msg}')
                            f.write(f"{msg}\n")
                            f.flush()
                        if min_d > 1500:
                            large_d_primes.append((p, min_d, k))
                p += 840

        elapsed = time.time() - start

        f.write(f'\n{"=" * 60}\n')
        f.write(f'RESULTS\n')
        f.write(f'{"=" * 60}\n')
        f.write(f'Scanned {count} Mordell-hard primes in {elapsed:.1f}s\n')
        f.write(f'Maximum d required: {max_d_seen}\n')
        f.write(f'Primes requiring d > 1500: {len(large_d_primes)}\n')

        print(f'\nScanned {count} Mordell-hard primes in {elapsed:.1f}s')
        print(f'Maximum d required: {max_d_seen}')
        print(f'Primes requiring d > 1500: {len(large_d_primes)}')

        if large_d_primes:
            f.write('\nPrimes requiring d > 1500:\n')
            print('\nPrimes requiring d > 1500:')
            for p, d, k in sorted(large_d_primes, key=lambda x: -x[1]):
                line = f'  p = {p:>12}, d = {d:>5}, k = {k:>2}'
                f.write(line + '\n')
                print(line)

    print(f'\nResults saved to {output_file}')

if __name__ == "__main__":
    main()
