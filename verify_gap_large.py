#!/usr/bin/env python3
"""
Verify ESC for larger gap primes.
"""
import sys

def verify(n, x, y, z):
    return 4 * x * y * z == n * (y * z + x * z + x * y)

def find_esc_fast(n, verbose=False):
    """Fast ESC search."""
    # Strategy 1: x divides n
    for x in range(1, n + 1):
        if n % x == 0:
            num = 4 * x - n
            if num <= 0:
                continue
            denom = n * x
            for y in range(x, min(4 * n, x + 50000)):
                d = num * y - denom
                if d > 0 and (denom * y) % d == 0:
                    z = (denom * y) // d
                    if z >= y and verify(n, x, y, z):
                        return (x, y, z)

    # Strategy 2: Small x search
    for x in range(n // 4 + 1, min(n + 1, n // 4 + 10000)):
        num = 4 * x - n
        if num <= 0:
            continue
        for y in range(x, min(10 * n, x + 50000)):
            d = num * y - n * x
            if d > 0 and (n * x * y) % d == 0:
                z = (n * x * y) // d
                if z >= y and verify(n, x, y, z):
                    return (x, y, z)
        if verbose and x % 1000 == 0:
            print(f"  x={x}...", flush=True)

    return None

# Larger gap primes
large_gaps = [61129, 62497, 1982401]

print("=" * 60)
print("ESC VERIFICATION FOR LARGER GAP PRIMES")
print("=" * 60)
print(flush=True)

for p in large_gaps:
    print(f"p = {p}...", flush=True)
    sol = find_esc_fast(p, verbose=True)
    if sol:
        x, y, z = sol
        print(f"  ✓ 4/{p} = 1/{x} + 1/{y} + 1/{z}")
        assert verify(p, x, y, z)
    else:
        print(f"  ✗ NOT FOUND (within search bounds)")
    sys.stdout.flush()
