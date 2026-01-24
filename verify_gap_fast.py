#!/usr/bin/env python3
"""
Fast verification of ESC for gap primes using known parametric families.
"""
import sys

def verify(n, x, y, z):
    """Check 4xyz = n(yz + xz + xy)"""
    return 4 * x * y * z == n * (y * z + x * z + x * y)

def find_esc_fast(n):
    """
    Fast ESC search using multiple strategies.
    """
    # Strategy 1: Type I - one of x, y, z divides n
    # If x divides n, then 4/n - 1/x = (4x-n)/(nx) must equal 1/y + 1/z
    for x in range(1, n + 1):
        if n % x == 0:
            # 4/n = 1/x + 1/y + 1/z where x | n
            # Remaining: (4x - n)/(nx) = 1/y + 1/z
            num = 4 * x - n
            if num <= 0:
                continue
            denom = n * x
            # 1/y + 1/z = num/denom
            # y*z = denom*(y+z)/num
            # For each y, check if z is integer
            for y in range(x, 4 * n):
                # z = denom*y / (num*y - denom) when this is positive integer
                d = num * y - denom
                if d > 0 and (denom * y) % d == 0:
                    z = (denom * y) // d
                    if z >= y and verify(n, x, y, z):
                        return (x, y, z)

    # Strategy 2: Bradford Type II - systematic small x search
    for x in range(n // 4 + 1, n + 1):
        num = 4 * x - n
        if num <= 0:
            continue
        for y in range(x, min(10 * n, x + 10000)):
            d = num * y - n * x
            if d > 0 and (n * x * y) % d == 0:
                z = (n * x * y) // d
                if z >= y and verify(n, x, y, z):
                    return (x, y, z)

    return None

# Small gap primes first
gap_primes = [97, 113, 229, 233, 1201]

print("=" * 60)
print("FAST ESC VERIFICATION FOR SMALL GAP PRIMES")
print("=" * 60)
print(flush=True)

for p in gap_primes:
    print(f"p = {p}...", end=" ", flush=True)
    sol = find_esc_fast(p)
    if sol:
        x, y, z = sol
        print(f"✓ 4/{p} = 1/{x} + 1/{y} + 1/{z}")
        # Double-check
        lhs = 4 * x * y * z
        rhs = p * (y*z + x*z + x*y)
        assert lhs == rhs, "Verification failed!"
    else:
        print("✗ NOT FOUND")
    sys.stdout.flush()

print()
print("All small gap primes verified!" if all(find_esc_fast(p) for p in gap_primes) else "Some gaps remain")
