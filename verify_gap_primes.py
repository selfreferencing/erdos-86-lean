#!/usr/bin/env python3
"""
Verify that gap primes (where Lemma 7B fails) still have ESC solutions.

ESC: 4/n = 1/x + 1/y + 1/z for positive integers x, y, z
Equivalent: 4xyz = n(yz + xz + xy)
"""

from math import isqrt, gcd

def find_esc_solution(n, max_x=None):
    """
    Find an ESC solution for n: 4/n = 1/x + 1/y + 1/z

    Returns (x, y, z) or None if not found within search bounds.
    """
    if max_x is None:
        max_x = 10 * n  # Usually sufficient

    # x <= y <= z, and x > n/4 (since 1/x < 4/n means x > n/4)
    # Also x <= 3n/4 (since if x > 3n/4, then 1/x < 4/(3n), leaving < 4/n - 4/(3n) = 8/(3n) for 1/y + 1/z)

    x_min = n // 4 + 1
    x_max = min(max_x, 3 * n // 4 + 1)

    for x in range(x_min, x_max + 1):
        # 4/n - 1/x = (4x - n) / (nx)
        # Need (4x - n) / (nx) = 1/y + 1/z = (y + z) / (yz)
        # So (4x - n) * yz = nx(y + z)

        num = 4 * x - n
        if num <= 0:
            continue

        # For fixed x, we need 1/y + 1/z = num/(n*x)
        # This means yz(num) = nx(y + z)
        # Rearranging: y*z*num - nx*y - nx*z = 0
        # y(z*num - nx) = nx*z
        # y = nx*z / (z*num - nx)

        # For y to be positive integer, need z*num > nx and (z*num - nx) | nx*z

        # z >= y >= x, and we need z*num > nx, so z > nx/num
        z_min = max(x, n * x // num + 1)

        # Upper bound: when y = x, we get smallest z
        # Also z <= nx/num + nx (rough bound)
        z_max = n * x // num + n * x + 1
        z_max = min(z_max, 100 * n)  # Safety cap

        for z in range(z_min, z_max + 1):
            denom = z * num - n * x
            if denom <= 0:
                continue
            if (n * x * z) % denom == 0:
                y = (n * x * z) // denom
                if y >= x and y <= z:
                    # Verify
                    if 4 * x * y * z == n * (y * z + x * z + x * y):
                        return (x, y, z)

    return None


def verify_solution(n, x, y, z):
    """Verify that 4/n = 1/x + 1/y + 1/z"""
    # Check: 4xyz = n(yz + xz + xy)
    lhs = 4 * x * y * z
    rhs = n * (y * z + x * z + x * y)
    return lhs == rhs


def analyze_solution(n, x, y, z):
    """Analyze the type of solution found."""
    # Check if it's a "Type I" style (one denominator divides n)
    type_info = []
    if n % x == 0:
        type_info.append(f"x={x} divides n")
    if n % y == 0:
        type_info.append(f"y={y} divides n")
    if n % z == 0:
        type_info.append(f"z={z} divides n")

    # Check witness size relative to sqrt(n)
    sqrt_n = isqrt(n)

    return {
        'x': x, 'y': y, 'z': z,
        'x/sqrt(n)': x / sqrt_n,
        'y/sqrt(n)': y / sqrt_n,
        'z/sqrt(n)': z / sqrt_n,
        'type_info': type_info if type_info else ['No simple divisibility']
    }


# Gap primes identified from prompt responses
gap_primes = [97, 113, 229, 233, 1201, 61129, 62497, 1982401]

print("=" * 70)
print("VERIFYING ESC SOLUTIONS FOR GAP PRIMES")
print("=" * 70)
print()

results = []

for p in gap_primes:
    print(f"Checking p = {p}...")
    solution = find_esc_solution(p)

    if solution:
        x, y, z = solution
        verified = verify_solution(p, x, y, z)
        analysis = analyze_solution(p, x, y, z)

        print(f"  ✓ FOUND: 4/{p} = 1/{x} + 1/{y} + 1/{z}")
        print(f"    Verified: {verified}")
        print(f"    x/√p = {analysis['x/sqrt(n)']:.3f}")
        print(f"    Type: {analysis['type_info']}")
        results.append((p, solution, True))
    else:
        print(f"  ✗ NO SOLUTION FOUND within search bounds")
        results.append((p, None, False))
    print()

print("=" * 70)
print("SUMMARY")
print("=" * 70)

found = sum(1 for _, _, success in results if success)
print(f"Solutions found: {found}/{len(gap_primes)}")
print()

for p, sol, success in results:
    if success:
        x, y, z = sol
        print(f"p = {p:>8}: 4/{p} = 1/{x} + 1/{y} + 1/{z}")
    else:
        print(f"p = {p:>8}: NO SOLUTION FOUND")
