#!/usr/bin/env python3
"""
Attack on the 86 Conjecture
Analyzing 5-adic orbit structure to find proof patterns.
"""

import sys
sys.set_int_max_str_digits(100000)

def u_k(n, k):
    """5-adic orbit value: u_k(n) = 2^(n-k) mod 5^k"""
    if n < k:
        return None
    return pow(2, n - k, 5**k)

def zero_threshold(k):
    """Threshold below which digit k-1 is zero: 5^(k-1)/2"""
    return 5**(k-1) // 2

def digit_k(n, k):
    """Extract k-th digit (from right, 0-indexed) of 2^n"""
    if k == 0:
        return pow(2, n, 10) % 10
    val = pow(2, n, 10**(k+1))
    return (val // 10**k) % 10

def survival_depth(n, max_k=500):
    """How many trailing digits of 2^n are zeroless?"""
    for k in range(1, max_k + 1):
        if digit_k(n, k-1) == 0:
            return k - 1
    return max_k

def analyze_orbit(n, depth):
    """Analyze the 5-adic orbit for n up to given depth."""
    print(f"\n{'='*60}")
    print(f"5-ADIC ORBIT ANALYSIS: n = {n}")
    print(f"{'='*60}")

    results = []
    for k in range(1, depth + 1):
        u = u_k(n, k)
        thresh = zero_threshold(k)
        in_zero_interval = u < thresh
        digit = digit_k(n, k-1)

        status = "ZERO!" if in_zero_interval else "safe"
        results.append((k, u, thresh, in_zero_interval, digit))

        if k <= 10 or in_zero_interval:
            print(f"k={k:2d}: u_k = {u:15d}, thresh = {thresh:15d}, "
                  f"{'IN ZERO INTERVAL' if in_zero_interval else 'safe':20s} d_{k-1} = {digit}")

        if in_zero_interval:
            print(f"  => First zero at position {k-1} (0-indexed)")
            break

    return results

def analyze_near_misses():
    """Why do n=87,...,128 all fail before n=129 succeeds?"""
    print("\n" + "="*70)
    print("NEAR MISS ANALYSIS: Why n=87-128 fail before level 27")
    print("="*70)

    print(f"\n{'n':<6} {'depth':<8} {'fail_k':<8} {'u_k at fail':<20} {'threshold':<20}")
    print("-"*70)

    for n in range(87, 135):
        depth = survival_depth(n)
        if depth < 50:
            fail_k = depth + 1
            u = u_k(n, fail_k)
            thresh = zero_threshold(fail_k)
            print(f"{n:<6} {depth:<8} {fail_k:<8} {u:<20} {thresh:<20}")

def compute_survivor_sets(max_k=10):
    """Compute survivor residue classes for each level."""
    print("\n" + "="*70)
    print("SURVIVOR SET STRUCTURE")
    print("="*70)

    for k in range(1, max_k + 1):
        period = 4 * 5**(k-1)
        survivors = []

        for r in range(period):
            # Check if residue class r survives to level k
            # Need to check a representative with enough digits
            n = r if r >= k else r + period

            # Check if last k digits are zeroless
            power = pow(2, n, 10**k)
            zeroless = True
            temp = power
            for _ in range(k):
                if temp % 10 == 0:
                    zeroless = False
                    break
                temp //= 10

            if zeroless:
                survivors.append(r)

        density = len(survivors) / period
        print(f"k={k:2d}: period={period:10d}, survivors={len(survivors):8d}, "
              f"density={density:.6f}, expected={(0.9)**(k-1):.6f}")

def find_pattern_in_survivors():
    """Look for patterns in survivor structure."""
    print("\n" + "="*70)
    print("SURVIVOR PATTERN ANALYSIS")
    print("="*70)

    # For small k, list all survivors
    for k in range(1, 6):
        period = 4 * 5**(k-1)
        survivors = []

        for r in range(period):
            n = r if r >= k else r + period
            power = pow(2, n, 10**k)
            zeroless = True
            temp = power
            for _ in range(k):
                if temp % 10 == 0:
                    zeroless = False
                    break
                temp //= 10

            if zeroless:
                survivors.append(r)

        print(f"\nk={k}, period={period}:")
        print(f"  Survivors mod {period}: {survivors[:30]}{'...' if len(survivors) > 30 else ''}")

        # Analyze residues mod 4, mod 5
        mod4 = [r % 4 for r in survivors]
        mod5 = [r % 5 for r in survivors if k > 1]

        from collections import Counter
        print(f"  Distribution mod 4: {dict(Counter(mod4))}")
        if mod5:
            print(f"  Distribution mod 5: {dict(Counter(mod5))}")

def analyze_129_specialness():
    """Why is 129 special? Analyze its 5-adic properties."""
    print("\n" + "="*70)
    print("WHY IS 129 SPECIAL?")
    print("="*70)

    n = 129
    print(f"\n129 in various representations:")
    print(f"  Decimal: {n}")
    print(f"  Binary: {bin(n)}")
    print(f"  Base 5: ", end="")

    # Convert to base 5
    temp = n
    base5 = []
    while temp:
        base5.append(temp % 5)
        temp //= 5
    print(''.join(map(str, reversed(base5))))

    print(f"\n129 mod various periods:")
    for k in range(1, 10):
        period = 4 * 5**(k-1)
        print(f"  129 mod {period} = {129 % period}")

    print(f"\n5-adic valuation: v_5(129 - r) for small r:")
    for r in range(10):
        diff = abs(129 - r)
        v5 = 0
        temp = diff
        while temp % 5 == 0 and temp > 0:
            v5 += 1
            temp //= 5
        print(f"  v_5(129 - {r}) = {v5}")

if __name__ == "__main__":
    # Phase 1: Analyze specific orbits
    analyze_orbit(86, 30)  # Last zeroless
    analyze_orbit(87, 30)  # First with zero
    analyze_orbit(129, 40) # Tightest case

    # Phase 2: Near miss analysis
    analyze_near_misses()

    # Phase 3: Survivor structure
    compute_survivor_sets(8)

    # Phase 4: Pattern search
    find_pattern_in_survivors()

    # Phase 5: Why 129?
    analyze_129_specialness()
