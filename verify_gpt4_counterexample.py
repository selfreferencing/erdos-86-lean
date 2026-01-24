#!/usr/bin/env python3
"""
Verify GPT4's counterexample showing that "large prime factor to first power"
does NOT guarantee a Type II witness exists.

Counterexample:
  p = 3889 (prime, p ≡ 1 mod 4)
  k = 29, m = 119
  x = (p + m)/4 = 1002 = 2 × 3 × 167
  q = 167 > 29 with v_q(x) = 1

Claim: No divisor d | x² satisfies d ≡ -x (mod 119)
"""

from math import gcd

def factor(n):
    """Return list of (prime, exponent) pairs."""
    factors = []
    d = 2
    temp = n
    while d * d <= temp:
        if temp % d == 0:
            e = 0
            while temp % d == 0:
                e += 1
                temp //= d
            factors.append((d, e))
        d += 1
    if temp > 1:
        factors.append((temp, 1))
    return factors

def divisors_of_square(n):
    """Return all divisors of n²."""
    facts = factor(n)
    divs = [1]
    for p, e in facts:
        new_divs = []
        for d in divs:
            power = 1
            for i in range(2*e + 1):  # 0 to 2e
                new_divs.append(d * power)
                power *= p
        divs = new_divs
    return sorted(divs)

def is_prime(n):
    if n < 2:
        return False
    if n == 2:
        return True
    if n % 2 == 0:
        return False
    for i in range(3, int(n**0.5) + 1, 2):
        if n % i == 0:
            return False
    return True

def verify_counterexample():
    print("=" * 70)
    print("VERIFYING GPT4's COUNTEREXAMPLE")
    print("=" * 70)

    p = 3889
    k = 29
    m = 4 * k + 3  # = 119

    print(f"\np = {p}")
    print(f"Is p prime? {is_prime(p)}")
    print(f"p mod 4 = {p % 4}")

    print(f"\nk = {k}")
    print(f"m_k = 4k + 3 = {m}")

    x = (p + m) // 4
    print(f"\nx = (p + m)/4 = {x}")
    print(f"Factorization of x: {factor(x)}")

    # Verify x = 2 × 3 × 167
    assert x == 2 * 3 * 167, f"Expected 1002, got {x}"
    print(f"x = 2 × 3 × 167 ✓")

    # Large prime factor
    q = 167
    print(f"\nLarge prime q = {q} > 29, v_q(x) = 1 ✓")

    # Target residue
    target = (-x) % m
    print(f"\nTarget: -x mod m = {target}")

    # Get all divisors of x²
    divs = divisors_of_square(x)
    print(f"\nDivisors of x² = {x**2}: {len(divs)} divisors")

    # Check each divisor
    witnesses = []
    for d in divs:
        if d % m == target:
            witnesses.append(d)

    print(f"\nDivisors d | x² with d ≡ {target} (mod {m}):")
    if witnesses:
        for d in witnesses:
            print(f"  d = {d} ≡ {d % m} (mod {m})")
        print(f"\nCOUNTEREXAMPLE FAILS: Found {len(witnesses)} witnesses!")
    else:
        print(f"  NONE FOUND!")
        print(f"\n✓ COUNTEREXAMPLE VERIFIED: No witness exists despite large prime factor")

    # Show all divisor residues
    print(f"\nAll divisor residues mod {m}:")
    residues = sorted(set(d % m for d in divs))
    print(f"  {residues}")
    print(f"  Count: {len(residues)} distinct residues out of φ({m}) = {sum(1 for a in range(1, m) if gcd(a, m) == 1)} units")

    # Check if target is in residues
    print(f"\nTarget {target} in divisor residues: {target in residues}")

    return len(witnesses) == 0

def analyze_obstruction():
    """Analyze WHY the counterexample fails - what's the obstruction?"""
    print("\n" + "=" * 70)
    print("ANALYZING THE OBSTRUCTION")
    print("=" * 70)

    x = 1002
    m = 119  # = 7 × 17
    s = 6  # 29-smooth part (2 × 3)
    q = 167  # large prime

    print(f"\nx = {x} = {q} × {s}")
    print(f"m = {m} = 7 × 17")

    # Check the four families from GPT4's framework
    print(f"\n--- Checking GPT4's Four Families ---")

    # Family 1: d = q, requires s ≡ -1 (mod m)
    print(f"\nFamily 1 (d = q): Need s ≡ -1 (mod m)")
    print(f"  s mod m = {s % m}")
    print(f"  -1 mod m = {(-1) % m}")
    print(f"  s ≡ -1? {s % m == (-1) % m}")

    # Family 2: d = q·t with t | s², need t ≡ -s (mod m)
    print(f"\nFamily 2 (d = q·t): Need t | s² with t ≡ -s (mod m)")
    target_f2 = (-s) % m
    print(f"  Target: -s mod m = {target_f2}")
    divs_s2 = divisors_of_square(s)
    print(f"  Divisors of s² = {s**2}: {divs_s2}")
    print(f"  Their residues mod {m}: {[d % m for d in divs_s2]}")
    found_f2 = [d for d in divs_s2 if d % m == target_f2]
    print(f"  Divisors ≡ {target_f2}: {found_f2}")

    # Family 3: d = q²·t, need t ≡ -s·q⁻¹ (mod m)
    print(f"\nFamily 3 (d = q²·t): Need t | s² with t ≡ -s·q⁻¹ (mod m)")
    q_inv = pow(q, -1, m)
    target_f3 = ((-s) * q_inv) % m
    print(f"  q⁻¹ mod m = {q_inv}")
    print(f"  Target: -s·q⁻¹ mod m = {target_f3}")
    found_f3 = [d for d in divs_s2 if d % m == target_f3]
    print(f"  Divisors ≡ {target_f3}: {found_f3}")

    # Family 4: d = t (no q), need t ≡ -q·s (mod m)
    print(f"\nFamily 4 (d = t): Need t | s² with t ≡ -q·s (mod m)")
    target_f4 = ((-q) * s) % m
    print(f"  Target: -q·s mod m = {target_f4}")
    found_f4 = [d for d in divs_s2 if d % m == target_f4]
    print(f"  Divisors ≡ {target_f4}: {found_f4}")

    print(f"\n--- Summary ---")
    print(f"Family 1: {'✓' if s % m == (-1) % m else '✗'}")
    print(f"Family 2: {'✓' if found_f2 else '✗'}")
    print(f"Family 3: {'✓' if found_f3 else '✗'}")
    print(f"Family 4: {'✓' if found_f4 else '✗'}")

    # Subgroup analysis
    print(f"\n--- Subgroup Analysis ---")
    # H(s) = subgroup generated by prime factors of s = {2, 3}
    primes_s = [2, 3]
    H = {1}
    for p in primes_s:
        if gcd(p, m) > 1:
            print(f"  Warning: gcd({p}, {m}) > 1")
            continue
        r = p % m
        new = set()
        for h in H:
            power = 1
            for _ in range(m):
                new.add((h * power) % m)
                power = (power * r) % m
                if power == 1:
                    break
        H.update(new)

    print(f"H(s) = ⟨2, 3⟩ mod {m} = {sorted(H)}")
    print(f"|H(s)| = {len(H)}")

    neg1 = (-1) % m
    print(f"-1 mod {m} = {neg1}")
    print(f"-1 ∈ H(s): {neg1 in H}")

    if neg1 not in H:
        print(f"\n✓ OBSTRUCTION IDENTIFIED: -1 not in H(s)")
        print(f"  Since -1 ∉ H(s), we cannot reach -s from divisors of s²")

def check_is_k13_relevant():
    """Check if k=29 is in K13 and what this means."""
    print("\n" + "=" * 70)
    print("RELEVANCE TO K13")
    print("=" * 70)

    K13 = [0, 1, 2, 5, 7, 9, 11, 14, 17, 19, 23, 26, 29]
    print(f"\nK13 = {K13}")
    print(f"k = 29 is in K13: {29 in K13}")

    if 29 in K13:
        print(f"\n⚠ This counterexample is for k=29 which IS in K13!")
        print(f"  This means even within K13, 'large prime factor' isn't sufficient")
        print(f"  The failures we see are when ALL k in K13 fail, not just some")

if __name__ == "__main__":
    verify_counterexample()
    analyze_obstruction()
    check_is_k13_relevant()
