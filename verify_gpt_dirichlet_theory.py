#!/usr/bin/env python3
"""
Verify GPT's Dirichlet Character Obstruction theory.

GPT claims: For ALL 14 K13 failures:
- All prime factors of x_0 are ≡ 1 (mod 3)  [kernel of quadratic char mod 3]
- All prime factors of x_1 are QRs mod 7    [kernel of quadratic char mod 7]
- All prime factors of x_2 are QRs mod 11   [kernel of quadratic char mod 11]

This would explain why k=0,1,2 all fail: the divisor residues are trapped
in the kernel of an odd character, but -x_k is NOT in the kernel.
"""

from math import gcd, isqrt

K13 = [0, 1, 2, 5, 7, 9, 11, 14, 17, 19, 23, 26, 29]
M_K = {k: 4*k + 3 for k in K13}

FAILURES = [
    10170169, 11183041, 22605361, 24966481, 30573481, 30619801,
    34103161, 35241529, 36851929, 36869281, 37228801, 45575401,
    46936849, 48991849
]

def legendre_symbol(a, p):
    """Compute Legendre symbol (a/p) for odd prime p."""
    a = a % p
    if a == 0:
        return 0
    result = pow(a, (p - 1) // 2, p)
    return -1 if result == p - 1 else result

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

def x_k(p, k):
    m = M_K[k]
    return (p + m) // 4

def verify_gpt_theory():
    """
    Verify GPT's claim about character obstructions for k=0,1,2.
    """
    print("VERIFYING GPT'S DIRICHLET CHARACTER THEORY")
    print("=" * 80)

    # The three key moduli
    test_cases = [
        (0, 3, "all primes ≡ 1 (mod 3)"),
        (1, 7, "all primes are QR mod 7"),
        (2, 11, "all primes are QR mod 11"),
    ]

    all_pass = True

    for k, m, description in test_cases:
        print(f"\n{'='*80}")
        print(f"k={k}, m_k={m}: Checking if {description}")
        print("=" * 80)

        k_passes = True

        for p in FAILURES:
            xk = x_k(p, k)
            facts = factor(xk)
            target = (-xk) % m

            # Check each prime factor
            prime_residues = []
            all_in_kernel = True

            for q, e in facts:
                if gcd(q, m) > 1:
                    # q divides m, skip
                    continue

                if m == 3:
                    # Kernel of quadratic char mod 3 is {1}
                    in_kernel = (q % 3 == 1)
                else:
                    # Kernel of quadratic char mod m (for prime m ≡ 3 mod 4)
                    # is the set of quadratic residues
                    in_kernel = (legendre_symbol(q, m) == 1)

                prime_residues.append((q, q % m, in_kernel))
                if not in_kernel:
                    all_in_kernel = False

            # Check if target is in kernel
            if m == 3:
                target_in_kernel = (target % 3 == 1)
            else:
                target_in_kernel = (legendre_symbol(target, m) == 1)

            # GPT's theory: all_in_kernel should be True, target_in_kernel should be False
            theory_predicts_failure = all_in_kernel and not target_in_kernel

            status = "✓" if all_in_kernel else "✗"

            if not all_in_kernel:
                k_passes = False
                # Find the non-kernel prime
                bad_primes = [(q, r) for q, r, ink in prime_residues if not ink]
                print(f"  p={p}: x_{k}={xk}")
                print(f"    FAILS: primes not in kernel: {bad_primes}")
            else:
                print(f"  p={p}: x_{k}={xk} - all {len(prime_residues)} prime factors in kernel, target={target} (in_kernel={target_in_kernel}) ✓")

        if k_passes:
            print(f"\n  ✓ GPT's claim VERIFIED for k={k}")
        else:
            print(f"\n  ✗ GPT's claim FAILS for k={k}")
            all_pass = False

    print(f"\n{'='*80}")
    print("OVERALL RESULT")
    print("=" * 80)

    if all_pass:
        print("GPT's Dirichlet character theory is VERIFIED for k=0,1,2!")
        print("All 14 failures have prime factors trapped in character kernels.")
    else:
        print("GPT's theory partially fails - some primes escape the kernel trap.")

    return all_pass

def check_alternative_extension():
    """
    GPT suggests {4, 13, 15, 22} as alternative extension.
    Let's verify this covers all 14 failures.
    """
    print(f"\n{'='*80}")
    print("VERIFYING GPT'S ALTERNATIVE EXTENSION: K13 + {4, 13, 15, 22}")
    print("=" * 80)

    def has_witness(p, k):
        m = 4*k + 3
        x = (p + m) // 4
        target = (-x) % m
        if target == 0:
            target = m
        x_sq = x * x
        d = target
        while d <= x:
            if d > 0 and x_sq % d == 0:
                return True
            d += m
        return False

    extension = [4, 13, 15, 22]

    for k in extension:
        covered = [p for p in FAILURES if has_witness(p, k)]
        print(f"  k={k} (m_k={4*k+3}): covers {len(covered)}/14 failures")
        if covered:
            print(f"    {covered}")

    # Check if union covers all
    uncovered = set(FAILURES)
    for k in extension:
        for p in list(uncovered):
            if has_witness(p, k):
                uncovered.discard(p)

    if uncovered:
        print(f"\n  Still uncovered: {uncovered}")
    else:
        print(f"\n  ✓ {extension} covers ALL 14 failures!")

if __name__ == "__main__":
    verify_gpt_theory()
    check_alternative_extension()
