#!/usr/bin/env python3
"""
Verify GPT5's key insight: the target residue r_k = -1/4 (mod m_k)
is always a quadratic NON-residue for m_k = 4k+3.

This is the root cause of the obstruction!
"""

from math import gcd

K13 = [0, 1, 2, 5, 7, 9, 11, 14, 17, 19, 23, 26, 29]

def legendre_symbol(a, p):
    """Compute Legendre symbol (a/p) for odd prime p."""
    a = a % p
    if a == 0:
        return 0
    result = pow(a, (p - 1) // 2, p)
    return -1 if result == p - 1 else result

def jacobi_symbol(a, n):
    """Compute Jacobi symbol (a/n)."""
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

def factor(n):
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

def verify_target_residue():
    """
    GPT5 claims: For each k, the target r_k = -1/4 (mod m_k) is a quadratic NON-residue.

    This is because:
    - m_k = 4k+3 ≡ 3 (mod 4)
    - For such moduli, -1 is a non-QR
    - 4 is always a QR (it's 2²)
    - So -1/4 = (-1) × (1/4) has the same character as -1, which is -1 (non-QR)
    """
    print("=" * 70)
    print("VERIFYING GPT5's TARGET RESIDUE CLAIM")
    print("=" * 70)
    print("\nFor each k in K13, compute r_k = -4^{-1} (mod m_k)")
    print("and verify it's a quadratic NON-residue.\n")

    print(f"{'k':>3} | {'m_k':>4} | {'4^{-1}':>6} | {'r_k=-4^{-1}':>10} | {'Jacobi(r_k/m_k)':>15} | {'Is prime?'}")
    print("-" * 70)

    all_non_qr = True

    for k in K13:
        mk = 4 * k + 3

        # Compute 4^{-1} mod m_k
        four_inv = pow(4, -1, mk)

        # r_k = -4^{-1} mod m_k
        rk = (-four_inv) % mk

        # Compute Jacobi symbol
        jac = jacobi_symbol(rk, mk)

        # Check if m_k is prime
        prime = is_prime(mk)

        status = "✓ NON-QR" if jac == -1 else ("QR" if jac == 1 else "?")
        if jac != -1:
            all_non_qr = False

        print(f"{k:>3} | {mk:>4} | {four_inv:>6} | {rk:>10} | {jac:>15} | {prime}")

    print("\n" + "=" * 70)
    if all_non_qr:
        print("✓ VERIFIED: All target residues r_k are quadratic NON-residues!")
        print("\nThis explains the obstruction mechanism:")
        print("  - If ALL prime factors of x_k are QRs mod m_k")
        print("  - Then ALL divisors of x_k² are QRs mod m_k")
        print("  - But the target r_k is a NON-QR")
        print("  - Therefore NO divisor can hit the target → no witness exists!")
    else:
        print("⚠ Some targets are not non-QRs - needs investigation")

def show_equivalent_formulations():
    """
    Show the equivalence between our formulation and GPT5's.
    """
    print("\n" + "=" * 70)
    print("EQUIVALENCE OF FORMULATIONS")
    print("=" * 70)

    print("""
Our formulation:
  - Find d | x_k² with d ≡ -x_k (mod m_k)

GPT5's formulation (after simplification):
  - Find q | x_k² with q ≡ r_k (mod m_k) where r_k = -1/4 (mod m_k)

Proof of equivalence:
  1. d ≡ -x_k (mod m_k)
  2. Since gcd(x_k, m_k) = 1, multiply both sides by x_k^{-1}:
     d · x_k^{-1} ≡ -1 (mod m_k)
  3. Let q = x_k²/d (the complementary divisor). Then:
     q ≡ x_k² · d^{-1} ≡ x_k² · (-x_k)^{-1} ≡ -x_k (mod m_k)

Wait, that gives q ≡ -x_k, not q ≡ -1/4...

Let me re-derive GPT5's formulation properly:
  1. Original: d ≡ -px_k (mod m_k) where p = 4x_k - m_k
  2. So px_k = (4x_k - m_k)x_k = 4x_k² - m_k·x_k ≡ 4x_k² (mod m_k)
  3. Thus: d ≡ -4x_k² (mod m_k)
  4. Setting q = x_k²/d: q ≡ x_k²/(-4x_k²) ≡ -1/4 (mod m_k)

So GPT5 is using the ORIGINAL Bradford formulation d ≡ -px (mod 4x-p),
while we simplified to d ≡ -x (mod m_k).

Let me verify these are equivalent...
""")

    # Check on a specific example
    p = 10170169  # First failure
    k = 0
    mk = 3
    t = (p + 3) // 4
    xk = t + k

    print(f"\nExample: p = {p}, k = {k}")
    print(f"  m_k = {mk}")
    print(f"  x_k = {xk}")

    # Our target: -x_k mod m_k
    our_target = (-xk) % mk
    print(f"  Our target: -x_k mod m_k = {our_target}")

    # GPT5's target: -4x_k² mod m_k, then normalize by x_k²
    gpt5_target = (-4 * xk * xk) % mk
    print(f"  GPT5's target: -4x_k² mod m_k = {gpt5_target}")

    # These should differ by a factor of 4x_k
    # d ≡ -4x_k² means d·(4x_k)^{-1} ≡ -x_k
    # So if we find d ≡ -4x_k², then d/(4x_k) ≡ -x_k (conceptually)

    # Actually, let's verify: for d | x², is d ≡ -x_k (mod m_k) equivalent to
    # d ≡ -4x_k² (mod m_k)?
    #
    # -4x_k² = -4·x_k·x_k ≡ -x_k·(4x_k) ≡ -x_k·(m_k + p) ≡ -x_k·p (mod m_k)
    # So d ≡ -px_k (mod m_k), which is Bradford's original!

    print(f"\n  Note: -4x_k² ≡ -px_k (mod m_k) since 4x_k ≡ p (mod m_k)")
    print(f"  Verify: 4·{xk} mod {mk} = {(4*xk) % mk}, p mod {mk} = {p % mk}")

def analyze_rescue_mechanism():
    """
    Analyze why k=31, 39, 41 rescue the failures.
    """
    print("\n" + "=" * 70)
    print("WHY k=31, 39, 41 RESCUE THE FAILURES")
    print("=" * 70)

    FAILURES = [
        10170169, 11183041, 22605361, 24966481, 30573481, 30619801,
        34103161, 35241529, 36851929, 36869281, 37228801, 45575401,
        46936849, 48991849
    ]

    rescue_k = [31, 39, 41]

    for k in rescue_k:
        mk = 4 * k + 3
        four_inv = pow(4, -1, mk)
        rk = (-four_inv) % mk

        print(f"\nk={k}: m_k={mk}, r_k={rk}")
        print(f"  Factor(m_k) = {factor(mk)}")

        # For each failure, check if x_k has a non-QR prime factor
        covered = 0
        for p in FAILURES:
            t = (p + 3) // 4
            xk = t + k
            facts = factor(xk)

            # Check if any prime factor is a non-QR mod m_k
            has_nonqr = False
            for q, e in facts:
                if gcd(q, mk) > 1:
                    continue
                jac = jacobi_symbol(q, mk)
                if jac == -1:
                    has_nonqr = True
                    break

            if has_nonqr:
                covered += 1

        print(f"  Covers {covered}/14 failures (by having non-QR prime factor)")

if __name__ == "__main__":
    verify_target_residue()
    show_equivalent_formulations()
    analyze_rescue_mechanism()
