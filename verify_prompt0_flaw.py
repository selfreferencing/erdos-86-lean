#!/usr/bin/env python3
"""
Verify GPT's critical finding: Coverage is NOT a residue-class property.

Two primes with the same residue mod m_k can have different coverage outcomes
because coverage depends on the divisor structure of x_k, not just on p mod m_k.

Counterexamples provided by GPT:
1. k=0 (m=3): p=73 fails, p=97 succeeds (both p ≡ 1 mod 3)
2. k=1 (m=7): p=29 fails, p=113 succeeds (both p ≡ 1 mod 28)
"""

from math import gcd

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

def divisors_of_square(n):
    """Return all divisors of n²."""
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

def check_coverage(p, k):
    """
    Check if prime p is covered by k.
    Returns (covered, witness_d, x_k, divisor_residues)
    """
    m_k = 4 * k + 3
    x_k = (p + m_k) // 4
    target = (-x_k) % m_k

    divs = divisors_of_square(x_k)
    div_residues = [(d, d % m_k) for d in divs]

    witness = None
    for d in divs:
        if d % m_k == target:
            witness = d
            break

    return (witness is not None, witness, x_k, div_residues, target)

def verify_counterexample_k0():
    """Verify k=0 counterexample: p=73 fails, p=97 succeeds."""
    print("=" * 70)
    print("COUNTEREXAMPLE 1: k=0 (m_0 = 3)")
    print("=" * 70)

    k = 0
    m_k = 3

    # Both primes should have same residue mod 3
    p1, p2 = 73, 97
    print(f"\np1 = {p1}, p1 mod 3 = {p1 % 3}")
    print(f"p2 = {p2}, p2 mod 3 = {p2 % 3}")
    print(f"Both ≡ {p1 % 3} (mod 3): {p1 % 3 == p2 % 3}")

    # Check p1 = 73
    covered1, witness1, x1, divs1, target1 = check_coverage(p1, k)
    print(f"\n--- p = {p1} ---")
    print(f"x_0 = (73 + 3)/4 = {x1}")
    print(f"Divisors of x_0² = {x1**2}: {[d for d, _ in divs1]}")
    print(f"Divisor residues mod 3: {[r for _, r in divs1]}")
    print(f"Target: -x_0 mod 3 = {target1}")
    print(f"Covered: {covered1}, Witness: {witness1}")

    # Check p2 = 97
    covered2, witness2, x2, divs2, target2 = check_coverage(p2, k)
    print(f"\n--- p = {p2} ---")
    print(f"x_0 = (97 + 3)/4 = {x2}")
    print(f"Divisors of x_0² = {x2**2}: {[d for d, _ in divs2]}")
    print(f"Divisor residues mod 3: {[r for _, r in divs2]}")
    print(f"Target: -x_0 mod 3 = {target2}")
    print(f"Covered: {covered2}, Witness: {witness2}")

    if not covered1 and covered2:
        print(f"\n✓ COUNTEREXAMPLE VERIFIED:")
        print(f"  p=73 and p=97 have SAME residue mod 3")
        print(f"  But k=0 FAILS for p=73 and SUCCEEDS for p=97")
        print(f"  ⟹ Coverage is NOT a residue-class property!")
        return True
    else:
        print(f"\n✗ Counterexample NOT verified")
        return False

def verify_counterexample_k1():
    """Verify k=1 counterexample: p=29 fails, p=113 succeeds."""
    print("\n" + "=" * 70)
    print("COUNTEREXAMPLE 2: k=1 (m_1 = 7)")
    print("=" * 70)

    k = 1
    m_k = 7

    # Both primes should have same residue mod 28 (= 4 × 7)
    p1, p2 = 29, 113
    print(f"\np1 = {p1}, p1 mod 7 = {p1 % 7}, p1 mod 28 = {p1 % 28}")
    print(f"p2 = {p2}, p2 mod 7 = {p2 % 7}, p2 mod 28 = {p2 % 28}")
    print(f"Both ≡ {p1 % 28} (mod 28): {p1 % 28 == p2 % 28}")

    # Check p1 = 29
    covered1, witness1, x1, divs1, target1 = check_coverage(p1, k)
    print(f"\n--- p = {p1} ---")
    print(f"x_1 = (29 + 7)/4 = {x1}")
    print(f"Divisors of x_1² = {x1**2}: {[d for d, _ in divs1]}")
    print(f"Divisor residues mod 7: {[r for _, r in divs1]}")
    print(f"Target: -x_1 mod 7 = {target1}")
    print(f"Covered: {covered1}, Witness: {witness1}")

    # Check p2 = 113
    covered2, witness2, x2, divs2, target2 = check_coverage(p2, k)
    print(f"\n--- p = {p2} ---")
    print(f"x_1 = (113 + 7)/4 = {x2}")
    print(f"Divisors of x_1² = {x2**2}: {[d for d, _ in divs2]}")
    print(f"Divisor residues mod 7: {sorted(set([r for _, r in divs2]))}")
    print(f"Target: -x_1 mod 7 = {target2}")
    print(f"Covered: {covered2}, Witness: {witness2}")

    if not covered1 and covered2:
        print(f"\n✓ COUNTEREXAMPLE VERIFIED:")
        print(f"  p=29 and p=113 have SAME residue mod 28")
        print(f"  But k=1 FAILS for p=29 and SUCCEEDS for p=113")
        print(f"  ⟹ Coverage is NOT a residue-class property!")
        return True
    else:
        print(f"\n✗ Counterexample NOT verified")
        return False

def demonstrate_repaired_approach():
    """
    Demonstrate GPT's 'repaired' approach:
    Fix a specific small prime q as the witness divisor.
    """
    print("\n" + "=" * 70)
    print("GPT's REPAIRED APPROACH: Fix specific witness q")
    print("=" * 70)

    print("""
The flaw: "∃ d | x_k² with d ≡ -x_k (mod m_k)" depends on factorization.

The repair: For a fixed small prime q, ask:
  1. q | x_k  ⟺  p ≡ -m_k (mod 4q)
  2. q ≡ -x_k (mod m_k)  ⟺  p ≡ -4q (mod m_k)

Together by CRT: single residue class mod 4qm_k.
This IS a residue-class property!
""")

    # Example: k=1, q=5
    k, q = 1, 5
    m_k = 4 * k + 3  # = 7

    print(f"Example: k={k}, m_k={m_k}, q={q}")
    print(f"\nCondition 1: q | x_k")
    print(f"  x_k = (p + {m_k})/4")
    print(f"  {q} | x_k  ⟺  p ≡ -{m_k} (mod 4·{q}) = {(-m_k) % (4*q)} (mod {4*q})")
    cond1 = (-m_k) % (4*q)

    print(f"\nCondition 2: q ≡ -x_k (mod m_k)")
    print(f"  Need {q} ≡ -x_k (mod {m_k})")
    print(f"  Since x_k = (p + {m_k})/4 ≡ p · 4⁻¹ (mod {m_k})")
    four_inv = pow(4, -1, m_k)
    print(f"  4⁻¹ mod {m_k} = {four_inv}")
    print(f"  So: {q} ≡ -p · {four_inv} (mod {m_k})")
    print(f"  ⟺  p ≡ -{q} · 4 (mod {m_k}) = {(-4*q) % m_k} (mod {m_k})")
    cond2 = (-4*q) % m_k

    # CRT
    print(f"\nCRT: p ≡ {cond1} (mod {4*q}) AND p ≡ {cond2} (mod {m_k})")

    # Find solution
    from math import gcd
    mod1, mod2 = 4*q, m_k
    lcm_mod = (mod1 * mod2) // gcd(mod1, mod2)

    # Brute force CRT for small numbers
    for r in range(lcm_mod):
        if r % mod1 == cond1 and r % mod2 == cond2:
            print(f"Solution: p ≡ {r} (mod {lcm_mod})")

            # Verify with p=113
            print(f"\nVerification: p = 113")
            print(f"  113 mod {mod1} = {113 % mod1} (need {cond1}): {113 % mod1 == cond1}")
            print(f"  113 mod {mod2} = {113 % mod2} (need {cond2}): {113 % mod2 == cond2}")
            print(f"  113 mod {lcm_mod} = {113 % lcm_mod} (need {r}): {113 % lcm_mod == r}")
            break

def main():
    print("VERIFYING GPT's CRITICAL FINDING:")
    print("Coverage is NOT a residue-class property mod m_k")
    print("=" * 70)

    v1 = verify_counterexample_k0()
    v2 = verify_counterexample_k1()

    print("\n" + "=" * 70)
    print("SUMMARY")
    print("=" * 70)

    if v1 and v2:
        print("\n✓ BOTH COUNTEREXAMPLES VERIFIED")
        print("\nCRITICAL IMPLICATION:")
        print("  The 'residue class completeness check' approach from Prompt 0")
        print("  CANNOT work as stated because coverage depends on factorization,")
        print("  not just residue class.")
        print("\n  GPT's 'repair' is needed: fix specific small divisors q,")
        print("  then coverage becomes a true residue-class property.")
    else:
        print("\n⚠ Some counterexamples not verified - needs investigation")

    demonstrate_repaired_approach()

if __name__ == "__main__":
    main()
