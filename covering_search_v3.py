#!/usr/bin/env python3
"""
Covering search v3: Divisor-pair approach.

Instead of ONLY using Lemma D.6 (which has a QR obstruction for prime M),
we also use the divisor-pair construction:

  Given P, offset delta ≡ 3 (mod 4), A = (P+delta)/4:
  Find divisors u, v of A with u + v = delta and u*v divides A.
  Then b = A/u, c = A/v gives (P+delta)(b+c) = 4*delta*b*c.

Actually, the correct construction: find d | A s.t. delta | (d + A/d).
Set b' = d, c' = A/d, then b'+c' = d + A/d ≡ 0 (mod delta).
Then b = d, c = A/d, offset = delta works IF the identity holds.

Let's verify: (P + delta)(b + c) = (P + delta)(d + A/d).
And 4*delta*b*c = 4*delta*d*(A/d) = 4*delta*A = 4*delta*(P+delta)/4 = delta*(P+delta).
So we need (P+delta)(d + A/d) = delta*(P+delta), i.e., d + A/d = delta.
That means u + v = delta where u=d, v=A/d, and u*v = A.

So the condition is: A has a factorization A = u*v with u + v = delta.
Equivalently: u and v are roots of t^2 - delta*t + A = 0.
This has integer solutions iff delta^2 - 4A >= 0 and is a perfect square.
Since delta = 4A - P: delta^2 - 4A = (4A-P)^2 - 4A = 16A^2 - 8AP + P^2 - 4A.

For A = (P + delta)/4 near P/4: delta ≈ 0 is too small, delta ≈ P gives
P^2 - 4*(P+P)/4 = P^2 - 2P which IS a perfect square for P large enough?
No, P^2 - 2P = (P-1)^2 - 1.

Let me re-derive more carefully. The Type II equation is:
  (P + offset)(b + c) = 4 * offset * b * c

Setting g = gcd(b,c), b = g*b', c = g*c' with gcd(b',c')=1:
  (P + offset)(b' + c') = 4 * offset * g * b' * c'

For g=1 (simplest case): (P + offset)(b' + c') = 4*offset*b'*c'.
This gives: P*b' + P*c' + offset*b' + offset*c' = 4*offset*b'*c'
P(b'+c') = offset(4b'c' - b' - c')
P = offset * (4b'c' - b' - c') / (b' + c')

For this to give integer P: (b'+c') | offset*(4b'c' - b' - c').
Since gcd(b',c')=1, gcd(b'+c', b'c') divides b'^2 + c'^2 or similar.

This is getting complicated. Let me just search directly.

For each prime P ≡ 1 (mod 24), try all offsets delta ≡ 3 (mod 4) up to some
bound, and for each, try to find b, c > 0 satisfying the identity.

Given (P, delta), A = (P+delta)/4. We need b, c > 0 with:
  (P + delta)(b + c) = 4*delta*b*c

Rearranging: 1/b + 1/c = (P+delta)/(4*delta*b*c) * (b+c) ...
Actually: A(b+c) = delta*b*c (since 4A = P+delta).
So: A/b + A/c = delta.
Let u = A/b, v = A/c. Then u+v = delta and b = A/u, c = A/v.
Need u | A and v | A and u + v = delta.

So: find two divisors u, v of A with u + v = delta = 4A - P.

This is a clean search: enumerate divisors of A, check if delta - d is also a divisor.
"""

import time
from math import gcd, isqrt
from collections import defaultdict


def is_prime(n):
    if n < 2: return False
    if n < 4: return True
    if n % 2 == 0 or n % 3 == 0: return False
    i = 5
    while i * i <= n:
        if n % i == 0 or n % (i + 2) == 0: return False
        i += 6
    return True


def divisors(n):
    """All divisors of n, sorted."""
    if n <= 0:
        return []
    small = []
    i = 1
    while i * i <= n:
        if n % i == 0:
            small.append(i)
            if i != n // i:
                small.append(n // i)
        i += 1
    return sorted(small)


def find_solution_divisor_pair(P, max_delta=200):
    """
    For prime P ≡ 1 (mod 24), find (offset, b, c) satisfying
    (P + offset)(b + c) = 4 * offset * b * c, offset ≡ 3 (mod 4).

    Method: for each delta ≡ 3 (mod 4), A = (P + delta)/4.
    Find divisors u, v of A with u + v = delta.
    Then b = A/u, c = A/v.
    """
    for delta in range(3, max_delta + 1, 4):  # delta ≡ 3 (mod 4)
        if (P + delta) % 4 != 0:
            continue  # shouldn't happen since P ≡ 1 mod 4
        A = (P + delta) // 4

        # Check window: A should be in [(P+3)/4, (3P-3)/4]
        # A = (P + delta)/4, so delta >= 3 gives A >= (P+3)/4. Good.
        # A <= (3P-3)/4 requires delta <= 2P - 3.

        # Find divisor pair: u + v = delta, u*v = A (NO! u|A and v|A and u+v=delta)
        # Actually: u + v = delta, b = A/u, c = A/v.
        # Need u | A AND v = delta - u AND v | A.

        divs_A = divisors(A)
        divs_set = set(divs_A)

        for u in divs_A:
            if u >= delta:
                break  # since v = delta - u must be > 0
            v = delta - u
            if v > 0 and v in divs_set:
                b = A // u
                c = A // v
                # Verify
                if (P + delta) * (b + c) == 4 * delta * b * c:
                    return (delta, b, c, A, u, v)

    return None


def find_solution_lemma_d6(P, max_r=30, max_s=30, max_alpha=10):
    """Try Lemma D.6 construction."""
    for alpha in range(1, max_alpha + 1):
        for s in range(1, max_s + 1):
            for r in range(1, max_r + 1):
                M = 4 * alpha * s * r - 1
                val = 4 * alpha * s * s + P
                if val % M != 0:
                    continue
                m = val // M
                c_prime = m * r - s
                if c_prime <= 0:
                    continue
                A = alpha * s * c_prime
                L = (P + 3) // 4
                U = (3 * P - 3) // 4
                if A < L or A > U:
                    continue
                offset = 4 * A - P
                g = alpha * r
                b = g * s
                c = g * c_prime
                if offset % 4 != 3 or b <= 0 or c <= 0:
                    continue
                if (P + offset) * (b + c) != 4 * offset * b * c:
                    continue
                return (offset, b, c, A)
    return None


def analyze_divisor_pair_congruences(max_delta=100, max_u=50):
    """
    For the divisor-pair method with fixed (delta, u):
    The congruence on P is: u | A and (delta - u) | A where A = (P+delta)/4.

    u | A means u | (P + delta)/4, i.e., P ≡ -delta (mod 4u).
    (delta-u) | A means (delta-u) | (P+delta)/4, i.e., P ≡ -delta (mod 4(delta-u)).

    Combined: P ≡ -delta (mod lcm(4u, 4(delta-u))) = P ≡ -delta (mod 4*lcm(u, delta-u)).

    The modulus is M_eff = 4 * lcm(u, delta-u).
    The residue is -delta mod M_eff.
    """
    print("=" * 78)
    print("DIVISOR-PAIR CONGRUENCE ANALYSIS")
    print("=" * 78)

    congruences = set()  # (modulus, residue)

    for delta in range(3, max_delta + 1, 4):
        for u in range(1, delta):
            v = delta - u
            if v <= 0:
                continue
            L = 4 * (u * v // gcd(u, v))  # 4 * lcm(u, v)
            res = (-delta) % L
            # Check: does this congruence target P ≡ 1 (mod 24)?
            if gcd(L, 24) > 0:
                # Check compatibility
                g = gcd(L, 24)
                if res % g != 1 % g:
                    continue  # incompatible with P ≡ 1 (mod 24)
            congruences.add((L, res))

    print(f"Total congruences found: {len(congruences)}")

    # Check: do these cover more than Lemma D.6?
    # Compute coverage mod a moderate Q
    from functools import reduce

    def lcm2(a, b):
        return a * b // gcd(a, b)

    # Use a moderate Q
    Q = 24 * 5 * 7 * 11 * 13  # = 120120
    target = set()
    for x in range(1, Q, 24):
        if gcd(x, Q) == 1:
            target.add(x)

    covered_d6 = set()
    covered_dp = set()

    # D6 coverage (from v2 search)
    from covering_search_v2 import get_residues_for_M, odd_part
    oQ = odd_part(Q)
    M_values = [d for d in divisors(oQ) if d % 4 == 3 and d >= 3]
    M_data = {}
    for M in M_values:
        res = get_residues_for_M(M)
        if res:
            M_data[M] = res

    for x in target:
        for M, residues in M_data.items():
            if x % M in residues:
                covered_d6.add(x)
                break

    # Divisor-pair coverage
    for L, res in congruences:
        if L > Q:
            continue
        if Q % L != 0:
            continue
        for x in target:
            if x % L == res:
                covered_dp.add(x)

    combined = covered_d6 | covered_dp

    print(f"\nCoverage mod Q={Q} ({len(target)} coprime targets):")
    print(f"  Lemma D.6 only:   {len(covered_d6)}/{len(target)} = {100*len(covered_d6)/len(target):.2f}%")
    print(f"  Divisor-pair only: {len(covered_dp)}/{len(target)} = {100*len(covered_dp)/len(target):.2f}%")
    print(f"  Combined:          {len(combined)}/{len(target)} = {100*len(combined)/len(target):.2f}%")
    print(f"  New from div-pair: {len(combined) - len(covered_d6)}")

    return congruences


def main():
    t0 = time.time()

    # Phase 1: Test divisor-pair method on primes
    print("=" * 78)
    print("PHASE 1: Testing divisor-pair method on primes ≡ 1 (mod 24)")
    print("=" * 78)

    max_P = 1_000_000
    checked = 0
    found_dp = 0
    found_d6 = 0
    failures = []
    dp_deltas = defaultdict(int)

    for P in range(25, max_P + 1, 24):
        if not is_prime(P):
            continue
        checked += 1

        # Try divisor-pair first
        result_dp = find_solution_divisor_pair(P, max_delta=200)
        if result_dp:
            found_dp += 1
            dp_deltas[result_dp[0]] += 1
            continue

        # Try Lemma D.6
        result_d6 = find_solution_lemma_d6(P, max_r=40, max_s=40, max_alpha=10)
        if result_d6:
            found_d6 += 1
            continue

        failures.append(P)

    print(f"\nChecked {checked} primes up to {max_P:,}")
    print(f"  Divisor-pair: {found_dp}")
    print(f"  Lemma D.6:    {found_d6}")
    print(f"  Failures:     {len(failures)}")

    if failures:
        print(f"  Failed primes: {failures[:30]}")
    else:
        print(f"  ALL PRIMES VERIFIED!")

    print(f"\nDivisor-pair delta distribution (top 15):")
    for delta, count in sorted(dp_deltas.items(), key=lambda x: -x[1])[:15]:
        print(f"  delta={delta:>5}: {count} primes")

    # Phase 2: Analyze congruences
    print()
    analyze_divisor_pair_congruences(max_delta=100)

    elapsed = time.time() - t0
    print(f"\nTotal time: {elapsed:.1f}s")


if __name__ == "__main__":
    main()
