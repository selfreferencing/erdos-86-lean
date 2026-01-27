#!/usr/bin/env python3
"""
ed2_delta_coverage.py (GPT Part 2)

Fast coverage test for primes p ≡ 1 (mod 4) up to LIMIT.
Uses the "divisors of A²" method: for each δ = 3, 7, 11, ...,
set A = (p+δ)/4, factor A, enumerate divisors of A², and test
whether any divisor d satisfies d ≡ -A (mod δ).

Findings (up to 10^6):
- All 39,175 primes have a solution
- Smallest working δ is always ≤ 63
- The unique prime with minimal δ = 63 is p = 87481
"""

import math
from collections import Counter


def sieve_spf(n: int):
    """Smallest prime factor sieve up to n."""
    spf = list(range(n + 1))
    spf[0] = spf[1] = 0
    r = int(n**0.5)
    for i in range(2, r + 1):
        if spf[i] == i:  # i is prime
            step = i
            start = i * i
            for j in range(start, n + 1, step):
                if spf[j] == j:
                    spf[j] = i
    return spf


def primes_upto(n: int):
    """Simple bytearray sieve to list primes <= n."""
    bs = bytearray(b"\x01") * (n + 1)
    bs[0:2] = b"\x00\x00"
    r = int(n**0.5)
    for i in range(2, r + 1):
        if bs[i]:
            bs[i*i:n+1:i] = b"\x00" * (((n - i*i) // i) + 1)
    return [i for i in range(n + 1) if bs[i]]


def factorize(n: int, spf):
    """Factorize n using spf array -> dict prime->exponent."""
    fac = {}
    while n > 1:
        p = spf[n]
        if p == 0:
            p = n
        e = 0
        while n % p == 0:
            n //= p
            e += 1
        fac[p] = e
    return fac


def divisors_of_square(fac: dict):
    """
    Given factorization of A: fac[p]=e, build list of divisors of A^2.
    A^2 has exponents 2e, so divisor count is prod(2e+1).
    """
    divs = [1]
    for p, e in fac.items():
        maxe = 2 * e
        new = []
        pe = 1
        for _k in range(maxe + 1):
            for d in divs:
                new.append(d * pe)
            pe *= p
        divs = new
    return divs


def smallest_delta_for_prime(p: int, spf):
    """
    For prime p ≡ 1 mod 4:
      δ ranges 3,7,11,...,2p-3
      A = (p+δ)/4 (always integer here)
    Need: ∃ d|A^2 such that d ≡ -A (mod δ).
    Return smallest δ (and A) or (None,None) if none in full window.
    """
    max_delta = 2 * p - 3
    delta = 3
    while delta <= max_delta:
        A = (p + delta) // 4

        fac = factorize(A, spf)
        divs = divisors_of_square(fac)

        target = (-A) % delta
        for d in divs:
            if d % delta == target:
                return delta, A

        delta += 4

    return None, None


def main(limit=1_000_000, out_path="delta_by_prime.txt", summary=True):
    # A max is (3p-3)/4, so for p<=limit we need spf up to that.
    maxA = (3 * limit - 3) // 4

    spf = sieve_spf(maxA)
    ps = primes_upto(limit)
    ps = [p for p in ps if p % 4 == 1]

    failures = []
    delta_counts = Counter()

    with open(out_path, "w", encoding="utf-8") as f:
        for p in ps:
            delta, A = smallest_delta_for_prime(p, spf)
            if delta is None:
                failures.append(p)
                f.write(f"{p}\tFAIL\n")
            else:
                delta_counts[delta] += 1
                f.write(f"{p}\t{delta}\tA={A}\n")

    print(f"Checked {len(ps)} primes p≡1 (mod 4) with p ≤ {limit}.")
    if failures:
        print(f"FAILURES ({len(failures)}): first few = {failures[:20]}")
    else:
        print("No failures.")

    if summary:
        if delta_counts:
            max_delta = max(delta_counts)
            print(f"Max minimal δ observed: {max_delta}")
            print("δ distribution (δ : count):")
            for d in sorted(delta_counts):
                print(f"  {d:>3} : {delta_counts[d]}")


if __name__ == "__main__":
    main()
