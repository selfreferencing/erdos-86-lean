#!/usr/bin/env python3
"""
ed2_d6_bruteforce_verifier.py (GPT Part 1)

Combined D.6 + brute-force verifier for primes p ≡ 1 (mod 4) up to MAX_P.

- Tries D.6 certificates first (bounded by α, s, r ≤ D6_BOUND)
- Falls back to δ-A-divisor brute force if D.6 fails
- Verifies every solution against (4αd'b' - 1)(4αd'c' - 1) = 4αpd'² + 1
- Reports failures and the 10 hardest primes
"""

import sympy as sp
from collections import defaultdict

MAX_P = 100_000
D6_BOUND = 50
DELTA_MAX = 500

def verify(p, alpha, d, b, c):
    lhs = (4*alpha*d*b - 1) * (4*alpha*d*c - 1)
    rhs = 4*alpha*p*d*d + 1
    return lhs == rhs and b > 0 and c > 0 and d > 0 and alpha > 0

def try_D6(p):
    for alpha in range(1, D6_BOUND + 1):
        for s in range(1, D6_BOUND + 1):
            for r in range(1, D6_BOUND + 1):
                if alpha * s * r > D6_BOUND:
                    continue
                M = 4*alpha*s*r - 1
                if M <= 0:
                    continue
                num = 4*alpha*s*s + p
                if num % M != 0:
                    continue
                t = num // M
                c = t*r - s
                if c <= 0:
                    continue
                if verify(p, alpha, r, s, c):
                    return {
                        "method": "D6",
                        "alpha": alpha,
                        "d": r,
                        "b": s,
                        "c": c,
                        "delta": None
                    }
    return None

def try_bruteforce(p):
    best = None
    for delta in range(3, DELTA_MAX, 4):
        if (p + delta) % 4 != 0:
            continue
        A = (p + delta) // 4
        if A <= 0:
            continue
        A2 = A*A
        for d in sp.divisors(A2):
            if (d + A) % delta != 0:
                continue
            if (A2//d + A) % delta != 0:
                continue
            b = (d + A) // delta
            c = (A2//d + A) // delta
            if b <= 0 or c <= 0:
                continue
            # This construction corresponds to alpha = 1, d' = 1
            if verify(p, 1, 1, b, c):
                cert = {
                    "method": "bruteforce",
                    "alpha": 1,
                    "d": 1,
                    "b": b,
                    "c": c,
                    "delta": delta
                }
                if best is None or delta < best["delta"]:
                    best = cert
    return best

def main():
    primes = [p for p in sp.primerange(5, MAX_P+1) if p % 4 == 1]

    stats = defaultdict(int)
    failures = []
    hardness = []

    for p in primes:
        res = try_D6(p)
        if res is not None:
            stats["D6"] += 1
            hardness.append((p, 0, max(res["b"], res["c"])))
            continue

        res = try_bruteforce(p)
        if res is not None:
            stats["bruteforce"] += 1
            hardness.append((p, res["delta"], max(res["b"], res["c"])))
            continue

        failures.append(p)

    print("==== Statistics ====")
    print(f"Total primes checked: {len(primes)}")
    print(f"D.6 successes:       {stats['D6']}")
    print(f"Bruteforce successes:{stats['bruteforce']}")
    print(f"Failures:            {len(failures)}")

    if failures:
        print("\nFailures:")
        print(failures)

    print("\n==== 10 Hardest Primes ====")
    hardness.sort(key=lambda x: (x[1], x[2]), reverse=True)
    for p, delta, size in hardness[:10]:
        print(f"p={p:6d}  delta={delta:4d}  max(b,c)={size}")

if __name__ == "__main__":
    main()
