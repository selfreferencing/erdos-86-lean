#!/usr/bin/env python3
"""
Find covering family - empirical approach.

For each prime P ≡ 1 (mod 4), find the minimal (α, d', x) template that works.
Collect all templates needed.
"""

import math
from collections import defaultdict

def gcd(a, b):
    while b:
        a, b = b, a % b
    return a

def is_squarefree(n):
    if n <= 0:
        return False
    i = 2
    while i * i <= n:
        if n % (i * i) == 0:
            return False
        i += 1
    return True

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

def find_template_for_prime(P, max_delta=100, max_x=100):
    """
    Find minimal template (α, d', x) for prime P.
    Returns (α, d', x, y) or None.
    """
    for delta in range(1, max_delta + 1):
        # Enumerate (α, d') with α * d'^2 = delta
        for d_prime in range(1, int(math.sqrt(delta)) + 1):
            if delta % (d_prime * d_prime) != 0:
                continue
            alpha = delta // (d_prime * d_prime)
            if not is_squarefree(alpha):
                continue

            # Try x values
            for x in range(1, max_x + 1):
                M = 4 * alpha * d_prime * x - 1
                numerator = P * d_prime + x

                if numerator % M != 0:
                    continue

                y = numerator // M
                if y < 1:
                    continue

                if gcd(x, y) != 1:
                    continue

                # Verify
                X = M
                Y = 4 * alpha * d_prime * y - 1
                N = X * Y
                expected = 4 * alpha * P * d_prime * d_prime + 1

                if N == expected:
                    return (alpha, d_prime, x, y, delta)

    return None

def main():
    print("Finding covering family empirically...")

    # Collect all primes P ≡ 1 (mod 4) up to 100,000
    primes = [p for p in range(5, 100001) if is_prime(p) and p % 4 == 1]
    print(f"Testing {len(primes)} primes")

    templates_used = defaultdict(list)  # (α, d', x) -> [primes using it]
    template_by_prime = {}  # P -> (α, d', x)

    for i, P in enumerate(primes):
        if i % 500 == 0:
            print(f"  Progress: {i}/{len(primes)}")

        result = find_template_for_prime(P)
        if result:
            alpha, d_prime, x, y, delta = result
            key = (alpha, d_prime, x)
            templates_used[key].append(P)
            template_by_prime[P] = key
        else:
            print(f"  FAILED: P = {P}")

    print(f"\n{'='*60}")
    print("TEMPLATES USED")
    print(f"{'='*60}")

    # Sort by frequency
    sorted_templates = sorted(templates_used.items(), key=lambda x: -len(x[1]))

    for (alpha, d_prime, x), primes_list in sorted_templates[:30]:
        M = 4 * alpha * d_prime * x - 1
        delta = alpha * d_prime * d_prime
        print(f"(α={alpha}, d'={d_prime}, x={x}): M={M}, δ={delta}, used by {len(primes_list)} primes")

    print(f"\n{'='*60}")
    print("SUMMARY")
    print(f"{'='*60}")
    print(f"Total templates needed: {len(templates_used)}")

    # Group by δ
    by_delta = defaultdict(list)
    for (alpha, d_prime, x), primes_list in templates_used.items():
        delta = alpha * d_prime * d_prime
        by_delta[delta].append(((alpha, d_prime, x), len(primes_list)))

    print("\nBy δ value:")
    for delta in sorted(by_delta.keys())[:20]:
        templates = by_delta[delta]
        total_primes = sum(count for _, count in templates)
        print(f"  δ={delta}: {len(templates)} templates, {total_primes} primes")

    # Find moduli
    moduli = set()
    for (alpha, d_prime, x), _ in templates_used.items():
        M = 4 * alpha * d_prime * x - 1
        moduli.add(M)

    print(f"\nDistinct moduli: {len(moduli)}")
    print(f"Moduli: {sorted(moduli)[:30]}...")

    # Check if small set suffices
    print(f"\n{'='*60}")
    print("MINIMAL COVERING ANALYSIS")
    print(f"{'='*60}")

    # Greedy: pick templates covering most uncovered primes
    uncovered = set(primes)
    selected = []

    while uncovered:
        best_template = None
        best_coverage = 0
        for key, primes_list in templates_used.items():
            coverage = len(set(primes_list) & uncovered)
            if coverage > best_coverage:
                best_coverage = coverage
                best_template = key

        if best_template is None:
            break

        selected.append(best_template)
        uncovered -= set(templates_used[best_template])
        print(f"Selected {best_template}: covers {best_coverage}, remaining {len(uncovered)}")

    print(f"\nMinimal covering size: {len(selected)} templates")

    print(f"\n{'='*60}")
    print("FINAL COVERING FAMILY")
    print(f"{'='*60}")
    for i, (alpha, d_prime, x) in enumerate(selected, 1):
        M = 4 * alpha * d_prime * x - 1
        delta = alpha * d_prime * d_prime
        count = len(templates_used[(alpha, d_prime, x)])
        print(f"{i}. (α={alpha}, d'={d_prime}, x={x}): M={M}, δ={delta}, covers {count} primes")

if __name__ == "__main__":
    main()
