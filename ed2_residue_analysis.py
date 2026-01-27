#!/usr/bin/env python3
"""
Analyze ED2 existence by residue class mod 840.

Goal: For each residue class P ≡ r (mod 840) with r ≡ 1 (mod 4),
find which (α, d') pair works and verify it's consistent.
"""

from math import isqrt, gcd
from sympy import isprime, factorint
from collections import defaultdict

def is_squarefree(n):
    """Check if n is squarefree."""
    if n <= 0:
        return False
    for p, e in factorint(n).items():
        if e >= 2:
            return False
    return True

def find_ed2_factorization(N, alpha, d_prime):
    """
    Find factorization N = X * Y with X ≡ Y ≡ -1 (mod 4αd'), X ≤ Y.
    Returns (X, Y, b', c') or None.
    """
    mod = 4 * alpha * d_prime
    target = mod - 1  # -1 (mod mod)

    for x in range(1, isqrt(N) + 1):
        if N % x == 0:
            y = N // x
            if x % mod == target and y % mod == target:
                # Verify coprimality of b', c'
                b_prime = (x + 1) // mod
                c_prime = (y + 1) // mod
                if gcd(b_prime, c_prime) == 1:
                    return (x, y, b_prime, c_prime)
    return None

def find_working_params(P, max_delta=50):
    """
    For prime P ≡ 1 (mod 4), find smallest (α, d') that works.
    Returns (δ, α, d', X, Y, b', c') or None.
    """
    for d_prime in range(1, isqrt(max_delta) + 2):
        for alpha in range(1, max_delta // max(1, d_prime * d_prime) + 1):
            if not is_squarefree(alpha):
                continue
            delta = alpha * d_prime * d_prime
            if delta > max_delta:
                break

            N = 4 * alpha * P * d_prime * d_prime + 1
            result = find_ed2_factorization(N, alpha, d_prime)
            if result:
                X, Y, b_prime, c_prime = result
                return (delta, alpha, d_prime, X, Y, b_prime, c_prime)
    return None

def analyze_residue_classes():
    """Analyze which (α, d') works for each P (mod 840)."""

    # Residue classes r with r ≡ 1 (mod 4) and gcd(r, 840) = 1
    # 840 = 2³ × 3 × 5 × 7
    valid_residues = [r for r in range(1, 840) if r % 4 == 1 and gcd(r, 840) == 1]
    print(f"Number of valid residue classes mod 840: {len(valid_residues)}")

    # For each residue class, find example primes and what works
    residue_params = {}  # Maps residue -> list of (P, delta, alpha, d')

    # Check primes up to 100000
    primes_1mod4 = [p for p in range(5, 100001) if isprime(p) and p % 4 == 1]
    print(f"Checking {len(primes_1mod4)} primes P ≡ 1 (mod 4) up to 100000...")

    failures = []
    max_delta_seen = 0

    for P in primes_1mod4:
        r = P % 840
        result = find_working_params(P, max_delta=100)
        if result:
            delta, alpha, d_prime, X, Y, b_prime, c_prime = result
            if r not in residue_params:
                residue_params[r] = []
            residue_params[r].append((P, delta, alpha, d_prime))
            max_delta_seen = max(max_delta_seen, delta)
        else:
            failures.append(P)

    print(f"\nResults:")
    print(f"  Successes: {len(primes_1mod4) - len(failures)}")
    print(f"  Failures: {len(failures)}")
    print(f"  Max δ seen: {max_delta_seen}")

    if failures:
        print(f"\n  Failed primes: {failures[:20]}...")

    # Analyze consistency within each residue class
    print("\n" + "=" * 70)
    print("Residue class analysis (checking if same (α, d') works consistently):")

    inconsistent = []
    for r in sorted(residue_params.keys()):
        entries = residue_params[r]
        # Check if the same (α, d') works for all primes in this class
        param_counts = defaultdict(int)
        for P, delta, alpha, d_prime in entries:
            param_counts[(alpha, d_prime)] += 1

        # Most common parameter
        most_common = max(param_counts.items(), key=lambda x: x[1])
        (best_alpha, best_d), count = most_common
        total = len(entries)

        if count < total:
            # Not all primes use the same parameters
            inconsistent.append((r, param_counts, total))

    print(f"\nInconsistent residue classes: {len(inconsistent)}")
    for r, param_counts, total in inconsistent[:10]:
        print(f"  r ≡ {r} (mod 840): {dict(param_counts)}")

    # Check the minimum delta needed for each residue class
    print("\n" + "=" * 70)
    print("Maximum δ needed by residue class:")

    residue_max_delta = {}
    for r in sorted(residue_params.keys()):
        entries = residue_params[r]
        max_d = max(delta for P, delta, alpha, d_prime in entries)
        residue_max_delta[r] = max_d

    # Group by max delta
    delta_groups = defaultdict(list)
    for r, max_d in residue_max_delta.items():
        delta_groups[max_d].append(r)

    for delta in sorted(delta_groups.keys()):
        residues = delta_groups[delta]
        print(f"  δ ≤ {delta}: {len(residues)} residue classes")
        if len(residues) <= 10:
            print(f"    Classes: {residues}")

    # Identify the hardest cases
    print("\n" + "=" * 70)
    print("Hardest residue classes (largest δ needed):")

    hard_cases = [(r, residue_max_delta[r]) for r in residue_max_delta
                  if residue_max_delta[r] >= 5]
    hard_cases.sort(key=lambda x: -x[1])

    for r, max_d in hard_cases[:20]:
        # Show example primes
        examples = [P for P, delta, alpha, d_prime in residue_params[r] if delta == max_d][:3]
        print(f"  r ≡ {r} (mod 840): max δ = {max_d}, examples: {examples}")

    return residue_params, failures

def verify_specific_cases():
    """Verify the specific hard cases identified."""
    print("\n" + "=" * 70)
    print("Detailed verification of hard cases:")

    hard_primes = [37, 421, 997, 1429, 2221]  # Primes needing larger δ

    for P in hard_primes:
        if not isprime(P) or P % 4 != 1:
            continue
        print(f"\nP = {P} (≡ {P % 840} mod 840):")

        for delta in range(1, 50):
            # Try all (α, d') with α(d')² = δ
            for d_prime in range(1, isqrt(delta) + 1):
                if delta % (d_prime * d_prime) != 0:
                    continue
                alpha = delta // (d_prime * d_prime)
                if not is_squarefree(alpha):
                    continue

                N = 4 * alpha * P * d_prime * d_prime + 1
                mod = 4 * alpha * d_prime
                result = find_ed2_factorization(N, alpha, d_prime)

                if result:
                    X, Y, b_prime, c_prime = result
                    print(f"  δ={delta} (α={alpha}, d'={d_prime}): N={N}={X}×{Y}, "
                          f"b'={b_prime}, c'={c_prime} ✓")
                    break
            else:
                continue
            break
        else:
            print(f"  NO SOLUTION FOUND for δ ≤ 50")

def generate_lean_table():
    """Generate a table for Lean proof by residue class."""
    print("\n" + "=" * 70)
    print("Generating Lean-compatible table...")

    # For each residue class, find the minimal (α, d') that always works
    # We'll check primes up to 10000 to establish patterns

    primes_1mod4 = [p for p in range(5, 10001) if isprime(p) and p % 4 == 1]

    # Group by residue mod 840
    by_residue = defaultdict(list)
    for P in primes_1mod4:
        r = P % 840
        result = find_working_params(P, max_delta=100)
        if result:
            delta, alpha, d_prime, X, Y, b_prime, c_prime = result
            by_residue[r].append((P, alpha, d_prime))

    # For each residue, find which (α, d') works for ALL primes in that class
    print("\n-- Lean: Residue class → guaranteed (α, d') pair")
    print("-- Format: residue ↦ (alpha, d_prime)")

    lean_table = {}
    for r in sorted(by_residue.keys()):
        entries = by_residue[r]
        # Find (α, d') that works for all
        all_params = set()
        for P, alpha, d_prime in entries:
            all_params.add((alpha, d_prime))

        # Check each candidate
        for alpha, d_prime in sorted(all_params, key=lambda x: x[0] * x[1]**2):
            works_for_all = True
            for P, _, _ in entries:
                N = 4 * alpha * P * d_prime * d_prime + 1
                if not find_ed2_factorization(N, alpha, d_prime):
                    works_for_all = False
                    break
            if works_for_all:
                lean_table[r] = (alpha, d_prime)
                break

    # Group by (α, d')
    param_to_residues = defaultdict(list)
    for r, params in lean_table.items():
        param_to_residues[params].append(r)

    print("\n-- Summary by (α, d') pair:")
    for params in sorted(param_to_residues.keys(), key=lambda x: x[0] * x[1]**2):
        alpha, d_prime = params
        delta = alpha * d_prime**2
        residues = param_to_residues[params]
        print(f"-- (α={alpha}, d'={d_prime}) [δ={delta}]: {len(residues)} classes")

if __name__ == "__main__":
    residue_params, failures = analyze_residue_classes()
    verify_specific_cases()
    generate_lean_table()
