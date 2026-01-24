#!/usr/bin/env python3
"""
Build the hierarchical CRT certificate for Erdős-Straus.

Based on GPT analysis:
- Level 1 (M=840): 90/96 classes covered by 15 universal recipes using k ∈ {0, 1, 3}
- Level 2: 6 resistant classes need larger modulus refinement

This script:
1. Verifies GPT's 15 recipes for M=840
2. Identifies which classes are universally covered
3. Identifies resistant classes
4. Tests which k values resolve resistant classes
"""

from math import gcd
from collections import defaultdict

# K_COMPLETE from our discovery
K_COMPLETE = [0, 1, 2, 3, 4, 5, 6, 7, 9, 11, 13, 14, 16, 17, 19, 21, 23, 25, 26, 29, 31, 39, 41]

# GPT's 15 recipes for M=840 (from Prompt 32 response)
# Format: (k, m_k, d, witness_type, description)
RECIPES_840 = [
    # k=0 (m=3)
    (0, 3, 2, "prime", "q=2"),
    (0, 3, 4, "square", "q=2, d=2²"),
    (0, 3, 5, "prime", "q=5"),
    (0, 3, 25, "square", "q=5, d=5²"),
    (0, 3, 7, "prime", "q=7"),
    # k=1 (m=7)
    (1, 7, 2, "prime", "q=2"),
    (1, 7, 4, "square", "q=2, d=2²"),
    (1, 7, 8, "product", "d=4·2"),
    (1, 7, 12, "product", "d=6·2"),
    (1, 7, 3, "prime", "q=3"),
    (1, 7, 5, "prime", "q=5"),
    (1, 7, 10, "product", "d=2·5"),
    (1, 7, 20, "product", "d=4·5"),
    # k=3 (m=15)
    (3, 15, 4, "square", "q=2, d=2²"),
    (3, 15, 7, "prime", "q=7"),
]

# The 6 resistant classes (Mordell-hard, perfect squares mod 840)
RESISTANT_CLASSES = [1, 121, 169, 289, 361, 529]

def get_admissible_classes(M=840):
    """Get all admissible residue classes mod M."""
    classes = []
    for r in range(1, M, 4):  # r ≡ 1 (mod 4)
        if gcd(r, M) == 1:
            classes.append(r)
    return classes

def check_recipe_covers_class(k, m_k, d, r, M=840):
    """
    Check if recipe (k, d) covers class r mod M.

    For the recipe to work universally, we need:
    1. The divisibility condition: rad(d) | x_k for all p ≡ r (mod M)
    2. The witness condition: d ≡ -x_k (mod m_k) for all p ≡ r (mod M)

    This requires:
    - p ≡ -m_k (mod 4·rad(d)) for divisibility
    - p ≡ -4d (mod m_k) for witness condition
    """
    # Compute rad(d) - product of distinct prime factors
    def rad(n):
        result = 1
        temp = n
        d_factor = 2
        while d_factor * d_factor <= temp:
            if temp % d_factor == 0:
                result *= d_factor
                while temp % d_factor == 0:
                    temp //= d_factor
            d_factor += 1
        if temp > 1:
            result *= temp
        return result

    rad_d = rad(d)

    # Required congruence for divisibility: p ≡ -m_k (mod 4·rad(d))
    div_mod = 4 * rad_d
    div_residue = (-m_k) % div_mod

    # Required congruence for witness: p ≡ -4d (mod m_k)
    wit_mod = m_k
    wit_residue = (-4 * d) % wit_mod

    # Check if r (mod M) is compatible with both conditions
    # This requires:
    # - r ≡ div_residue (mod gcd(M, div_mod))
    # - r ≡ wit_residue (mod gcd(M, wit_mod))

    g1 = gcd(M, div_mod)
    g2 = gcd(M, wit_mod)

    compatible_div = (r % g1) == (div_residue % g1)
    compatible_wit = (r % g2) == (wit_residue % g2)

    # Also need r ≡ 1 (mod 4) which is already ensured by admissibility

    return compatible_div and compatible_wit

def find_covering_recipes(M=840):
    """Find which recipes cover which classes."""
    admissible = get_admissible_classes(M)

    # Track coverage
    class_to_recipes = defaultdict(list)

    for r in admissible:
        for recipe in RECIPES_840:
            k, m_k, d, wtype, desc = recipe
            if check_recipe_covers_class(k, m_k, d, r, M):
                class_to_recipes[r].append(recipe)

    return class_to_recipes

def analyze_coverage():
    """Analyze certificate coverage at M=840."""
    print("=" * 70)
    print("CERTIFICATE ANALYSIS AT M = 840")
    print("=" * 70)

    admissible = get_admissible_classes(840)
    print(f"\nTotal admissible classes: {len(admissible)}")

    class_to_recipes = find_covering_recipes(840)

    covered = [r for r in admissible if class_to_recipes[r]]
    uncovered = [r for r in admissible if not class_to_recipes[r]]

    print(f"Covered by universal recipes: {len(covered)}")
    print(f"Not covered (resistant): {len(uncovered)}")

    print(f"\nResistant classes: {uncovered}")
    print(f"Expected (GPT): {RESISTANT_CLASSES}")

    # Check if resistant classes match Mordell-hard (perfect squares)
    mordell_hard = [r for r in uncovered if is_perfect_square_mod_840(r)]
    print(f"Mordell-hard in resistant: {mordell_hard}")

    # Show coverage breakdown
    print("\n" + "-" * 70)
    print("COVERAGE BY RECIPE")
    print("-" * 70)

    recipe_coverage = defaultdict(list)
    for r, recipes in class_to_recipes.items():
        if recipes:
            # Use first recipe
            key = (recipes[0][0], recipes[0][2])  # (k, d)
            recipe_coverage[key].append(r)

    for (k, d), classes in sorted(recipe_coverage.items()):
        print(f"k={k}, d={d}: {len(classes)} classes")

    return covered, uncovered

def is_perfect_square_mod_840(r):
    """Check if r is a perfect square mod 840."""
    for i in range(840):
        if (i * i) % 840 == r:
            return True
    return False

def test_resistant_class_coverage(resistant_classes, max_k=50):
    """
    For each resistant class, find which k ∈ K_COMPLETE resolves it.
    Uses direct prime testing.
    """
    print("\n" + "=" * 70)
    print("ANALYZING RESISTANT CLASS COVERAGE")
    print("=" * 70)

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
        if n <= 1:
            return []
        factors = []
        d = 2
        while d * d <= n:
            if n % d == 0:
                e = 0
                while n % d == 0:
                    e += 1
                    n //= d
                factors.append((d, e))
            d += 1 if d == 2 else 2
        if n > 1:
            factors.append((n, 1))
        return factors

    def divisors_of_square(n):
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

    def find_witness(p, k):
        m_k = 4 * k + 3
        if (p + m_k) % 4 != 0:
            return None
        x_k = (p + m_k) // 4
        if gcd(x_k, m_k) > 1:
            return None
        target = (-x_k) % m_k
        divs = divisors_of_square(x_k)
        for d in divs:
            if d % m_k == target:
                return d
        return None

    for r in resistant_classes:
        print(f"\nClass r ≡ {r} (mod 840):")

        # Find first few primes in this class
        primes = []
        p = r
        while len(primes) < 5 and p < 10**7:
            if p > 1 and is_prime(p):
                primes.append(p)
            p += 840

        print(f"  Sample primes: {primes[:3]}")

        # For each prime, find which k values work
        k_that_work = defaultdict(int)
        for p in primes:
            for k in K_COMPLETE:
                if k > max_k:
                    continue
                witness = find_witness(p, k)
                if witness is not None:
                    k_that_work[k] += 1

        # Show k values that work for all sample primes
        universal_k = [k for k, count in k_that_work.items() if count == len(primes)]
        print(f"  k values that work for ALL sample primes: {sorted(universal_k)}")

        if universal_k:
            # Show details for best k
            best_k = min(universal_k)
            print(f"  Using k={best_k} (m={4*best_k+3}):")
            for p in primes[:2]:
                witness = find_witness(p, best_k)
                print(f"    p={p}: witness d={witness}")

def main():
    # Analyze coverage at M=840
    covered, uncovered = analyze_coverage()

    # Test resistant classes
    if uncovered:
        test_resistant_class_coverage(uncovered)

    # Summary
    print("\n" + "=" * 70)
    print("SUMMARY")
    print("=" * 70)
    print(f"Level 1 (M=840): {len(covered)}/96 classes universally covered")
    print(f"Level 2 needed: {len(uncovered)} resistant classes")
    print(f"Resistant classes: {uncovered}")

if __name__ == "__main__":
    main()
