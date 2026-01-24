# TASK: Enumerate Obstruction Patterns B_k for Each k ∈ K10

## Context

For the Erdős-Straus proof, we need to classify when k fails (no Type II witness).

**Key insight (GPT6):** For each k ∈ K10, there is a finite list B_k of "bad residue multisets" such that:
- k fails for prime p ⟺ the multiset of prime factor residues of x_k (mod m_k) lies in B_k

## The Setup

- K10 = {5, 7, 9, 11, 14, 17, 19, 23, 26, 29}
- m_k = 4k + 3 for each k
- x_k = (p + m_k) / 4 = r + k where r = (p + 3) / 4

## The Obstruction Condition

k fails ⟺ D_m(x_k) ∩ (-D_m(x_k)) = ∅

Where D_m(x) = {d mod m : d | x}.

Equivalently: no two divisors a, b of x_k satisfy a ≡ -b (mod m_k).

## Your Task

Write Python code that:

1. For each k ∈ K10, enumerate minimal obstruction patterns
2. An obstruction pattern is a multiset of residues (mod m_k) that can appear as prime factors and cause failure
3. Use the exponent-sum model from GPT6's analysis

```python
from sympy import divisors, primefactors, primitive_root, discrete_log
from itertools import product
from collections import Counter

def get_divisor_residues(n, m):
    """Get set of divisor residues of n mod m"""
    return set(d % m for d in divisors(n) if d > 0)

def check_witness_exists(x, m):
    """Check if Type II witness exists: D_m(x) ∩ (-D_m(x)) ≠ ∅"""
    D = get_divisor_residues(x, m)
    neg_D = set((m - d) % m for d in D if d != 0)
    return bool(D & neg_D)

def check_witness_from_factorization(prime_residues, m):
    """
    Given a list of prime factor residues mod m,
    check if witness exists (using A·A framework).

    prime_residues: list of (residue, exponent) pairs
    """
    # Build divisor residue set
    # Divisors are products of prime factors with exponents 0 to e_i
    residues = {1}
    for (res, exp) in prime_residues:
        new_residues = set()
        for r in residues:
            for e in range(exp + 1):
                new_residues.add((r * pow(res, e, m)) % m)
        residues = new_residues

    # Check if any residue pairs to its negative
    for r in residues:
        if r != 0 and (m - r) % m in residues:
            return True
    return False

def enumerate_obstruction_patterns(m, max_prime_factors=5):
    """
    Enumerate minimal obstruction patterns for modulus m.

    An obstruction pattern is a multiset of residues in (Z/mZ)*
    such that the divisor residue set doesn't contain a negative pair.
    """
    # Get (Z/mZ)*
    units = [i for i in range(1, m) if gcd(i, m) == 1]

    obstruction_patterns = []

    # Try multisets of size 1, 2, 3, ...
    from itertools import combinations_with_replacement

    for size in range(1, max_prime_factors + 1):
        for pattern in combinations_with_replacement(units, size):
            # Convert to (residue, count) pairs
            counter = Counter(pattern)
            prime_residues = [(r, c) for r, c in counter.items()]

            # Check if this causes obstruction (no witness)
            if not check_witness_from_factorization(prime_residues, m):
                # Check if minimal (no proper sub-pattern also causes obstruction)
                is_minimal = True
                for r, c in prime_residues:
                    if c > 1:
                        reduced = [(r, c-1) if r == r else (r, c) for r, c in prime_residues]
                        if not check_witness_from_factorization(reduced, m):
                            is_minimal = False
                            break

                if is_minimal:
                    obstruction_patterns.append(pattern)

    return obstruction_patterns

from math import gcd

# Compute for each k in K10
K10 = [5, 7, 9, 11, 14, 17, 19, 23, 26, 29]

print("Obstruction Patterns for K10")
print("=" * 50)

for k in K10:
    m = 4 * k + 3
    print(f"\nk = {k}, m = {m}")
    print(f"  (Z/{m}Z)* has order {m - 1 if is_prime(m) else euler_phi(m)}")

    patterns = enumerate_obstruction_patterns(m, max_prime_factors=4)
    print(f"  Obstruction patterns (first 10):")
    for p in patterns[:10]:
        print(f"    {p}")
    if len(patterns) > 10:
        print(f"    ... and {len(patterns) - 10} more")
```

## Note on Efficiency

For prime m, (Z/mZ)* is cyclic, so the obstruction condition can be rephrased in terms of the discrete log. A pattern causes obstruction iff the signed subset sums of the discrete logs cannot reach (m-1)/2 (the log of -1).

## Deliverable

1. For each k ∈ K10, the list of minimal obstruction patterns B_k
2. Analysis of which patterns are ruled out by Hard10 constraints
3. Summary suitable for Lean formalization
