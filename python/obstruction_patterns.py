"""
Minimal Obstruction Patterns for Erdős-Straus K10 Coverage
==========================================================

Key Lemma (Downward Closure):
  If y | x and D_m(x) ∩ (-D_m(x)) = ∅, then D_m(y) ∩ (-D_m(y)) = ∅.

Reason: Every divisor of y is also a divisor of x, so D_m(y) ⊆ D_m(x).
If D_m(y) contained a pair {a, -a}, then D_m(x) would too. Contradiction.

Corollary: Minimal obstruction patterns (under sub-multiset inclusion) are
exactly the singletons [a] where a ∈ (Z/mZ)* and a ≠ -1.

If the only prime factor has residue -1, then D_m(x) contains {1, -1},
giving an immediate witness d = 1 with d ≡ -x when x ≡ -1.
"""

from math import gcd
import json

K10 = [5, 7, 9, 11, 14, 17, 19, 23, 26, 29]

def units_mod(m: int):
    """Return all units in Z/mZ."""
    return [a for a in range(1, m) if gcd(a, m) == 1]

def minimal_obstruction_patterns(m: int):
    """
    Minimal obstruction patterns under multiset inclusion.

    By downward-closure of the obstruction condition under divisors,
    the only nonempty minimal obstruction patterns are singletons [a]
    with a ∈ (Z/mZ)* and a != -1 mod m.
    """
    minus_one = (-1) % m
    return [[a] for a in units_mod(m) if a != minus_one]

def B_for_K10():
    """Compute B_k for each k in K10."""
    out = {}
    for k in K10:
        m = 4*k + 3
        out[k] = {
            "m": m,
            "phi": len(units_mod(m)),
            "B_k": minimal_obstruction_patterns(m),
        }
    return out

def filter_Bk_by_allowed_residues(Bk, allowed_residues):
    """Filter B_k to only patterns with residues in allowed set."""
    allowed = set(allowed_residues)
    return [pat for pat in Bk if pat[0] in allowed]

if __name__ == "__main__":
    B = B_for_K10()

    print("Minimal Obstruction Patterns B_k for K10")
    print("=" * 50)

    for k in K10:
        m = B[k]["m"]
        phi = B[k]["phi"]
        size = len(B[k]["B_k"])
        print(f"k={k:2d}, m={m:3d}, φ(m)={phi:3d}, |B_k|={size:3d}")

    print()
    print("Summary:")
    print("-" * 50)
    print("For prime m: |B_k| = m - 2 (excludes 0 and -1)")
    print("For composite m: |B_k| = φ(m) - 1 (excludes -1 from units)")

    # Save to JSON
    output = {}
    for k in K10:
        m = 4*k + 3
        output[str(k)] = {
            "m": m,
            "patterns": [p[0] for p in B[k]["B_k"]]  # Just the residue values
        }

    with open("/Users/kvallie2/Desktop/esc_stage8/data/B_k_singletons.json", "w") as f:
        json.dump(output, f, indent=2)

    print()
    print("Saved to B_k_singletons.json")
