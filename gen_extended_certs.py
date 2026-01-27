#!/usr/bin/env python3
"""Generate extended Type II certificates for sorry-region primes.

Finds all primes in the sorry region up to bound B that are NOT covered
by any of the 22 D.6 M-values, then generates (offset, b, c) certificates
for each. Outputs both CSV and Lean-ready format.

Safe: Python-only, no Lean build triggered.
"""

import sys
import math
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
    if n <= 0: return []
    result = []
    i = 1
    while i * i <= n:
        if n % i == 0:
            result.append(i)
            if i != n // i:
                result.append(n // i)
        i += 1
    return sorted(result)


def in_sorry_region(p):
    """Check if p is in the sorry region (falls through mod 11/19/23 inline checks)."""
    if p % 24 != 1: return False
    if p % 7 not in (1, 2, 4): return False
    if p % 5 not in (1, 4): return False
    if p % 11 in (0, 7, 8, 10): return False
    if p % 19 in (0, 14, 15, 18): return False
    if p % 23 in (0, 7, 10, 11, 15, 17, 19, 20, 21, 22): return False
    return True


def get_d6_covered_residues(M):
    """Compute residues mod M covered by D.6."""
    if (M + 1) % 4 != 0:
        return set()
    k = (M + 1) // 4
    covered = set()
    for a in divisors(k):
        rem = k // a
        for s in divisors(rem):
            r = rem // s
            res = (-4 * a * s * s) % M
            covered.add(res)
    return covered


# The 22 D.6 M-values used in the Lean proof
D6_M_VALUES = [39, 47, 119, 159, 71, 95, 111, 143, 79, 87, 151, 59,
               191, 155, 199, 83, 127, 43, 99, 107, 131, 167]

# The 9 stubborn primes already handled by ed2_stubborn_primes
STUBBORN_PRIMES = {167521, 225289, 329401, 361321, 409081,
                   833281, 915961, 954409, 996361}


def is_covered_by_d6(p):
    """Check if prime p is covered by any of the 22 D.6 M-values."""
    for M in D6_M_VALUES:
        covered = get_d6_covered_residues(M)
        if p % M in covered:
            return True
    return False


def find_witness_d6(p, max_M=20000):
    """Try D6 construction with M values up to max_M."""
    for M in range(3, max_M + 1, 4):
        k = (M + 1) // 4
        if 4 * k - 1 != M:
            continue
        for a in divisors(k):
            rem = k // a
            for s in divisors(rem):
                r = rem // s
                res = (-4 * a * s * s) % M
                if p % M != res:
                    continue
                num_a = 4 * a * s * s
                if (p + num_a) % M != 0:
                    continue
                offset = (p + num_a) // M
                if offset % 4 != 3:
                    continue
                b_val = a * r * s
                if b_val <= 0:
                    continue
                denom = 4 * offset * b_val - p - offset
                if denom <= 0:
                    continue
                num = (p + offset) * b_val
                if num % denom != 0:
                    continue
                c_val = num // denom
                if c_val <= 0:
                    continue
                if (p + offset) * (b_val + c_val) == 4 * offset * b_val * c_val:
                    return (offset, b_val, c_val)
    return None


def find_witness_dp(p, max_delta=200000, max_b=5000):
    """Try divisor-pair construction (brute force over delta and b)."""
    for delta in range(3, max_delta + 1, 4):
        if (p + delta) % 4 != 0:
            continue
        A = (p + delta) // 4
        for b in range(1, min(delta + 1, max_b)):
            denom = 4 * delta * b - p - delta
            if denom <= 0:
                continue
            num = (p + delta) * b
            if num % denom != 0:
                continue
            c = num // denom
            if c > 0:
                return (delta, b, c)
    return None


def find_witness(p):
    """Find a Type II witness for prime p."""
    w = find_witness_d6(p)
    if w:
        return w
    w = find_witness_dp(p)
    if w:
        return w
    return None


def main():
    B = int(sys.argv[1]) if len(sys.argv) > 1 else 10_000_000

    print("=" * 70)
    print(f"Extended Certificate Generation for Sorry-Region Primes up to {B:,}")
    print("=" * 70)

    # Precompute D.6 coverage for each M
    d6_coverage = {}
    for M in D6_M_VALUES:
        d6_coverage[M] = get_d6_covered_residues(M)
    print(f"\nPrecomputed D.6 coverage for {len(D6_M_VALUES)} M-values")

    # Phase 1: Find all sorry-region primes up to B
    print(f"\nScanning for sorry-region primes up to {B:,}...")
    sorry_primes = []
    for p in range(25, B + 1, 24):  # p % 24 = 1, starting from 25
        if not is_prime(p):
            continue
        if not in_sorry_region(p):
            continue
        sorry_primes.append(p)

    print(f"Found {len(sorry_primes)} sorry-region primes up to {B:,}")

    # Phase 2: Filter out D.6-covered and stubborn primes
    uncovered = []
    d6_covered_count = 0
    stubborn_count = 0
    for p in sorry_primes:
        if p in STUBBORN_PRIMES:
            stubborn_count += 1
            continue
        covered = False
        for M in D6_M_VALUES:
            if p % M in d6_coverage[M]:
                covered = True
                break
        if covered:
            d6_covered_count += 1
        else:
            uncovered.append(p)

    print(f"\nD.6-covered: {d6_covered_count}")
    print(f"Stubborn (already handled): {stubborn_count}")
    print(f"Uncovered (need new certificates): {len(uncovered)}")

    if not uncovered:
        print("\nNo uncovered primes! The sorry region is fully handled.")
        return

    # Phase 3: Generate certificates for uncovered primes
    print(f"\nGenerating certificates for {len(uncovered)} uncovered primes...")
    certificates = {}
    failures = []

    for i, p in enumerate(uncovered):
        if (i + 1) % 100 == 0:
            print(f"  Progress: {i+1}/{len(uncovered)} ({100*(i+1)//len(uncovered)}%)")
        w = find_witness(p)
        if w:
            offset, b, c = w
            # Verify
            assert offset % 4 == 3, f"offset%4={offset%4} for p={p}"
            assert b > 0 and c > 0, f"b={b}, c={c} for p={p}"
            assert (p + offset) * (b + c) == 4 * offset * b * c, \
                f"Type II equation fails for p={p}"
            certificates[p] = (offset, b, c)
        else:
            failures.append(p)

    print(f"\nCertificates found: {len(certificates)}/{len(uncovered)}")
    if failures:
        print(f"FAILURES ({len(failures)}): {failures[:20]}...")
        if len(failures) > 20:
            print(f"  ... and {len(failures) - 20} more")

    # Phase 4: Output results
    # CSV file
    csv_path = f"/Users/kvallie2/Desktop/esc_stage8/extended_certs_{B}.csv"
    with open(csv_path, "w") as f:
        f.write("p,offset,b,c\n")
        for p, (offset, b, c) in sorted(certificates.items()):
            f.write(f"{p},{offset},{b},{c}\n")
    print(f"\nCSV written to {csv_path}")

    # Lean Type2Cert format
    lean_path = f"/Users/kvallie2/Desktop/esc_stage8/extended_certs_{B}_lean.txt"
    with open(lean_path, "w") as f:
        f.write(f"-- Extended Type II certificates for sorry-region primes\n")
        f.write(f"-- Primes from {min(uncovered):,} to {max(uncovered):,}\n")
        f.write(f"-- Total: {len(certificates)} certificates\n")
        f.write(f"-- Generated by gen_extended_certs.py\n\n")

        # Lean list format matching Type2CertData.lean
        f.write("def type2CertsExtended : List Type2Cert :=\n[\n")
        entries = sorted(certificates.items())
        for i, (p, (offset, b, c)) in enumerate(entries):
            comma = "," if i < len(entries) - 1 else ""
            f.write(f"  {{ p := {p}, offset := {offset}, b := {b}, c := {c} }}{comma}\n")
        f.write("]\n")
    print(f"Lean format written to {lean_path}")

    # Statistics
    print(f"\n{'='*70}")
    print("Statistics")
    print(f"{'='*70}")
    print(f"Total sorry-region primes up to {B:,}: {len(sorry_primes)}")
    print(f"  Covered by D.6: {d6_covered_count} ({100*d6_covered_count//len(sorry_primes)}%)")
    print(f"  Stubborn (Phase 2): {stubborn_count}")
    print(f"  Uncovered: {len(uncovered)} ({100*len(uncovered)//len(sorry_primes)}%)")
    print(f"  Certificates found: {len(certificates)}")
    print(f"  Failures: {len(failures)}")

    if certificates:
        offsets = [w[0] for w in certificates.values()]
        bs = [w[1] for w in certificates.values()]
        cs = [w[2] for w in certificates.values()]
        print(f"\nCertificate value ranges:")
        print(f"  Offset: {min(offsets)} to {max(offsets)} (median {sorted(offsets)[len(offsets)//2]})")
        print(f"  b: {min(bs)} to {max(bs)} (median {sorted(bs)[len(bs)//2]})")
        print(f"  c: {min(cs)} to {max(cs)} (median {sorted(cs)[len(cs)//2]})")

    # Summary for integration planning
    if not failures:
        print(f"\n*** ALL {len(uncovered)} uncovered primes have certificates! ***")
        print(f"Integration plan:")
        print(f"  1. Put {len(certificates)} certs in Type2CertDataExtended.lean")
        print(f"  2. Verify via native_decide in Type2CoveringExtended.lean")
        print(f"  3. At sorry in Existence.lean, split on p < {B}")
        print(f"  4. p < {B} branch: lookup in extended cert table")
        print(f"  5. p >= {B} branch: sorry (asymptotic argument needed)")
    else:
        print(f"\n{len(failures)} primes lack certificates. Increase search bounds.")


if __name__ == "__main__":
    main()
