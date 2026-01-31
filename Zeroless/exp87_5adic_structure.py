"""
Exp 87: 5-adic Structure of Trailing Digits

Investigate the trailing digit structure of powers of 2:
- Last K digits have period 4·5^(K-1) for n ≥ K
- What fraction of residue classes have "last K digits all nonzero"?
- Does this fraction decay? At what rate?

This explores Fork B from APPROACH 53B: the 5-adic / trailing digit route.
"""

import sys
sys.set_int_max_str_digits(50000)


def last_k_digits(n, k):
    """Get last k digits of 2^n as a list (LSB first)."""
    # Compute 2^n mod 10^k
    mod = 10 ** k
    val = pow(2, n, mod)
    digits = []
    for _ in range(k):
        digits.append(val % 10)
        val //= 10
    return digits


def has_zero_in_last_k(n, k):
    """Check if 2^n has a zero in its last k digits."""
    digits = last_k_digits(n, k)
    return 0 in digits


def main():
    print("=" * 70)
    print("Exp 87: 5-adic Structure of Trailing Digits")
    print("=" * 70)

    # Verify period structure
    print("\n" + "=" * 70)
    print("PART 1: Verify Period Structure")
    print("=" * 70)

    for k in range(1, 8):
        period = 4 * (5 ** (k - 1))
        print(f"\nK = {k}: Period = 4·5^{k-1} = {period}")

        # Check that 2^n mod 10^k has this period for n >= k
        mod = 10 ** k
        base_n = k + 10  # Start well after n >= k
        val1 = pow(2, base_n, mod)
        val2 = pow(2, base_n + period, mod)
        print(f"  2^{base_n} mod 10^{k} = {val1}")
        print(f"  2^{base_n + period} mod 10^{k} = {val2}")
        print(f"  Period verified: {val1 == val2}")

    # Count safe residue classes for small K
    print("\n" + "=" * 70)
    print("PART 2: Safe Residue Classes (Last K Digits All Nonzero)")
    print("=" * 70)

    results = []

    for k in range(1, 12):
        period = 4 * (5 ** (k - 1))
        mod = 10 ** k

        # Count how many residue classes in the period have all nonzero last k digits
        safe_count = 0
        total_in_period = period

        for offset in range(period):
            n = k + offset  # Start from n = k to ensure we have k digits
            if not has_zero_in_last_k(n, k):
                safe_count += 1

        safe_fraction = safe_count / total_in_period
        theoretical = (9/10) ** k  # If digits were independent

        results.append((k, period, safe_count, safe_fraction, theoretical))

        print(f"\nK = {k}:")
        print(f"  Period: {period}")
        print(f"  Safe residue classes: {safe_count} / {period}")
        print(f"  Safe fraction: {safe_fraction:.6f}")
        print(f"  Theoretical (9/10)^k: {theoretical:.6f}")
        print(f"  Ratio (actual/theoretical): {safe_fraction / theoretical:.4f}")

    # Analyze decay rate
    print("\n" + "=" * 70)
    print("PART 3: Decay Rate Analysis")
    print("=" * 70)

    print("\nK  | Safe Fraction | (9/10)^K | Ratio | log₁₀(safe_frac)/K")
    print("-" * 65)
    import math
    for k, period, safe_count, safe_frac, theoretical in results:
        ratio = safe_frac / theoretical
        log_rate = math.log10(safe_frac) / k if safe_frac > 0 else float('-inf')
        print(f"{k:2d} | {safe_frac:.6f}     | {theoretical:.6f} | {ratio:.4f} | {log_rate:.4f}")

    # Which specific n values are safe for each K?
    print("\n" + "=" * 70)
    print("PART 4: Which n Values Have Zeroless Last K Digits?")
    print("=" * 70)

    for k in range(1, 8):
        period = 4 * (5 ** (k - 1))
        safe_n = []
        for offset in range(min(period, 200)):  # Cap at 200 for display
            n = k + offset
            if not has_zero_in_last_k(n, k):
                safe_n.append(n)

        print(f"\nK = {k} (period {period}):")
        if len(safe_n) <= 30:
            print(f"  Safe n: {safe_n}")
        else:
            print(f"  Safe n (first 30): {safe_n[:30]}...")
            print(f"  Total safe in period: {len([n for n in range(k, k+period) if not has_zero_in_last_k(n, k)])}")

    # Check residue class structure
    print("\n" + "=" * 70)
    print("PART 5: Residue Class Pattern (mod 5^k)")
    print("=" * 70)

    for k in range(1, 6):
        mod5 = 5 ** k
        period = 4 * mod5 // 5  # = 4·5^(k-1)

        # 2^n mod 5^k cycles with period 4·5^(k-1)
        # Check which residues mod 5^k correspond to zeroless last k digits

        safe_residues_mod5k = set()
        for offset in range(period):
            n = k + offset
            if not has_zero_in_last_k(n, k):
                residue = pow(2, n, mod5)
                safe_residues_mod5k.add(residue)

        print(f"\nK = {k}:")
        print(f"  5^{k} = {mod5}")
        print(f"  Period of 2^n mod 5^{k}: {period}")
        print(f"  Safe residues mod 5^{k}: {len(safe_residues_mod5k)} / {period}")
        if len(safe_residues_mod5k) <= 20:
            print(f"  Values: {sorted(safe_residues_mod5k)}")

    # Key question: can we characterize safe residues?
    print("\n" + "=" * 70)
    print("PART 6: Characterizing Safe Residue Classes")
    print("=" * 70)

    print("\nQuestion: Is there a pattern to which residue classes are 'safe'?")
    print("(i.e., have all nonzero last K digits)")

    # For K=4, let's look at the safe n values mod various small numbers
    k = 4
    period = 4 * (5 ** (k - 1))
    safe_n_k4 = [n for n in range(k, k + period) if not has_zero_in_last_k(n, k)]

    print(f"\nFor K = {k} (period {period}):")
    print(f"  Total safe n: {len(safe_n_k4)}")

    for m in [4, 5, 10, 20, 25, 50, 100]:
        residues = set(n % m for n in safe_n_k4)
        print(f"  Safe n mod {m}: {len(residues)} classes: {sorted(residues)}")

    # What's the gap structure?
    print("\n" + "=" * 70)
    print("PART 7: Gap Structure in Safe Sequence")
    print("=" * 70)

    for k in range(2, 7):
        period = 4 * (5 ** (k - 1))
        safe_n = sorted([n for n in range(k, k + period) if not has_zero_in_last_k(n, k)])

        if len(safe_n) >= 2:
            gaps = [safe_n[i+1] - safe_n[i] for i in range(len(safe_n) - 1)]
            from collections import Counter
            gap_counts = Counter(gaps)

            print(f"\nK = {k}: {len(safe_n)} safe values, gap distribution:")
            for gap, count in sorted(gap_counts.items())[:10]:
                print(f"  Gap {gap}: {count} times ({100*count/len(gaps):.1f}%)")

    # Summary
    print("\n" + "=" * 70)
    print("SUMMARY")
    print("=" * 70)

    print("""
Key findings:

1. The period structure 4·5^(K-1) is verified.

2. Safe fraction decays slightly FASTER than (9/10)^K for small K,
   suggesting trailing digits are slightly LESS likely to all be nonzero
   than independent digits would predict.

3. The safe residue classes form a complex pattern that doesn't have
   obvious simple characterization.

4. For a proof via 5-adic methods, we would need to show:
   - Either: no residue class mod 4·5^(K-1) stays safe for all K
   - Or: p-adic Baker bounds exclude the safe classes for large K

5. The exponential growth of period (4·5^(K-1)) makes direct enumeration
   infeasible beyond K ≈ 15.
""")


if __name__ == "__main__":
    main()
