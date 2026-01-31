"""
Exp 60: Carry Cascade Dynamics and Protection Analysis

Key questions from APPROACH 50:
1. What is the actual protection rate for 5s in powers of 2?
2. How do 5-cascades (consecutive 5s) behave under doubling?
3. Is there a pattern in carry structure that explains termination?
4. Can we predict which n have protected vs unprotected 5s?
"""

def get_digits_and_carries(n):
    """
    Get digits of 2^n and the carry sequence when computing 2^{n+1}.
    Returns (digits, carries) where:
    - digits[i] = i-th digit of 2^n (LSB first)
    - carries[i] = carry entering position i when computing 2^{n+1}
    """
    power = 2 ** n
    digits = []
    while power > 0:
        digits.append(power % 10)
        power //= 10

    # Compute carry sequence
    carries = [0]  # Initial carry is 0
    carry = 0
    for d in digits:
        val = 2 * d + carry
        carry = val // 10
        carries.append(carry)

    return digits, carries[:-1]  # Remove last carry (overflow)


def analyze_protection(n):
    """
    Analyze protection status of all 5s in 2^n.
    Returns dict with counts and positions.
    """
    digits, carries = get_digits_and_carries(n)

    five_positions = [i for i, d in enumerate(digits) if d == 5]
    protected = [i for i in five_positions if carries[i] == 1]
    unprotected = [i for i in five_positions if carries[i] == 0]

    return {
        'n': n,
        'num_digits': len(digits),
        'num_fives': len(five_positions),
        'num_protected': len(protected),
        'num_unprotected': len(unprotected),
        'five_positions': five_positions,
        'protected_positions': protected,
        'unprotected_positions': unprotected,
        'protection_rate': len(protected) / len(five_positions) if five_positions else 1.0
    }


def find_five_cascades(n):
    """
    Find consecutive blocks of 5s in 2^n.
    Returns list of (start_pos, length) tuples.
    """
    digits, _ = get_digits_and_carries(n)

    cascades = []
    i = 0
    while i < len(digits):
        if digits[i] == 5:
            start = i
            while i < len(digits) and digits[i] == 5:
                i += 1
            length = i - start
            if length >= 2:  # Only report cascades of length >= 2
                cascades.append((start, length))
        else:
            i += 1

    return cascades


def trace_cascade_evolution(n, cascade_start, cascade_length):
    """
    Trace what happens to a 5-cascade through doublings.
    """
    results = []
    for k in range(5):  # Track through 5 doublings
        power = 2 ** (n + k)
        s = str(power)
        digits = [int(d) for d in reversed(s)]  # LSB first

        # Check if the cascade region still contains 5s
        region = digits[cascade_start:cascade_start + cascade_length] if cascade_start + cascade_length <= len(digits) else []

        results.append({
            'k': k,
            'power': n + k,
            'region': region,
            'has_fives': 5 in region,
            'all_fives': region == [5] * len(region) if region else False
        })

    return results


def main():
    print("=" * 70)
    print("Exp 60: Carry Cascade Dynamics and Protection Analysis")
    print("=" * 70)

    # Part A: Protection statistics across all powers
    print("\n" + "=" * 70)
    print("PART A: Protection statistics for 2^n, n = 0 to 200")
    print("=" * 70)

    zeroless = []
    stats_by_n = {}

    for n in range(201):
        power_str = str(2 ** n)
        is_zeroless = '0' not in power_str
        stats = analyze_protection(n)
        stats_by_n[n] = stats

        if is_zeroless:
            zeroless.append(n)

    print(f"\nZeroless powers: {zeroless}")
    print(f"Total: {len(zeroless)}")

    # Compare protection rates for zeroless vs zero-containing
    zeroless_rates = [stats_by_n[n]['protection_rate'] for n in zeroless if stats_by_n[n]['num_fives'] > 0]
    nonzeroless = [n for n in range(201) if n not in zeroless]
    nonzeroless_rates = [stats_by_n[n]['protection_rate'] for n in nonzeroless if stats_by_n[n]['num_fives'] > 0]

    print(f"\nProtection rate for zeroless powers: {sum(zeroless_rates)/len(zeroless_rates):.3f} (n={len(zeroless_rates)})")
    print(f"Protection rate for zero-containing powers: {sum(nonzeroless_rates)/len(nonzeroless_rates):.3f} (n={len(nonzeroless_rates)})")

    # Part B: Detailed analysis of late zeroless powers
    print("\n" + "=" * 70)
    print("PART B: Detailed analysis of late zeroless powers (n >= 30)")
    print("=" * 70)

    late_zeroless = [n for n in zeroless if n >= 30]
    print("\n  n | digits | #5s | #prot | #unprot | rate | cascades")
    print("-" * 70)

    for n in late_zeroless:
        s = stats_by_n[n]
        cascades = find_five_cascades(n)
        cascade_str = str(cascades) if cascades else "none"
        print(f" {n:3} | {s['num_digits']:6} | {s['num_fives']:3} | {s['num_protected']:5} | {s['num_unprotected']:7} | {s['protection_rate']:.2f} | {cascade_str}")

    # Part C: The n=76 cascade analysis
    print("\n" + "=" * 70)
    print("PART C: The n=76 cascade in detail")
    print("=" * 70)

    n = 76
    digits, carries = get_digits_and_carries(n)
    cascades = find_five_cascades(n)

    print(f"\n2^{n} = {2**n}")
    print(f"Digit count: {len(digits)}")
    print(f"5-cascades: {cascades}")

    if cascades:
        for start, length in cascades:
            print(f"\nCascade at positions {start}-{start+length-1}:")
            print(f"  Digits: {digits[start:start+length]}")
            print(f"  Carries entering: {carries[start:start+length]}")

            # Trace evolution
            evolution = trace_cascade_evolution(n, start, length)
            print(f"  Evolution through doublings:")
            for ev in evolution:
                print(f"    k={ev['k']}: 2^{ev['power']} region = {ev['region']}")

    # Part D: Carry structure analysis
    print("\n" + "=" * 70)
    print("PART D: Carry structure statistics")
    print("=" * 70)

    print("\nCarry=1 fraction by digit position (averaged over n=50-150):")

    # Collect carry statistics by position (as fraction of total digits)
    position_buckets = {i: [] for i in range(10)}  # 0-10%, 10-20%, etc.

    for n in range(50, 151):
        digits, carries = get_digits_and_carries(n)
        num_digits = len(digits)
        for i, c in enumerate(carries):
            bucket = min(9, int(10 * i / num_digits))
            position_buckets[bucket].append(c)

    print("  Position range | Avg carry | Sample size")
    print("-" * 50)
    for bucket in range(10):
        vals = position_buckets[bucket]
        if vals:
            avg = sum(vals) / len(vals)
            print(f"  {bucket*10:3}-{(bucket+1)*10:3}%       | {avg:.3f}     | {len(vals)}")

    # Part E: Why does protection fail?
    print("\n" + "=" * 70)
    print("PART E: Conditions when protection fails")
    print("=" * 70)

    print("\nFor each unprotected 5, what digit is to its right?")

    right_digit_counts = {d: 0 for d in range(10)}

    for n in range(10, 201):
        digits, carries = get_digits_and_carries(n)
        for i, d in enumerate(digits):
            if d == 5 and carries[i] == 0:
                if i > 0:
                    right_digit_counts[digits[i-1]] += 1

    print("\n  Right digit | Count | Cumulative %")
    print("-" * 40)
    total = sum(right_digit_counts.values())
    cumulative = 0
    for d in range(10):
        count = right_digit_counts[d]
        cumulative += count
        pct = 100 * cumulative / total if total > 0 else 0
        print(f"  {d:11} | {count:5} | {pct:.1f}%")

    # Part F: Predict termination
    print("\n" + "=" * 70)
    print("PART F: Can we predict unprotected 5 from digit count?")
    print("=" * 70)

    # For each n, track: num_fives, num_unprotected
    print("\nExpected vs actual unprotected 5s:")
    print("\n  n | digits | #5s | Expected unprot (4/9) | Actual | Difference")
    print("-" * 70)

    for n in late_zeroless:
        s = stats_by_n[n]
        expected = s['num_fives'] * (4/9)  # Using stationary distribution P(carry=0) = 4/9
        actual = s['num_unprotected']
        diff = actual - expected
        marker = " *** ANOMALY" if actual == 0 and s['num_fives'] > 0 else ""
        print(f" {n:3} | {s['num_digits']:6} | {s['num_fives']:3} | {expected:21.2f} | {actual:6} | {diff:+.2f}{marker}")

    # Part G: The transition 76 -> 77 -> 78
    print("\n" + "=" * 70)
    print("PART G: Full digit trace 76 -> 77 -> 78")
    print("=" * 70)

    for n in [76, 77, 78]:
        power = 2 ** n
        power_str = str(power)
        digits, carries = get_digits_and_carries(n)

        print(f"\n2^{n} = {power_str}")
        print(f"  Digits (LSB first): {digits}")
        print(f"  Carries:            {carries}")

        # Find 5s
        fives = [(i, 'P' if carries[i] == 1 else 'U') for i, d in enumerate(digits) if d == 5]
        print(f"  5s: {fives}  (P=protected, U=unprotected)")

        # Find zeros
        zeros = [i for i, d in enumerate(digits) if d == 0]
        print(f"  0s at positions: {zeros}")

    # Part H: Summary statistics
    print("\n" + "=" * 70)
    print("PART H: Summary")
    print("=" * 70)

    # Count how often protection rate = 1.0 for zeroless powers
    perfect_protection = [n for n in zeroless if stats_by_n[n]['num_fives'] > 0 and stats_by_n[n]['protection_rate'] == 1.0]
    print(f"\nZeroless powers with 100% protection: {perfect_protection}")
    print(f"Count: {len(perfect_protection)} out of {len([n for n in zeroless if stats_by_n[n]['num_fives'] > 0])}")

    # The theoretical expectation
    print("\n\nTheoretical prediction:")
    print("  If P(carry=1) = 5/9 ≈ 0.556 (stationary), then")
    print("  P(k 5s all protected) = (5/9)^k")
    print()
    for k in range(1, 6):
        prob = (5/9) ** k
        print(f"  k={k}: P = {prob:.4f}")

    print("\n  For n=76 with multiple 5s to all be protected is RARE.")
    print("  This explains why n=76 is an anomaly.")


if __name__ == "__main__":
    main()
