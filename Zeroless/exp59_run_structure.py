"""
Exp 59: Run Structure and Termination Analysis

Key insight from Exp 57/58: There are CONSECUTIVE RUNS of zeroless powers.
E.g., 31-37 are ALL zeroless (7 consecutive).

Questions:
1. What are all the runs?
2. What terminates each run?
3. Is there a pattern in run lengths?
4. What's special about the isolated late survivors (39, 49, 51, 67, etc.)?
"""

def is_zeroless(n):
    """Check if 2^n contains no zero digit."""
    return '0' not in str(2 ** n)

def find_unprotected_5_lsb(n):
    """
    Find positions where digit 5 has carry-in = 0 when doubling.
    Returns list of (position, context) tuples.
    """
    s = str(2 ** n)
    digits = [int(d) for d in reversed(s)]  # LSB first

    unprotected = []
    carry = 0
    for i, d in enumerate(digits):
        if d == 5 and carry == 0:
            # Get context: digit to left and right
            left = digits[i+1] if i+1 < len(digits) else None
            right = digits[i-1] if i > 0 else None
            unprotected.append((i, f"...{left if left else ''}[5]{right if right else ''}..."))
        val = 2 * d + carry
        carry = val // 10

    return unprotected

def main():
    print("=" * 70)
    print("Exp 59: Run Structure and Termination Analysis")
    print("=" * 70)

    # Part A: Identify all runs
    print("\n" + "=" * 70)
    print("PART A: All consecutive runs of zeroless powers")
    print("=" * 70)

    # Find all zeroless n up to 100
    zeroless = [n for n in range(101) if is_zeroless(n)]
    print(f"\nAll zeroless powers: {zeroless}")
    print(f"Count: {len(zeroless)}")

    # Identify runs
    runs = []
    current_run = [zeroless[0]]
    for i in range(1, len(zeroless)):
        if zeroless[i] == zeroless[i-1] + 1:
            current_run.append(zeroless[i])
        else:
            runs.append(current_run)
            current_run = [zeroless[i]]
    runs.append(current_run)

    print(f"\nRuns (consecutive sequences):")
    for i, run in enumerate(runs):
        print(f"  Run {i+1}: {run} (length {len(run)})")

    # Part B: What terminates each run?
    print("\n" + "=" * 70)
    print("PART B: Run termination analysis")
    print("=" * 70)

    print("\nFor each run, what causes the first zero in 2^{last+1}?")

    for run in runs:
        last_n = run[-1]
        next_n = last_n + 1

        power_last = 2 ** last_n
        power_next = 2 ** next_n

        # Find where zero appears
        s_next = str(power_next)
        zero_pos = s_next.find('0')

        # Check for unprotected 5 in 2^{last_n}
        up5 = find_unprotected_5_lsb(last_n)

        print(f"\nRun {run}:")
        print(f"  2^{last_n} = {power_last}")
        print(f"  2^{next_n} = {power_next}")
        print(f"  Zero at position {zero_pos} (from left) in 2^{next_n}")
        print(f"  Unprotected 5 in 2^{last_n}: {up5}")

        # Trace the specific zero creation
        digits_last = [int(d) for d in reversed(str(power_last))]
        carry = 0
        zero_created_at = []
        for i, d in enumerate(digits_last):
            val = 2 * d + carry
            d_out = val % 10
            if d_out == 0:
                zero_created_at.append((i, d, carry))
            carry = val // 10

        # Check MSB growth
        if len(str(power_next)) > len(str(power_last)):
            # New MSB digit
            new_msb = int(str(power_next)[0])
            print(f"  MSB grew: {len(str(power_last))} → {len(str(power_next))} digits")

        if zero_created_at:
            for pos, d, c in zero_created_at:
                print(f"  Zero created at pos {pos}: 2*{d}+{c}=10 → d=0")

    # Part C: Gap analysis
    print("\n" + "=" * 70)
    print("PART C: Gaps between runs")
    print("=" * 70)

    print("\nGaps between consecutive zeroless powers:")
    gaps = []
    for i in range(1, len(zeroless)):
        gap = zeroless[i] - zeroless[i-1]
        gaps.append((zeroless[i-1], zeroless[i], gap))

    # Group by gap size
    from collections import Counter
    gap_counts = Counter(g for _, _, g in gaps)
    print(f"\nGap distribution:")
    for gap_size in sorted(gap_counts.keys()):
        print(f"  Gap {gap_size}: {gap_counts[gap_size]} occurrences")

    # Show large gaps
    print(f"\nLarge gaps (> 5):")
    for prev, curr, gap in gaps:
        if gap > 5:
            print(f"  {prev} → {curr}: gap = {gap}")

    # Part D: Isolated survivors analysis
    print("\n" + "=" * 70)
    print("PART D: Isolated survivors (gap > 1 on both sides)")
    print("=" * 70)

    isolated = []
    for i, n in enumerate(zeroless):
        left_gap = n - zeroless[i-1] if i > 0 else float('inf')
        right_gap = zeroless[i+1] - n if i < len(zeroless) - 1 else float('inf')
        if left_gap > 1 and right_gap > 1:
            isolated.append((n, left_gap, right_gap))

    print(f"\nIsolated zeroless powers:")
    for n, lg, rg in isolated:
        power = 2 ** n
        digits = len(str(power))
        up5 = find_unprotected_5_lsb(n)
        print(f"  n={n}: gaps ({lg}, {rg}), {digits} digits, unprotected 5: {[p for p,_ in up5]}")

    # Part E: The final stretch
    print("\n" + "=" * 70)
    print("PART E: The final stretch (n ≥ 37)")
    print("=" * 70)

    print("\nAll zeroless n ≥ 37:")
    final_stretch = [n for n in zeroless if n >= 37]
    for n in final_stretch:
        power = 2 ** n
        digits = len(str(power))
        up5 = find_unprotected_5_lsb(n)
        up5_positions = [p for p, _ in up5]

        # Check what ends this one
        next_power = 2 ** (n+1)
        has_zero = '0' in str(next_power)

        print(f"  n={n}: {digits} digits, unprotected 5 at {up5_positions}, 2^{n+1} has zero: {has_zero}")

    # Part F: Pattern in unprotected 5 positions
    print("\n" + "=" * 70)
    print("PART F: Unprotected 5 position patterns")
    print("=" * 70)

    print("\nFor late zeroless n, where are the unprotected 5s?")
    for n in [39, 49, 51, 67, 72, 76, 77, 81, 86]:
        power = str(2 ** n)
        digits = len(power)
        up5 = find_unprotected_5_lsb(n)

        if up5:
            positions = [p for p, _ in up5]
            # Express as fraction of digit length
            fracs = [p / digits for p in positions]
            print(f"  n={n} ({digits} digits): positions {positions}, fractions {[f'{f:.2f}' for f in fracs]}")
        else:
            print(f"  n={n} ({digits} digits): NO unprotected 5!")

    # Part G: The n=76 anomaly
    print("\n" + "=" * 70)
    print("PART G: The n=76 anomaly (no unprotected 5, yet survives)")
    print("=" * 70)

    n = 76
    print(f"\n2^{n} = {2**n}")
    print(f"2^{n+1} = {2**(n+1)}")
    print(f"2^{n+2} = {2**(n+2)}")

    for k in [0, 1, 2]:
        m = n + k
        power = str(2 ** m)
        has_zero = '0' in power
        up5 = find_unprotected_5_lsb(m)
        print(f"\n  2^{m} = {power}")
        print(f"    zeroless: {not has_zero}, unprotected 5: {[p for p,_ in up5]}")

    # Trace 76 → 77 → 78
    print("\n  Carry trace from 76 → 77:")
    digits_76 = [int(d) for d in reversed(str(2**76))]
    digits_77 = [int(d) for d in reversed(str(2**77))]

    carry = 0
    for i, d in enumerate(digits_76):
        val = 2 * d + carry
        d_out = val % 10
        c_out = val // 10
        if d == 5:
            status = "protected" if carry == 1 else "UNPROTECTED"
            print(f"    pos {i}: 2*{d}+{carry}={val} → {d_out}, carry={c_out} ({status})")
        carry = c_out

if __name__ == "__main__":
    main()
