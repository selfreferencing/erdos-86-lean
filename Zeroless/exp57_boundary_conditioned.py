"""
Exp 57: Boundary-Conditioned T_k Analysis

The k-step transfer operator T_k counts ALL m-digit numbers N such that
N, 2N, 4N, ..., 2^k N are all zeroless.

But for the specific orbit 2^n, the digits are NOT arbitrary - they're
determined by the doubling dynamics. This experiment asks:

For each n, consider the "spacetime" grid:
- Row 0: digits of 2^n
- Row 1: digits of 2^{n+1}
- ...
- Row k: digits of 2^{n+k}

The BOUNDARY CONDITION is that each row must equal the actual 2^{n+j}.

Question: For which n does this spacetime grid contain a zero?
At what "height" k does the first zero appear?

This directly targets whether the orbit can stay zeroless.
"""

from collections import defaultdict

def get_digits(n_val):
    """Get decimal digits of 2^n as a list (LSB first)."""
    if n_val == 0:
        return [1]
    power = 2 ** n_val
    digits = []
    while power > 0:
        digits.append(power % 10)
        power //= 10
    return digits

def first_zero_position(n_val):
    """Find first position (from right) where 2^n has a zero, or -1 if none."""
    digits = get_digits(n_val)
    for i, d in enumerate(digits):
        if d == 0:
            return i
    return -1

def analyze_zero_height(n_start, n_end):
    """
    For each n in range, find the smallest k such that 2^{n+k} contains a zero.
    This is the "height at which the orbit first hits zero" starting from n.
    """
    results = []
    for n in range(n_start, n_end + 1):
        # Find smallest k >= 0 such that 2^{n+k} has a zero
        k = 0
        while True:
            pos = first_zero_position(n + k)
            if pos >= 0:
                results.append((n, k, pos))
                break
            k += 1
            if k > 200:  # Safety limit
                results.append((n, -1, -1))
                break
    return results

def analyze_spacetime_pattern(n, max_height=50):
    """
    Analyze the spacetime digit pattern starting at 2^n.
    Returns the height at which first zero appears, and position info.
    """
    for k in range(max_height + 1):
        digits = get_digits(n + k)
        for pos, d in enumerate(digits):
            if d == 0:
                return {
                    'n': n,
                    'first_zero_height': k,
                    'first_zero_position': pos,
                    'power_with_zero': n + k
                }
    return {
        'n': n,
        'first_zero_height': -1,
        'first_zero_position': -1,
        'power_with_zero': -1
    }

def analyze_suffix_evolution(n, k_steps, m_digits):
    """
    Track how the last m digits evolve through k doubling steps.
    Returns True if all k+1 rows (2^n through 2^{n+k}) have zeroless last-m digits.
    """
    for step in range(k_steps + 1):
        power = 2 ** (n + step)
        suffix = power % (10 ** m_digits)
        suffix_str = str(suffix).zfill(m_digits)
        if '0' in suffix_str:
            return False, step
    return True, k_steps + 1

def main():
    print("=" * 70)
    print("Exp 57: Boundary-Conditioned T_k Analysis")
    print("=" * 70)

    # Part A: For each n, when does the orbit first hit a zero?
    print("\n" + "=" * 70)
    print("PART A: Height to first zero for each n")
    print("=" * 70)

    results = analyze_zero_height(0, 100)

    # Group by height
    by_height = defaultdict(list)
    for n, k, pos in results:
        by_height[k].append(n)

    print("\nDistribution of 'height to first zero':")
    for k in sorted(by_height.keys()):
        if k <= 10:
            print(f"  k = {k}: n ∈ {by_height[k][:20]}{'...' if len(by_height[k]) > 20 else ''}")
        else:
            print(f"  k = {k}: {len(by_height[k])} values")

    # The zeroless n are those where first zero is at k=1 (meaning 2^n is zeroless, 2^{n+1} has zero)
    # Wait, that's not right. k=0 means 2^n itself has a zero.
    # Zeroless powers are those with k > 0.

    zeroless_n = [n for n, k, pos in results if k > 0]
    print(f"\nZeroless powers of 2 (k > 0): {zeroless_n}")
    print(f"Count: {len(zeroless_n)}")

    # Part B: For the last few zeroless powers, analyze in detail
    print("\n" + "=" * 70)
    print("PART B: Detailed analysis of late zeroless powers")
    print("=" * 70)

    late_zeroless = [n for n in zeroless_n if n >= 50]
    for n in late_zeroless:
        info = analyze_spacetime_pattern(n)
        digits_n = get_digits(n)
        print(f"\nn = {n}: 2^{n} has {len(digits_n)} digits")
        print(f"  2^{n} = {2**n}")
        print(f"  First zero appears at 2^{info['power_with_zero']} (height k={info['first_zero_height']})")
        print(f"  Zero position from right: {info['first_zero_position']}")

    # Part C: Suffix evolution analysis
    print("\n" + "=" * 70)
    print("PART C: Suffix evolution (last m digits through k doublings)")
    print("=" * 70)

    # For n = 86 (last zeroless), track suffix evolution
    n = 86
    print(f"\nAnalyzing n = {n} (last zeroless power):")
    print(f"2^{n} = {2**n}")

    for m in [4, 6, 8, 10]:
        for k in [1, 2, 3, 5, 10]:
            ok, fail_step = analyze_suffix_evolution(n, k, m)
            if ok:
                print(f"  m={m}, k={k}: All {k+1} suffixes zeroless ✓")
            else:
                print(f"  m={m}, k={k}: Zero appears at step {fail_step}")

    # Part D: The critical transition 86 → 87
    print("\n" + "=" * 70)
    print("PART D: The 86 → 87 transition (carry analysis)")
    print("=" * 70)

    n = 86
    print(f"\n2^{n} = {2**n}")
    print(f"2^{n+1} = {2**(n+1)}")

    digits_86 = get_digits(86)
    digits_87 = get_digits(87)

    print(f"\nDigit-by-digit doubling (LSB first):")
    print("Pos | d_86 | carry_in | 2*d+c | d_87 | carry_out")
    print("-" * 55)

    carry = 0
    for i in range(max(len(digits_86), len(digits_87))):
        d_86 = digits_86[i] if i < len(digits_86) else 0
        val = 2 * d_86 + carry
        d_87_computed = val % 10
        carry_out = val // 10
        d_87_actual = digits_87[i] if i < len(digits_87) else 0

        marker = " ← ZERO!" if d_87_computed == 0 else ""
        print(f"{i:3} | {d_86:4} | {carry:8} | {val:5} | {d_87_computed:4} | {carry_out:9}{marker}")

        carry = carry_out

        if i > 30:
            print("...")
            break

    # Part E: Which positions have "unprotected 5"?
    print("\n" + "=" * 70)
    print("PART E: Unprotected 5 analysis across zeroless powers")
    print("=" * 70)

    print("\nFor each zeroless 2^n, find positions with 'unprotected 5' (5 followed by <5):")

    for n in zeroless_n:
        digits = get_digits(n)
        unprotected = []
        for i in range(len(digits) - 1):
            if digits[i+1] == 5 and digits[i] < 5:  # digits[i] is to the right of digits[i+1]
                unprotected.append(i+1)  # position of the 5

        if n >= 30:  # Only show later ones
            if unprotected:
                print(f"  n={n}: unprotected 5 at positions {unprotected} (will create zero in 2^{n+1})")
            else:
                print(f"  n={n}: no unprotected 5 (2^{n+1} gets zero from elsewhere)")

    # Part F: What happens to the "admissible suffix set" as we track the orbit?
    print("\n" + "=" * 70)
    print("PART F: Orbit tracking in mod 5^m space")
    print("=" * 70)

    # The last m digits of 2^n are determined by 2^n mod 10^m
    # Since gcd(2, 5) = 1, the relevant structure is 2^n mod 5^m (times the 2-adic part)

    m = 4
    period = 4 * (5 ** (m-1))  # Period of 2^n mod 10^m for n >= m
    print(f"\nFor m = {m} digits, period = {period}")

    # Compute which residues are "safe" (zeroless and no unprotected 5)
    def is_safe_suffix(n_val, m_digits):
        """Check if last m digits of 2^n are safe."""
        suffix = (2 ** n_val) % (10 ** m_digits)
        s = str(suffix).zfill(m_digits)
        if '0' in s:
            return False
        for i in range(len(s) - 1):
            if s[i] == '5' and s[i+1] in '1234':
                return False
        return True

    # Track the orbit
    print(f"\nOrbit of 2^n mod 10^{m} (safe status):")
    for n in range(0, 100):
        suffix = (2 ** n) % (10 ** m)
        safe = is_safe_suffix(n, m)
        zeroless_full = '0' not in str(2**n)

        if n in zeroless_n or n < 20:
            marker = "★ ZEROLESS" if zeroless_full else ""
            print(f"  n={n:3}: suffix={suffix:04d}, safe={safe}, {marker}")

    print("\n" + "=" * 70)
    print("PART G: Summary statistics")
    print("=" * 70)

    # Count how many zeroless n have safe vs unsafe suffixes at various m
    for m in [4, 5, 6]:
        safe_count = sum(1 for n in zeroless_n if is_safe_suffix(n, m))
        print(f"m={m}: {safe_count}/{len(zeroless_n)} zeroless powers have safe last-{m} suffix")

if __name__ == "__main__":
    main()
