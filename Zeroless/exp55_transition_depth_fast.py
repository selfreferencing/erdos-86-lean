"""
Experiment 55 (Fast): Find the Transition Depth for E∩X Reachability

Faster version that samples E∩X cylinders rather than exhaustive check.
"""

from itertools import product
import random

def is_zeroless(s):
    return '0' not in s

def has_entry_witness(prefix):
    for i in range(len(prefix) - 1):
        if prefix[i] in '2468' and prefix[i+1] == '1':
            return True
    return False

def has_exit_witness(prefix):
    for i in range(len(prefix) - 1):
        if prefix[i] == '5' and prefix[i+1] in '1234':
            return True
    return False

def has_zeroless_predecessor(target, max_extra_digits=3):
    """
    Check if there exists a zeroless N such that 2*N starts with target.
    """
    target_int = int(target)

    for extra in range(max_extra_digits + 1):
        scale = 10 ** extra
        lower = (target_int * scale + 1) // 2
        upper = ((target_int + 1) * scale) // 2

        for n in range(lower, min(upper + 1, lower + 100)):  # Limit search
            n_str = str(n)
            if is_zeroless(n_str):
                doubled = str(2 * n)
                if doubled.startswith(target):
                    return True, n

    return False, None

def floor_half_has_zero(cyl):
    """Check if floor(cyl/2) contains a zero."""
    cyl_int = int(cyl)
    half = cyl_int // 2
    return '0' in str(half)

def main():
    print("=" * 70)
    print("Experiment 55 (Fast): Transition Depth for E∩X Reachability")
    print("=" * 70)

    print("""
Testing depths 3-11 to find where E∩X first becomes arithmetically possible.
Using floor(w/2) contains zero as the primary test.
""")

    for depth in range(3, 12):
        print(f"\n--- Depth {depth} ---")

        # Generate E∩X cylinders
        ex_cylinders = []
        for digits in product(range(1, 10), repeat=depth):
            cyl = ''.join(str(d) for d in digits)
            if has_entry_witness(cyl) and has_exit_witness(cyl):
                ex_cylinders.append(cyl)

        total = len(ex_cylinders)
        print(f"  Total E∩X cylinders: {total}")

        if total == 0:
            continue

        # Check floor(w/2) has zero for all
        zero_in_half = sum(1 for cyl in ex_cylinders if floor_half_has_zero(cyl))
        print(f"  floor(w/2) has zero: {zero_in_half}/{total} ({100*zero_in_half/total:.1f}%)")

        # If not all have zero in floor(w/2), check for actual reachability
        if zero_in_half < total:
            non_zero_half = [cyl for cyl in ex_cylinders if not floor_half_has_zero(cyl)]
            print(f"  Checking {len(non_zero_half)} cylinders with zeroless floor(w/2)...")

            reachable_examples = []
            for cyl in non_zero_half[:50]:  # Sample up to 50
                has_pred, pred = has_zeroless_predecessor(cyl, max_extra_digits=2)
                if has_pred:
                    reachable_examples.append((cyl, pred))

            if reachable_examples:
                print(f"  FOUND REACHABLE E∩X CYLINDERS!")
                for cyl, pred in reachable_examples[:5]:
                    print(f"    {cyl} <- 2*{pred} = {2*pred}")
                print(f"\n  >>> TRANSITION DEPTH: m = {depth}")
                break
            else:
                print(f"  None found in sample (all blocked despite zeroless floor)")

        else:
            print(f"  All blocked by floor(w/2) containing zero")

    # Additional analysis: why does floor(w/2) always have zero?
    print("\n" + "=" * 70)
    print("ANALYSIS: Why floor(w/2) Contains Zero for All E∩X")
    print("=" * 70)

    print("""
For E∩X at depth m ≤ 5:
- E∩X requires entry witness (even→1) AND exit witness (5→small)
- These patterns overlap or are adjacent

Consider the structure:
- Exit at position i means digit i is 5, digit i+1 is small (1-4)
- Entry at position j means digit j is even (2,4,6,8), digit j+1 is 1

When i and j are close (gap < 3), this forces specific digit sequences.

The key observation: When w starts with 5X where X is even,
then w/2 starts with 2X' where X' often contains 0.

Specifically:
- 52X/2 = 26X/2 → digits 260, 261, 262, etc.
- 54X/2 = 27X/2 → digits 270, 271, 272, etc.

The middle digit is often 0 because of how division by 2 propagates.
""")

    # Detailed pattern analysis
    print("\n" + "=" * 70)
    print("PATTERN: E∩X Cylinder Structure")
    print("=" * 70)

    for depth in [3, 4, 5]:
        print(f"\n--- Depth {depth} ---")

        patterns = {}
        for digits in product(range(1, 10), repeat=depth):
            cyl = ''.join(str(d) for d in digits)
            if not (has_entry_witness(cyl) and has_exit_witness(cyl)):
                continue

            # First two digits
            first_two = cyl[:2]
            half = int(cyl) // 2
            half_str = str(half)

            if first_two not in patterns:
                patterns[first_two] = {'count': 0, 'zero_in_half': 0}
            patterns[first_two]['count'] += 1
            if '0' in half_str:
                patterns[first_two]['zero_in_half'] += 1

        print(f"  First 2 digits → zero in half:")
        for prefix in sorted(patterns.keys()):
            p = patterns[prefix]
            pct = 100 * p['zero_in_half'] / p['count']
            print(f"    {prefix}: {p['zero_in_half']}/{p['count']} ({pct:.0f}%)")

if __name__ == "__main__":
    main()
