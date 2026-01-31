"""
Exp 74: The Prefix-Only Witnesses

For m = 27..35, there are witnesses that have zeroless m-digit prefixes
but are NOT fully zeroless. These are:
- 2^111 (34 digits): witnesses for m = 27,28,29,30
- 2^117 (36 digits): witnesses for m = 28,29,30
- 2^122 (37 digits): witnesses for m = 29,30,31,32,33,34,35

Questions:
1. Where are the zeros in these numbers?
2. Why do the prefixes stay zeroless while other digits have zeros?
3. Is there a structural pattern?
"""


def get_digits(n):
    """Get digits of 2^n (LSB first)."""
    power = 2 ** n
    digits = []
    while power > 0:
        digits.append(power % 10)
        power //= 10
    return digits


def main():
    print("=" * 70)
    print("Exp 74: The Prefix-Only Witnesses")
    print("=" * 70)

    # Key prefix-only witnesses
    witnesses = [111, 117, 122, 130]

    for n in witnesses:
        digits = get_digits(n)
        d = len(digits)
        power_str = str(2**n)

        print(f"\n{'='*70}")
        print(f"2^{n} = {power_str}")
        print(f"{'='*70}")
        print(f"Digit count: {d}")

        # Find zeros
        zero_positions = [i for i, dig in enumerate(digits) if dig == 0]
        zero_positions_msb = [d - 1 - i for i in zero_positions]  # MSB-first indexing

        print(f"\nZero positions (LSB-first): {zero_positions}")
        print(f"Zero positions (MSB-first): {zero_positions_msb}")

        # Show the digit string with zeros highlighted
        digit_str_msb = power_str
        print(f"\nDigit string (MSB first):")
        print(f"  Position: ", end="")
        for i in range(d):
            print(f"{i%10}", end="")
        print()
        print(f"  Digit:    {digit_str_msb}")
        print(f"  Zeros:    ", end="")
        for i in range(d):
            if digit_str_msb[i] == '0':
                print("^", end="")
            else:
                print(" ", end="")
        print()

        # For each m this is a witness for
        print(f"\nPrefix analysis:")
        for m in range(max(1, d-10), d+1):
            prefix = digit_str_msb[:m]
            has_zero = '0' in prefix
            suffix = digit_str_msb[m:] if m < d else ""
            suffix_zeros = suffix.count('0')
            status = "HAS ZERO" if has_zero else f"ZEROLESS (but {suffix_zeros} zeros in remaining {d-m} digits)"
            print(f"  m={m:2}: prefix={''.join(prefix[:10])}{'...' if m>10 else ''} | {status}")

    # Part B: The pattern
    print("\n" + "=" * 70)
    print("PART B: Pattern Analysis")
    print("=" * 70)

    print("\nKey observation: The zeros tend to be in the SUFFIX (low-order digits)")
    print("while the PREFIX (high-order digits) stays zeroless longer.")
    print()
    print("This makes sense because:")
    print("  - High-order digits change slowly (every ~3.32 powers)")
    print("  - Low-order digits change rapidly")
    print("  - Zeros appearing in low-order digits don't affect high-order prefix")

    # Part C: Where do zeros first appear in the digit string?
    print("\n" + "=" * 70)
    print("PART C: First Zero Position Distribution")
    print("=" * 70)

    print("\nFor powers 2^n with n > 86, find the FIRST zero (MSB-first):")
    print()

    first_zero_dist = {}
    for n in range(87, 200):
        digits = get_digits(n)
        d = len(digits)
        power_str = str(2**n)

        # Find first zero from MSB
        first_zero = None
        for i, c in enumerate(power_str):
            if c == '0':
                first_zero = i
                break

        if first_zero is not None:
            # Normalize to fraction of digit count
            frac = first_zero / d
            bucket = int(frac * 10) / 10  # Round to 0.1
            first_zero_dist[bucket] = first_zero_dist.get(bucket, 0) + 1

    print("  Fraction from MSB | Count")
    print("-" * 35)
    for bucket in sorted(first_zero_dist.keys()):
        count = first_zero_dist[bucket]
        bar = "*" * count
        print(f"  {bucket:.1f} - {bucket+0.1:.1f}         | {count:3} {bar}")

    # Part D: Why does the prefix stay clean?
    print("\n" + "=" * 70)
    print("PART D: Why Does the Prefix Stay Clean?")
    print("=" * 70)

    print("""
The prefix of 2^n changes slowly:
- The m most significant digits of 2^n are approximately 2^n / 10^{d-m}
- This only changes when 2^n crosses a power-of-10 boundary

For the prefix to gain a zero:
- A new digit must be introduced (rare, every ~3.32 powers)
- Or an existing digit must become 0 (requires specific carry pattern)

For 2^111, 2^117, 2^122:
- Their prefixes happen to be zeroless "by chance"
- But their suffixes (which change more rapidly) contain zeros
- This is why they're "prefix-only" witnesses
""")

    # Part E: Conclusion
    print("=" * 70)
    print("CONCLUSION")
    print("=" * 70)

    print("""
The prefix-only witnesses (m = 27..35) arise because:

1. High-order digits change slowly, low-order digits change rapidly
2. A power can have a zeroless prefix while having zeros elsewhere
3. For m = 27..35, specific n values (111, 117, 122, 130) have this property

For the proof:
- N_m = 0 for m ≥ 36 means NO n gives a zeroless 36+ digit prefix
- This is SUFFICIENT to prove no fully zeroless powers exist for large n
- Because any fully zeroless power would need ALL prefixes zeroless

The critical threshold is m = 36, not m = 27.
For m ≥ 36, the prefix condition fails universally.
""")


if __name__ == "__main__":
    main()
