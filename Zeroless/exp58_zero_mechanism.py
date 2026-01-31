"""
Exp 58: Zero Creation Mechanism Investigation

Key finding from Exp 57: n=31-36 have NO unprotected 5 (digit 5 immediately
followed by digit < 5), yet 2^{n+1}, 2^{n+2}, etc. still get zeros.

Question: What mechanism creates zeros if not the standard "unprotected 5"?

Possible answers:
1. The unprotected 5 detection was wrong
2. There's another mechanism (impossible since 2*d+c=10 requires d=5, c=0)
3. The zero is created at a position that DOESN'T exist in 2^n (MSB growth)

Let's trace exactly what happens for n=31-36.
"""

def get_digits_msb_first(n_val):
    """Get decimal digits as string (MSB first, standard reading order)."""
    return str(2 ** n_val)

def get_digits_lsb_first(n_val):
    """Get decimal digits as list (LSB first)."""
    s = str(2 ** n_val)
    return [int(d) for d in reversed(s)]

def trace_doubling(n):
    """Trace the doubling from 2^n to 2^{n+1} digit by digit."""
    digits_n = get_digits_lsb_first(n)
    digits_n1 = get_digits_lsb_first(n + 1)

    result = {
        'n': n,
        'power_n': 2**n,
        'power_n1': 2**(n+1),
        'len_n': len(digits_n),
        'len_n1': len(digits_n1),
        'zero_positions': [],
        'zero_causes': [],
    }

    carry = 0
    for i in range(len(digits_n1)):
        d_n = digits_n[i] if i < len(digits_n) else 0  # Pad with 0 at MSB
        val = 2 * d_n + carry
        d_out = val % 10
        carry_out = val // 10

        if d_out == 0:
            result['zero_positions'].append(i)
            if d_n == 5 and carry == 0:
                result['zero_causes'].append(f"pos {i}: unprotected 5")
            elif d_n == 0:
                result['zero_causes'].append(f"pos {i}: doubled a 0 (shouldn't happen for zeroless)")
            else:
                result['zero_causes'].append(f"pos {i}: d={d_n}, c={carry}, val={val} ← UNEXPECTED")

        carry = carry_out

    return result

def find_unprotected_5_detailed(n):
    """
    Find all positions where digit 5 has carry-in 0.
    Carry-in at position i depends on all digits to the right (positions 0..i-1).
    """
    digits = get_digits_lsb_first(n)
    unprotected = []

    carry = 0
    for i, d in enumerate(digits):
        if d == 5 and carry == 0:
            unprotected.append(i)
        val = 2 * d + carry
        carry = val // 10

    return unprotected

def main():
    print("=" * 70)
    print("Exp 58: Zero Creation Mechanism Investigation")
    print("=" * 70)

    # Part A: Detailed trace for n=31-36
    print("\n" + "=" * 70)
    print("PART A: Detailed doubling trace for n=31-36")
    print("=" * 70)

    for n in range(31, 37):
        print(f"\n--- n = {n} ---")
        print(f"2^{n} = {2**n}")
        print(f"2^{n+1} = {2**(n+1)}")

        result = trace_doubling(n)
        print(f"Digits: {result['len_n']} → {result['len_n1']}")
        print(f"Zero positions in 2^{n+1}: {result['zero_positions']}")
        print(f"Zero causes: {result['zero_causes']}")

        # Check unprotected 5 with carry tracking
        up5 = find_unprotected_5_detailed(n)
        print(f"Unprotected 5 positions (carry-aware): {up5}")

    # Part B: Check the difference between "followed by <5" and "carry-in = 0"
    print("\n" + "=" * 70)
    print("PART B: Comparing 'followed by <5' vs 'carry-in = 0' definitions")
    print("=" * 70)

    print("\nThe two definitions of 'unprotected 5':")
    print("  DEF1: Digit 5 immediately followed by digit < 5 (local pattern)")
    print("  DEF2: Digit 5 with carry-in = 0 (requires tracing carries)")
    print("\nThese are NOT equivalent when there are cascading carries!")

    for n in [31, 32, 33, 34, 35, 36, 86]:
        digits = get_digits_lsb_first(n)

        # DEF1: local pattern
        def1_positions = []
        for i in range(len(digits) - 1):
            if digits[i+1] == 5 and digits[i] < 5:
                def1_positions.append(i+1)

        # DEF2: carry tracking
        def2_positions = find_unprotected_5_detailed(n)

        print(f"\nn={n}: 2^{n} = {2**n}")
        print(f"  DEF1 (local '5X' with X<5): {def1_positions}")
        print(f"  DEF2 (5 with carry-in=0):   {def2_positions}")
        if def1_positions != def2_positions:
            print("  *** MISMATCH! ***")

    # Part C: For n=31-36, where DO the zeros come from?
    print("\n" + "=" * 70)
    print("PART C: Detailed carry trace for n=32 (example)")
    print("=" * 70)

    n = 32
    print(f"\n2^{n} = {2**n}")
    print(f"2^{n+1} = {2**(n+1)}")

    digits_n = get_digits_lsb_first(n)
    digits_n1 = get_digits_lsb_first(n+1)

    print(f"\nPosition-by-position trace (LSB first):")
    print("Pos | d_n | carry_in | 2*d+c | d_{n+1} | carry_out | Notes")
    print("-" * 70)

    carry = 0
    for i in range(max(len(digits_n), len(digits_n1))):
        d_n = digits_n[i] if i < len(digits_n) else 0
        val = 2 * d_n + carry
        d_out = val % 10
        carry_out = val // 10
        d_actual = digits_n1[i] if i < len(digits_n1) else -1

        notes = ""
        if d_out == 0:
            notes = "← ZERO!"
        elif d_n == 5:
            if carry == 0:
                notes = "(5 unprotected)"
            else:
                notes = "(5 protected)"

        print(f"{i:3} | {d_n:3} | {carry:8} | {val:5} | {d_out:7} | {carry_out:9} | {notes}")
        carry = carry_out

    # Part D: The key insight - MSB position
    print("\n" + "=" * 70)
    print("PART D: MSB growth analysis")
    print("=" * 70)

    print("\nWhen 2^n doubles to 2^{n+1}, sometimes a new digit is added at the MSB.")
    print("If the MSB of 2^n is >= 5, doubling creates a carry that adds a new digit.")
    print("This new position starts with d=0 in the 'virtual extension' of 2^n.")

    for n in range(31, 42):
        digits_n = get_digits_msb_first(n)
        digits_n1 = get_digits_msb_first(n+1)
        msb_n = int(digits_n[0])
        grows = len(digits_n1) > len(digits_n)

        has_zero = '0' in digits_n1
        zero_pos = digits_n1.find('0') if has_zero else -1

        # Check if zero is in the "new" MSB region
        if grows and has_zero:
            old_len = len(digits_n)
            new_len = len(digits_n1)
            zero_in_new_region = zero_pos < (new_len - old_len)
        else:
            zero_in_new_region = False

        print(f"n={n}: MSB={msb_n}, grows={grows}, has_zero={has_zero}, zero_pos={zero_pos}, in_new_region={zero_in_new_region}")
        print(f"       2^{n}   = {digits_n}")
        print(f"       2^{n+1} = {digits_n1}")

    # Part E: Final summary
    print("\n" + "=" * 70)
    print("PART E: Summary of zero-creation mechanisms")
    print("=" * 70)

    print("\nFor each zeroless n, categorize how 2^{n+1} gets its first zero:")

    zeroless = [1, 2, 3, 4, 5, 6, 7, 8, 9, 13, 14, 15, 16, 18, 19, 24, 25, 27, 28,
                31, 32, 33, 34, 35, 36, 37, 39, 49, 51, 67, 72, 76, 77, 81, 86]

    mechanisms = {'unprotected_5': [], 'msb_growth': [], 'other': []}

    for n in zeroless:
        result = trace_doubling(n)
        up5 = find_unprotected_5_detailed(n)

        digits_n = get_digits_msb_first(n)
        digits_n1 = get_digits_msb_first(n+1)
        grows = len(digits_n1) > len(digits_n)

        # Check if zero comes from unprotected 5
        if up5:
            mechanisms['unprotected_5'].append(n)
        elif grows:
            # Zero might come from MSB growth region
            mechanisms['msb_growth'].append(n)
        else:
            mechanisms['other'].append(n)

    print(f"\nUnprotected 5 mechanism: {mechanisms['unprotected_5']}")
    print(f"MSB growth mechanism: {mechanisms['msb_growth']}")
    print(f"Other mechanism: {mechanisms['other']}")

if __name__ == "__main__":
    main()
