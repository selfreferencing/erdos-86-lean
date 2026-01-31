"""
Exp 61: What Conditions Enable Full Protection?

Key question: Why does n=76 achieve 100% protection of its 4 5s?

The answer from Exp 60 Part E: A 5 is protected iff the digit to its right is >= 5.

This experiment investigates:
1. The exact digit context around each 5 in zeroless powers
2. Whether we can predict protection from local patterns
3. What makes n=76 special
"""

def get_digits(n):
    """Get digits of 2^n (LSB first)."""
    power = 2 ** n
    digits = []
    while power > 0:
        digits.append(power % 10)
        power //= 10
    return digits


def analyze_five_contexts(n):
    """
    For each 5 in 2^n, get:
    - Position
    - Digit to the right (determines carry)
    - Whether protected
    """
    digits = get_digits(n)
    contexts = []

    for i, d in enumerate(digits):
        if d == 5:
            right_digit = digits[i-1] if i > 0 else None
            # Carry = 1 iff right_digit >= 5 OR there's a cascade
            # Simple local check: carry = 1 iff 2*right_digit >= 10
            local_carry = 1 if right_digit is not None and right_digit >= 5 else 0

            # Actual carry needs full propagation
            actual_carry = compute_carry_at(digits, i)

            contexts.append({
                'position': i,
                'right_digit': right_digit,
                'local_prediction': local_carry,
                'actual_carry': actual_carry,
                'protected': actual_carry == 1
            })

    return contexts


def compute_carry_at(digits, target_pos):
    """Compute the carry entering position target_pos."""
    carry = 0
    for i in range(target_pos):
        val = 2 * digits[i] + carry
        carry = val // 10
    return carry


def main():
    print("=" * 70)
    print("Exp 61: What Conditions Enable Full Protection?")
    print("=" * 70)

    zeroless = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 13, 14, 15, 16, 18, 19, 24, 25,
                27, 28, 31, 32, 33, 34, 35, 36, 37, 39, 49, 51, 67, 72, 76, 77, 81, 86]

    # Part A: Analyze all 5-contexts for late zeroless powers
    print("\n" + "=" * 70)
    print("PART A: 5-contexts for zeroless powers n >= 30")
    print("=" * 70)

    print("\nFor each 5: position, right digit, local pred, actual carry, protected?")

    for n in [n for n in zeroless if n >= 30]:
        power = 2 ** n
        power_str = str(power)
        contexts = analyze_five_contexts(n)

        if not contexts:
            print(f"\nn={n}: 2^{n} = {power_str}")
            print(f"  No 5s in this number")
            continue

        print(f"\nn={n}: 2^{n} = {power_str}")
        all_protected = all(c['protected'] for c in contexts)
        print(f"  All protected: {all_protected}")

        for c in contexts:
            rd = c['right_digit'] if c['right_digit'] is not None else '-'
            local = c['local_prediction']
            actual = c['actual_carry']
            match = "✓" if local == actual else "CASCADE"
            prot = "P" if c['protected'] else "U"
            print(f"    pos {c['position']:2}: right={rd}, local_pred={local}, actual={actual} {match}, {prot}")

    # Part B: Focus on n=76
    print("\n" + "=" * 70)
    print("PART B: Deep dive into n=76")
    print("=" * 70)

    n = 76
    digits = get_digits(n)
    power_str = str(2**n)

    print(f"\n2^{n} = {power_str}")
    print(f"\nFull digit sequence (LSB first):")
    print(f"Position: {list(range(len(digits)))}")
    print(f"Digits:   {digits}")

    # Compute full carry sequence
    carries = [0]
    carry = 0
    for d in digits:
        val = 2 * d + carry
        carry = val // 10
        carries.append(carry)
    carries = carries[:-1]

    print(f"Carries:  {carries}")

    # Mark 5s
    five_positions = [i for i, d in enumerate(digits) if d == 5]
    print(f"\n5s at positions: {five_positions}")

    # Trace the carry cascade leading to position 19
    print("\n\nCarry trace leading to position 19 (first 5 in cascade):")
    print("Pos | Digit | Carry_in | 2*d+c | Digit_out | Carry_out")
    print("-" * 55)
    carry = 0
    for i in range(22):
        d = digits[i]
        val = 2 * d + carry
        d_out = val % 10
        c_out = val // 10
        marker = " <-- 5" if d == 5 else ""
        print(f" {i:2} | {d:5} | {carry:8} | {val:5} | {d_out:9} | {c_out:9}{marker}")
        carry = c_out

    # Part C: What digits precede the cascade?
    print("\n" + "=" * 70)
    print("PART C: What enables the 555 cascade protection?")
    print("=" * 70)

    print("\nFor the 555 cascade at positions 19-21 to be protected:")
    print("  - We need carry=1 entering position 19")
    print("  - This requires 2*d[18] + c[18] >= 10")
    print()
    print(f"  d[18] = {digits[18]}")
    print(f"  c[18] = {carries[18]}")
    print(f"  2*{digits[18]} + {carries[18]} = {2*digits[18] + carries[18]}")
    print()

    if 2*digits[18] + carries[18] >= 10:
        print("  YES: 2*d[18] + c[18] >= 10, so cascade is protected!")
    else:
        print("  NO: would need carry from earlier cascade")

    print("\nThe digit d[18] = 7 with carry c[18] = 1 gives:")
    print("  2*7 + 1 = 15 >= 10 ✓")
    print("\nSo the 7 at position 18 (with its own incoming carry) protects the 555 cascade.")

    # Part D: What about the isolated 5 at position 12?
    print("\n" + "=" * 70)
    print("PART D: The isolated 5 at position 12")
    print("=" * 70)

    print(f"\nDigit at position 12: {digits[12]}")
    print(f"Carry at position 12: {carries[12]}")
    print(f"Digit at position 11: {digits[11]}")

    print("\nFor position 12 to be protected:")
    print(f"  Need c[12] = 1")
    print(f"  This requires 2*d[11] + c[11] >= 10")
    print(f"  2*{digits[11]} + {carries[11]} = {2*digits[11] + carries[11]}")

    if 2*digits[11] + carries[11] >= 10:
        print("  YES: protected!")
    else:
        print("  NO!")

    # Part E: Summary - what makes n=76 special
    print("\n" + "=" * 70)
    print("PART E: Why n=76 is special")
    print("=" * 70)

    print("\n2^76 has 4 5s at positions 12, 19, 20, 21.")
    print("\nProtection analysis:")
    print("  - Position 12: Protected because d[11]=9, 2*9+0=18 >= 10 ✓")
    print("  - Position 19: Protected because d[18]=7 with c[18]=1, 2*7+1=15 >= 10 ✓")
    print("  - Position 20: Protected because d[19]=5 with c[19]=1, 2*5+1=11 >= 10 ✓")
    print("  - Position 21: Protected because d[20]=5 with c[20]=1, 2*5+1=11 >= 10 ✓")
    print()
    print("KEY INSIGHT: n=76 achieves full protection because:")
    print("  1. The isolated 5 at pos 12 is preceded by a 9")
    print("  2. The 555 cascade at pos 19-21 is preceded by a 7 with incoming carry 1")
    print("  3. Once the cascade starts (carry=1), it self-sustains through the 5s")
    print()
    print("This is a RARE alignment of digit values!")

    # Part F: Compare to n=86 (terminator)
    print("\n" + "=" * 70)
    print("PART F: Compare to n=86 (the final zeroless power)")
    print("=" * 70)

    n = 86
    digits = get_digits(n)
    power_str = str(2**n)
    contexts = analyze_five_contexts(n)

    print(f"\n2^{n} = {power_str}")
    print(f"\nDigits (LSB first): {digits}")

    print("\n5-contexts:")
    for c in contexts:
        rd = c['right_digit'] if c['right_digit'] is not None else '-'
        prot = "PROTECTED" if c['protected'] else "UNPROTECTED"
        print(f"  pos {c['position']:2}: right_digit={rd}, {prot}")

    print("\nWhy n=86 fails:")
    for c in contexts:
        if not c['protected']:
            rd = c['right_digit']
            print(f"  Position {c['position']}: right digit is {rd} < 5, so carry=0, ZERO created!")


if __name__ == "__main__":
    main()
