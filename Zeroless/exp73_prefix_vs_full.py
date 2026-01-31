"""
Exp 73: Prefix Zeroless vs Full Zeroless

Clarify the distinction:
- N_m counts j where 2^{m+j} has zeroless m-digit PREFIX
- The conjecture is about 2^n being FULLY zeroless

Key question: What's the relationship?
- If 2^n is fully zeroless, then all its prefixes are zeroless
- But 2^n can have a zeroless prefix without being fully zeroless

Let's verify the witness values from Exp 72 and check which correspond
to actual zeroless powers.
"""

import math


def get_digits(n):
    """Get digits of 2^n (LSB first)."""
    power = 2 ** n
    digits = []
    while power > 0:
        digits.append(power % 10)
        power //= 10
    return digits


def get_m_digit_prefix(n, m):
    """Get the m most significant digits of 2^n (MSB first)."""
    digits = get_digits(n)
    if len(digits) < m:
        return digits[::-1]
    return digits[-m:][::-1]


def is_zeroless(digits):
    """Check if digit list is zeroless."""
    return 0 not in digits


def main():
    print("=" * 70)
    print("Exp 73: Prefix Zeroless vs Full Zeroless")
    print("=" * 70)

    # Part A: All zeroless powers of 2
    print("\n" + "=" * 70)
    print("PART A: All Zeroless Powers of 2")
    print("=" * 70)

    zeroless_powers = []
    for n in range(200):
        if is_zeroless(get_digits(n)):
            zeroless_powers.append(n)

    print(f"\nZeroless powers: {zeroless_powers}")
    print(f"Count: {len(zeroless_powers)}")
    print(f"Last: n = {max(zeroless_powers)}")

    # Part B: For each zeroless power, what's its digit count m?
    print("\n" + "=" * 70)
    print("PART B: Digit Counts of Zeroless Powers")
    print("=" * 70)

    print("\n  n  | m (digits) | 2^n")
    print("-" * 50)

    for n in zeroless_powers:
        digits = get_digits(n)
        m = len(digits)
        power_str = str(2**n)
        if len(power_str) > 30:
            power_str = power_str[:15] + "..." + power_str[-10:]
        print(f" {n:3} | {m:10} | {power_str}")

    # Part C: Witnesses from Exp 72 - are they full zeroless?
    print("\n" + "=" * 70)
    print("PART C: Exp 72 Witnesses - Full Zeroless Check")
    print("=" * 70)

    print("\nFor each m, check if witness j gives FULLY zeroless 2^{m+j}:")
    print()

    log10_2 = math.log10(2)

    for m in range(25, 40):
        L_m = math.ceil(m / log10_2)

        # Find witnesses (zeroless m-prefix)
        witnesses = []
        for j in range(L_m):
            n = m + j
            prefix = get_m_digit_prefix(n, m)
            if len(prefix) >= m and is_zeroless(prefix):
                witnesses.append(j)

        if witnesses:
            print(f"m={m}: witnesses = {witnesses}")
            for j in witnesses:
                n = m + j
                full_digits = get_digits(n)
                full_zeroless = is_zeroless(full_digits)
                digit_count = len(full_digits)

                status = "FULL ZEROLESS" if full_zeroless else "prefix only"
                print(f"       j={j}, n={n}, {digit_count} digits: {status}")

    # Part D: The key relationship
    print("\n" + "=" * 70)
    print("PART D: Key Relationship")
    print("=" * 70)

    print("""
For 2^n with d digits to be fully zeroless:
  - The d-digit prefix must be zeroless (trivially, it's all digits)
  - All shorter prefixes must also be zeroless

So if 2^n is fully zeroless with d digits:
  - It contributes to N_m for all m = 1, 2, ..., d

But the REVERSE is not true:
  - 2^n can have a zeroless m-digit prefix without being fully zeroless
  - The other (d-m) digits might contain zeros
""")

    # Part E: Verify: do all zeroless powers contribute to N_m?
    print("=" * 70)
    print("PART E: Do All Zeroless Powers Contribute to N_m?")
    print("=" * 70)

    print("\nFor each zeroless 2^n with d digits, check N_m contributions:")
    print()

    for n in zeroless_powers[20:]:  # Focus on larger ones
        d = len(get_digits(n))
        print(f"  n={n}, d={d} digits: contributes to N_m for m=1..{d}")

        # Verify it's a witness for each m
        for m in [d-2, d-1, d]:
            if m < 1:
                continue
            L_m = math.ceil(m / log10_2)
            j = n - m
            if 0 <= j < L_m:
                prefix = get_m_digit_prefix(n, m)
                if is_zeroless(prefix):
                    status = "✓"
                else:
                    status = "✗ (prefix has zero)"
            else:
                status = f"✗ (j={j} not in [0, {L_m}))"
            print(f"    m={m}: j={j}, {status}")

    # Part F: The conjecture structure
    print("\n" + "=" * 70)
    print("PART F: The Conjecture Structure")
    print("=" * 70)

    print("""
The conjecture "2^86 is the last zeroless power" means:

1. For all n > 86, 2^n contains at least one zero digit

2. Equivalently: For n > 86 with d = ⌊n·log₁₀(2)⌋ + 1 digits,
   the d-digit "prefix" (= all digits) has at least one zero

3. This is STRONGER than N_d = 0, because:
   - N_d = 0 means no n in [d, d+L_d) gives zeroless d-prefix
   - But 2^n with n > 86 might have MORE than d digits

The key insight: As n → ∞, both d = ⌊n·log₁₀(2)⌋ + 1 → ∞
and the probability of ANY prefix being zeroless → 0.

The N_m = 0 for m ≥ 36 result is STRONG EVIDENCE that
no large power of 2 can be zeroless, because even the
m-digit prefix fails for m ≥ 36.
""")

    # Part G: The gap analysis
    print("=" * 70)
    print("PART G: Gap Analysis - Why 86 is Special")
    print("=" * 70)

    # 2^86 has 26 digits. Let's check the prefix structure.
    n = 86
    d = len(get_digits(n))
    print(f"\n2^86 has d = {d} digits")
    print(f"2^86 = {2**86}")

    # For 2^86 to be zeroless, it must be a witness for m = 26
    m = d
    L_m = math.ceil(m / log10_2)
    j = n - m

    print(f"\nFor m = {d}: L_m = {L_m}, j = n - m = {j}")
    print(f"j is in [0, L_m) = [0, {L_m})? {0 <= j < L_m}")

    # Check the witness
    prefix = get_m_digit_prefix(n, m)
    print(f"26-digit prefix of 2^86: {''.join(map(str, prefix))}")
    print(f"Zeroless? {is_zeroless(prefix)}")

    print("\n" + "=" * 70)
    print("CONCLUSION")
    print("=" * 70)

    print(f"""
Summary:
1. The last zeroless power is 2^86 (26 digits)
2. N_m = 0 for all m ≥ 36 (prefix test)
3. N_26 > 0 with 2^86 as a witness (j = 60)

The gap between m = 26 (last zeroless power) and m = 36 (first N_m = 0)
arises because:
- For m = 27..35, there exist n values with zeroless m-prefix
- But these n values are NOT fully zeroless (other digits have zeros)
- For m ≥ 36, even the m-prefix fails universally

The proof strategy:
1. Show N_m = 0 for m ≥ M₀ (already verified for M₀ = 36)
2. For m < M₀, exhaustive verification or danger cylinder bounds
""")


if __name__ == "__main__":
    main()
