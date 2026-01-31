"""
Experiment 54: GPT 22B's Boundary Parity Test

GPT 22B claims:
1. The 2 inverse branches correspond to the boundary carry c_top ∈ {0,1}
2. c_top is determined by d_{m+1} mod 2 (parity of digit above window)
3. Conditioning on X (zeroless) biases this parity distribution
4. If P(zero-branch parity | X) ≈ 1/3, this explains the gap

This experiment tests:
1. For each hit at depth m, record d_{m+1}
2. Compute which parity gives the "zero-predecessor branch"
3. Check if parity distribution is ~2:1 skewed
"""

import math

def is_zeroless(s):
    return '0' not in s

def has_entry_witness(prefix):
    """Entry witness: even followed by 1."""
    for i in range(len(prefix) - 1):
        if prefix[i] in '2468' and prefix[i+1] == '1':
            return True
    return False

def compute_inverse_with_carry(prefix, c_top):
    """
    Compute the predecessor prefix given boundary carry c_top.

    The inverse of doubling: 2*pred = current
    So pred = current / 2, with carries propagating.

    For digit d_out with incoming carry c_in:
        2*d_in + c_in = d_out + 10*c_out

    The key insight from GPT 22B:
        c_in ≡ d_out (mod 2)

    So internal carries are forced by parities.
    Only c_top (the carry exiting the top) is free.

    Returns the predecessor prefix (or None if invalid).
    """
    n = len(prefix)
    pred_digits = []

    # Process from top to bottom
    # c_top is the carry-out from the topmost digit
    carry_out = c_top

    for i in range(n):
        d_out = int(prefix[i])

        # From 2*d_in + c_in = d_out + 10*c_out
        # We know c_in ≡ d_out (mod 2)
        # And c_out is what we're tracking

        # The digit below will have c_in = c_out from this digit
        # So: 2*d_in + c_out_prev = d_out + 10*c_out_current

        # Actually, let's think more carefully.
        # When doubling, we process right to left.
        # For inverse, we process left to right with the boundary carry.

        # If the output is d_out with carry_out going up,
        # then 2*d_in + carry_in = d_out + 10*carry_out
        # where carry_in comes from the digit to the right.

        # For the leftmost digit, carry_out = c_top (given).
        # Then d_in = (d_out + 10*carry_out - carry_in) / 2

        # But we don't know carry_in yet (it comes from below).
        # This is the tricky part.

        pass

    # Actually, let me use a simpler approach:
    # Just compute 2^{n-1} directly and check if it has zeros
    return None

def find_all_hits(max_n=100):
    """Find all zeroless powers up to n."""
    hits = []
    for n in range(1, max_n + 1):
        power = 2 ** n
        power_str = str(power)
        if is_zeroless(power_str):
            hits.append({
                'n': n,
                'm': len(power_str),
                'value': power,
                'str': power_str
            })
    return hits

def main():
    print("=" * 70)
    print("Experiment 54: GPT 22B's Boundary Parity Test")
    print("=" * 70)

    hits = find_all_hits(100)

    # =========================================================================
    # PART A: Basic parity distribution in hits
    # =========================================================================

    print("\n" + "=" * 70)
    print("PART A: Parity of d_{m+1} in Zeroless Hits")
    print("=" * 70)

    print("""
For each m-digit hit, we look at the (m+1)-digit prefix.
d_{m+1} is the digit at position m (0-indexed), i.e., the first digit
beyond the m-digit window.

GPT 22B claims: d_{m+1} mod 2 determines the boundary carry,
and this should be biased ~2:1 on zeroless prefixes.
""")

    # For each hit, record d_{m+1} parity
    parity_counts = {0: 0, 1: 0}
    parity_by_m = {}

    for h in hits:
        n = h['n']
        m = h['m']
        s = h['str']

        # d_{m+1} is at position m (if the number is long enough)
        # But wait - the hit IS an m-digit number, so there's no d_{m+1}
        # unless we look at the full power.

        # Actually, for an m-digit zeroless power, m = len(str(2^n)).
        # The "window" is the full number, so there's no d_{m+1}.

        # I think GPT means: for a FIXED window depth m, look at numbers
        # that are LONGER than m digits, and see what's beyond the window.
        pass

    # Let me reconsider. GPT 22B is talking about:
    # - A fixed depth m window
    # - The digit d_{m+1} above this window
    # - How the parity of d_{m+1} biases the branch

    # For zeroless 2^n with len(2^n) > m, we can look at the m-digit prefix
    # and the (m+1)th digit.

    print("\n--- Fixed window analysis ---")

    for window_m in [3, 4, 5, 6]:
        print(f"\n  Window depth m = {window_m}:")

        even_d = 0
        odd_d = 0

        for n in range(1, 100):
            power_str = str(2**n)
            if len(power_str) > window_m and is_zeroless(power_str):
                # The m-digit prefix is zeroless
                prefix = power_str[:window_m]
                if is_zeroless(prefix):
                    d_next = int(power_str[window_m])
                    if d_next % 2 == 0:
                        even_d += 1
                    else:
                        odd_d += 1

        total = even_d + odd_d
        if total > 0:
            print(f"    Even d_{{m+1}}: {even_d} ({even_d/total:.1%})")
            print(f"    Odd d_{{m+1}}: {odd_d} ({odd_d/total:.1%})")
            print(f"    Ratio: {max(even_d,odd_d)/min(even_d,odd_d):.2f}:1" if min(even_d,odd_d) > 0 else "    Ratio: N/A")

    # =========================================================================
    # PART B: Parity and predecessor zeros
    # =========================================================================

    print("\n" + "=" * 70)
    print("PART B: Parity vs Predecessor Zero")
    print("=" * 70)

    print("""
For each zeroless hit 2^n, check:
1. Does 2^{n-1} have a zero? (predecessor zero)
2. What's the parity of d_{m+1} in the prefix?

GPT 22B predicts: one parity should correlate with "predecessor has zero".
""")

    for window_m in [3, 4, 5]:
        print(f"\n  Window depth m = {window_m}:")

        # (parity, pred_has_zero) counts
        counts = {
            (0, True): 0, (0, False): 0,
            (1, True): 0, (1, False): 0
        }

        for n in range(2, 100):  # Start at 2 so we have a predecessor
            power_str = str(2**n)
            pred_str = str(2**(n-1))

            if len(power_str) > window_m:
                prefix = power_str[:window_m]
                if is_zeroless(prefix):
                    d_next = int(power_str[window_m])
                    parity = d_next % 2

                    # Does predecessor have zero in its first window_m digits?
                    pred_prefix = pred_str[:window_m] if len(pred_str) >= window_m else pred_str
                    pred_has_zero = '0' in pred_prefix

                    counts[(parity, pred_has_zero)] += 1

        # Display
        total = sum(counts.values())
        print(f"    Total cases: {total}")

        even_pred_zero = counts[(0, True)]
        even_pred_ok = counts[(0, False)]
        odd_pred_zero = counts[(1, True)]
        odd_pred_ok = counts[(1, False)]

        print(f"\n    Even d_{{m+1}}:")
        print(f"      Pred has zero: {even_pred_zero}")
        print(f"      Pred zeroless: {even_pred_ok}")
        if even_pred_zero + even_pred_ok > 0:
            print(f"      P(pred zero | even): {even_pred_zero/(even_pred_zero+even_pred_ok):.2%}")

        print(f"\n    Odd d_{{m+1}}:")
        print(f"      Pred has zero: {odd_pred_zero}")
        print(f"      Pred zeroless: {odd_pred_ok}")
        if odd_pred_zero + odd_pred_ok > 0:
            print(f"      P(pred zero | odd): {odd_pred_zero/(odd_pred_zero+odd_pred_ok):.2%}")

        # The key ratio for GPT's claim
        if odd_pred_zero + even_pred_zero > 0:
            print(f"\n    >>> P(pred has zero | zeroless prefix) = {(even_pred_zero + odd_pred_zero)/total:.2%}")

    # =========================================================================
    # PART C: Entry witness correlation with parity
    # =========================================================================

    print("\n" + "=" * 70)
    print("PART C: Entry Witness vs Boundary Parity")
    print("=" * 70)

    print("""
For zeroless hits, check if entry witness (even→1 pattern) correlates
with the parity of d_{m+1}.

If GPT 22B is right, entry witness should correlate with the
"rare parity" (~1/3 of cases).
""")

    for window_m in [4, 5, 6]:
        print(f"\n  Window depth m = {window_m}:")

        # (parity, has_entry) counts
        counts = {
            (0, True): 0, (0, False): 0,
            (1, True): 0, (1, False): 0
        }

        for n in range(2, 100):
            power_str = str(2**n)

            if len(power_str) > window_m:
                prefix = power_str[:window_m]
                if is_zeroless(prefix):
                    d_next = int(power_str[window_m])
                    parity = d_next % 2
                    has_entry = has_entry_witness(prefix)
                    counts[(parity, has_entry)] += 1

        total = sum(counts.values())

        even_entry = counts[(0, True)]
        even_no = counts[(0, False)]
        odd_entry = counts[(1, True)]
        odd_no = counts[(1, False)]

        print(f"    Even d_{{m+1}}: {even_entry} with entry, {even_no} without")
        print(f"    Odd d_{{m+1}}: {odd_entry} with entry, {odd_no} without")

        total_entry = even_entry + odd_entry
        if total_entry > 0:
            print(f"\n    Among entries:")
            print(f"      Even parity: {even_entry}/{total_entry} = {even_entry/total_entry:.1%}")
            print(f"      Odd parity: {odd_entry}/{total_entry} = {odd_entry/total_entry:.1%}")

    # =========================================================================
    # PART D: Direct test of GPT's claim
    # =========================================================================

    print("\n" + "=" * 70)
    print("PART D: GPT 22B's Specific Claim")
    print("=" * 70)

    print("""
GPT 22B claims:
- The boundary carry c_top = d_{m+1} mod 2
- On zeroless cylinders, P(c_top = zero-branch) ≈ 1/3
- This explains the ~3× gap

Testing: Is there a ~2:1 skew in d_{m+1} parity on zeroless prefixes?
""")

    for window_m in range(3, 10):
        even_count = 0
        odd_count = 0

        for n in range(1, 300):
            power_str = str(2**n)
            if len(power_str) > window_m:
                prefix = power_str[:window_m]
                if is_zeroless(prefix):
                    d_next = int(power_str[window_m])
                    if d_next % 2 == 0:
                        even_count += 1
                    else:
                        odd_count += 1

        total = even_count + odd_count
        if total > 10:
            ratio = max(even_count, odd_count) / min(even_count, odd_count) if min(even_count, odd_count) > 0 else float('inf')
            minority = min(even_count, odd_count)
            minority_pct = minority / total * 100
            print(f"  m={window_m}: even={even_count}, odd={odd_count}, ratio={ratio:.2f}:1, minority={minority_pct:.1f}%")

    # =========================================================================
    # SYNTHESIS
    # =========================================================================

    print("\n" + "=" * 70)
    print("SYNTHESIS")
    print("=" * 70)

    print("""
GPT 22B's claim requires:
1. d_{m+1} parity should be ~2:1 skewed on zeroless prefixes
2. The minority parity should be ~33% (matching the ~3× gap)

Results above show whether this holds.

If the parity distribution is close to 50/50, GPT's mechanism
doesn't explain the gap, and our arithmetic constraint finding
(Exp 52-53) remains the primary explanation.
""")

if __name__ == "__main__":
    main()
