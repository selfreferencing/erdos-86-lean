#!/usr/bin/env python3
"""
Computational verification for the 86 Conjecture (Zeroless Powers of 2)
"""

def has_zero(n):
    """Check if 2^n contains digit 0"""
    return '0' in str(2**n)

def automaton_trace(num):
    """
    Run the doubling automaton on num.
    Returns (accepted, rejection_position, final_state, trace)

    The automaton checks: does 2*num contain digit 0?
    - State s0 (carry=0): digit 0 or 5 produces 0 -> REJECT
    - State s1 (carry=1): no rejection possible
    """
    state = 0  # 0 = s0, 1 = s1
    trace = []
    pos = 0

    while num > 0 or state == 1:
        if num == 0 and state == 0:
            break  # Terminated cleanly

        digit = num % 10 if num > 0 else 0
        num //= 10

        if state == 0:
            if digit in (0, 5):
                return (False, pos, state, trace)  # REJECT
            elif digit in (1, 2, 3, 4):
                new_state = 0
            else:  # 6, 7, 8, 9
                new_state = 1
        else:  # state == 1
            if digit in (0, 1, 2, 3, 4):
                new_state = 0
            else:  # 5, 6, 7, 8, 9
                new_state = 1

        trace.append((pos, digit, state, new_state))
        state = new_state
        pos += 1

        if pos > 1000:  # Safety limit
            break

    return (True, -1, state, trace)

def analyze_level_2():
    """Analyze survivors at level 2 (period 20)"""
    print("=" * 60)
    print("LEVEL 2 ANALYSIS (period 20)")
    print("=" * 60)

    survivors = []
    s0_classes = []
    s1_classes = []

    for n in range(1, 21):
        power = 2**n
        last2 = power % 100
        accepted, rej_pos, final_state, trace = automaton_trace(power)

        if accepted:
            survivors.append(n)
            if final_state == 0:
                s0_classes.append(n)
            else:
                s1_classes.append(n)
            status = f"survives, ends s{final_state}"
        else:
            status = f"REJECTED at pos {rej_pos}"

        print(f"n ≡ {n:2d} (mod 20): 2^n ≡ {last2:02d} (mod 100) -> {status}")

    print(f"\nSurvivors: {len(survivors)} classes")
    print(f"  s0: {len(s0_classes)} classes: {s0_classes}")
    print(f"  s1: {len(s1_classes)} classes: {s1_classes}")

    return survivors, s0_classes, s1_classes

def analyze_level_3():
    """Analyze survivors at level 3 (period 100)"""
    print("\n" + "=" * 60)
    print("LEVEL 3 ANALYSIS (period 100)")
    print("=" * 60)

    survivors = []
    s0_classes = []
    s1_classes = []
    rejected_at_pos2 = []

    for n in range(1, 101):
        power = 2**n
        last3 = power % 1000
        accepted, rej_pos, final_state, trace = automaton_trace(power)

        if accepted:
            survivors.append(n)
            if final_state == 0:
                s0_classes.append(n)
            else:
                s1_classes.append(n)
        elif rej_pos == 2:
            rejected_at_pos2.append(n)

    print(f"Survivors: {len(survivors)} classes")
    print(f"  s0: {len(s0_classes)} classes")
    print(f"  s1: {len(s1_classes)} classes")
    print(f"New rejections at position 2: {len(rejected_at_pos2)} classes")
    print(f"  Rejected: {rejected_at_pos2[:10]}..." if len(rejected_at_pos2) > 10 else f"  Rejected: {rejected_at_pos2}")

    return survivors, s0_classes, s1_classes

def analyze_digit_cycling():
    """Verify that digits at position k cycle through {0,2,4,6,8} or {1,3,5,7,9}"""
    print("\n" + "=" * 60)
    print("DIGIT CYCLING ANALYSIS")
    print("=" * 60)

    # For each level-2 survivor, check how digit 2 (position 2) varies across 5 lifts
    level2_survivors = [3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]

    print("\nDigit at position 2 for each level-2 class across 5 lifts:")
    for base in level2_survivors[:8]:  # First 8 for brevity
        digits = []
        for k in range(5):
            n = base + 20 * k
            power = 2**n
            digit2 = (power // 100) % 10
            digits.append(digit2)
        parity = "EVEN" if all(d % 2 == 0 for d in digits) else "ODD"
        print(f"  n ≡ {base:2d} (mod 20): digits = {digits} ({parity})")

def find_zeroless_powers(max_n=200):
    """Find all zeroless powers of 2 up to 2^max_n"""
    print("\n" + "=" * 60)
    print(f"ZEROLESS POWERS OF 2 (n ≤ {max_n})")
    print("=" * 60)

    zeroless = []
    for n in range(1, max_n + 1):
        if not has_zero(n):
            zeroless.append(n)

    print(f"Zeroless powers: {zeroless}")
    print(f"Count: {len(zeroless)}")
    if zeroless:
        print(f"Maximum: n = {max(zeroless)}")

    return zeroless

def analyze_why_zeroless(n_list):
    """Analyze why specific n values have zeroless 2^n"""
    print("\n" + "=" * 60)
    print("WHY THESE POWERS ARE ZEROLESS")
    print("=" * 60)

    for n in n_list[-10:]:  # Last 10 zeroless powers
        power = 2**n
        digits = len(str(power))
        print(f"n = {n:2d}: 2^n = {power} ({digits} digits)")

def verify_recurrence(max_level=6):
    """Verify the survivor recurrence S_{k+1} ≈ (9/2) S_k"""
    print("\n" + "=" * 60)
    print("SURVIVOR RECURRENCE VERIFICATION")
    print("=" * 60)

    for level in range(1, max_level + 1):
        period = 4 * (5 ** (level - 1))
        survivors = 0
        s0_count = 0
        s1_count = 0

        # Check all residue classes
        for n in range(level, period + level):  # n >= level for valid last-level digits
            power = 2**n
            accepted, rej_pos, final_state, trace = automaton_trace(power)

            # Only count if not rejected at positions 0 through level-1
            # Actually, we should check positions 0 to level-1
            if accepted or (rej_pos >= level):
                survivors += 1
                if final_state == 0:
                    s0_count += 1
                else:
                    s1_count += 1

        ratio = survivors / (period) if period > 0 else 0
        print(f"Level {level}: period = {period:6d}, survivors = {survivors:6d}, "
              f"fraction = {ratio:.4f}, s0 = {s0_count}, s1 = {s1_count}")

def verify_recurrence_v2(max_level=6):
    """Verify survivor counts more carefully"""
    print("\n" + "=" * 60)
    print("SURVIVOR COUNT BY LEVEL (v2)")
    print("=" * 60)

    for level in range(1, max_level + 1):
        period = 4 * (5 ** (level - 1))
        survivors = 0
        s0_count = 0
        s1_count = 0

        for n_mod in range(period):
            # Use n = period + n_mod to ensure n >= level
            n = period + n_mod
            power = 2**n

            # Check if rejected at positions 0 through level-1
            accepted, rej_pos, final_state, trace = automaton_trace(power)

            if accepted or rej_pos >= level:
                survivors += 1
                # Determine state after position level-1
                # This requires tracking through the trace
                state_after = 0
                for pos, digit, s_in, s_out in trace:
                    if pos < level:
                        state_after = s_out
                    else:
                        break
                if state_after == 0:
                    s0_count += 1
                else:
                    s1_count += 1

        ratio = survivors / period if period > 0 else 0
        prev_S = None
        if level > 2:
            prev_period = 4 * (5 ** (level - 2))
            prev_S = prev_survivors if 'prev_survivors' in dir() else None

        print(f"Level {level}: period = {period:6d}, S_{level} = {survivors:6d}, "
              f"fraction = {ratio:.4f}, s0 = {s0_count}, s1 = {s1_count}")
        prev_survivors = survivors

def main():
    # Find zeroless powers
    zeroless = find_zeroless_powers(200)

    # Analyze level 2
    survivors2, s0_2, s1_2 = analyze_level_2()

    # Analyze level 3
    survivors3, s0_3, s1_3 = analyze_level_3()

    # Digit cycling
    analyze_digit_cycling()

    # Why zeroless
    analyze_why_zeroless(zeroless)

    # Recurrence
    verify_recurrence_v2(5)

    print("\n" + "=" * 60)
    print("SUMMARY")
    print("=" * 60)
    print(f"Zeroless powers of 2: n ∈ {zeroless}")
    print(f"Maximum zeroless: n = {max(zeroless) if zeroless else 'none'}")
    print(f"Level 2: {len(survivors2)} survivors (s0: {len(s0_2)}, s1: {len(s1_2)})")
    print(f"Level 3: {len(survivors3)} survivors (s0: {len(s0_3)}, s1: {len(s1_3)})")

if __name__ == "__main__":
    main()
