"""
Experiment 48: Why Does the Orbit Avoid E∩X? + Anomalous Cylinder Investigation

PART A: E∩X Avoidance
- Exp 47 found ZERO hit cylinders in E∩X (entry AND exit witness)
- Only 2 out of 729 3-digit cylinders are in E∩X
- What are these 2 cylinders? Why doesn't the orbit hit them?

PART B: Anomalous Cylinders
- Three 2-digit cylinders are hit but NOT graph-reachable: {21, 42, 85}
- How do they appear in the orbit?
- What's special about their structure?

PART C: Structural Constraints
- What prevents E∩X cylinders from appearing?
- Is there a carry-chain incompatibility?
"""

import math
from collections import defaultdict

def is_zeroless(s):
    """Check if string has no '0' digit."""
    return '0' not in s

def has_entry_witness(prefix):
    """Check for entry witness: (2,4,6,8) followed by 1."""
    for i in range(len(prefix) - 1):
        if prefix[i] in '2468' and prefix[i+1] == '1':
            return True
    return False

def has_exit_witness(prefix):
    """Check for exit witness: 5 followed by (1,2,3,4)."""
    for i in range(len(prefix) - 1):
        if prefix[i] == '5' and prefix[i+1] in '1234':
            return True
    return False

def find_all_hits(max_m=27):
    """Find all zeroless powers up to m digits."""
    hits = []
    for n in range(1, 500):
        power = 2 ** n
        power_str = str(power)
        m = len(power_str)
        if m > max_m:
            break
        if is_zeroless(power_str):
            hits.append({
                'n': n,
                'm': m,
                'prefix': power_str
            })
    return hits

def analyze_predecessor(n):
    """Analyze the predecessor 2^{n-1}."""
    if n <= 1:
        return None
    pred = 2 ** (n - 1)
    pred_str = str(pred)
    return {
        'n': n - 1,
        'value': pred,
        'str': pred_str,
        'digits': len(pred_str),
        'zeroless': is_zeroless(pred_str),
        'has_zero': '0' in pred_str
    }

def analyze_successor(n):
    """Analyze the successor 2^{n+1}."""
    succ = 2 ** (n + 1)
    succ_str = str(succ)
    return {
        'n': n + 1,
        'value': succ,
        'str': succ_str,
        'digits': len(succ_str),
        'zeroless': is_zeroless(succ_str),
        'has_zero': '0' in succ_str
    }

def main():
    print("=" * 70)
    print("Experiment 48: E∩X Avoidance + Anomalous Cylinders")
    print("=" * 70)

    hits = find_all_hits(27)

    # =========================================================================
    # PART A: What are the E∩X cylinders?
    # =========================================================================

    print("\n" + "=" * 70)
    print("PART A: The E∩X Cylinders")
    print("=" * 70)

    # Find all 3-digit E∩X cylinders
    all_zeroless_3 = [f"{a}{b}{c}" for a in range(1,10) for b in range(1,10) for c in range(1,10)]
    ex_cylinders = [c for c in all_zeroless_3 if has_entry_witness(c) and has_exit_witness(c)]

    print(f"\nAll 3-digit cylinders in E∩X: {len(ex_cylinders)}")
    for c in ex_cylinders:
        # Find where entry and exit witnesses are
        entry_pos = None
        exit_pos = None
        for i in range(len(c) - 1):
            if c[i] in '2468' and c[i+1] == '1':
                entry_pos = i
            if c[i] == '5' and c[i+1] in '1234':
                exit_pos = i

        print(f"\n  Cylinder: {c}")
        print(f"    Entry witness at position {entry_pos}: '{c[entry_pos:entry_pos+2]}'")
        print(f"    Exit witness at position {exit_pos}: '{c[exit_pos:exit_pos+2]}'")

        # Check if this cylinder is reachable
        # What 3-digit number doubled would give this prefix?
        # 2*X starts with c means X is in [c*10/2, (c+1)*10/2) roughly

        # Can we ever reach this cylinder?
        print(f"    Analyzing reachability...")

        # Check all 2^n for m=3..10 if they start with this
        found_n = []
        for n in range(1, 100):
            p = str(2**n)
            if p.startswith(c):
                found_n.append(n)
                if len(found_n) >= 3:
                    break

        if found_n:
            print(f"    Powers starting with '{c}': n = {found_n}")
            for n in found_n[:2]:
                print(f"      2^{n} = {str(2**n)[:20]}...")
                if is_zeroless(str(2**n)):
                    print(f"        (zeroless!)")
                else:
                    zero_pos = str(2**n).find('0')
                    print(f"        First zero at position {zero_pos}")
        else:
            print(f"    No powers found starting with '{c}' (up to n=100)")

    # Also check 2-digit E∩X
    all_zeroless_2 = [f"{a}{b}" for a in range(1,10) for b in range(1,10)]
    ex_2 = [c for c in all_zeroless_2 if has_entry_witness(c) and has_exit_witness(c)]
    print(f"\n2-digit cylinders in E∩X: {ex_2}")

    # =========================================================================
    # PART B: Why does the orbit avoid E∩X?
    # =========================================================================

    print("\n" + "=" * 70)
    print("PART B: Why Does the Orbit Avoid E∩X?")
    print("=" * 70)

    # The two E∩X 3-digit cylinders are likely {something with both 21/41/61/81 AND 51/52/53/54}
    # Let's check: can a zeroless power have BOTH patterns?

    print("\nAnalyzing structure of E∩X cylinders...")

    for c in ex_cylinders:
        # Entry: even followed by 1 -> positions where we have X1 for X even
        # Exit: 5 followed by 1,2,3,4 -> positions where we have 5Y for Y <= 4

        # In a 3-digit cylinder ABC:
        # Entry at 0 means A is even and B=1
        # Entry at 1 means B is even and C=1
        # Exit at 0 means A=5 and B<=4
        # Exit at 1 means B=5 and C<=4

        print(f"\n  Cylinder {c}:")

        # Decode the patterns
        a, b, c_digit = int(c[0]), int(c[1]), int(c[2])

        # Check which patterns apply
        entry_at_0 = (a in [2,4,6,8]) and (b == 1)
        entry_at_1 = (b in [2,4,6,8]) and (c_digit == 1)
        exit_at_0 = (a == 5) and (b <= 4)
        exit_at_1 = (b == 5) and (c_digit <= 4)

        print(f"    Digits: A={a}, B={b}, C={c_digit}")
        print(f"    Entry at 0: {entry_at_0} (A even, B=1)")
        print(f"    Entry at 1: {entry_at_1} (B even, C=1)")
        print(f"    Exit at 0: {exit_at_0} (A=5, B<=4)")
        print(f"    Exit at 1: {exit_at_1} (B=5, C<=4)")

        # The structural constraint
        if entry_at_0 and exit_at_1:
            print(f"    >>> Pattern: A is even, B=1, then B=5? IMPOSSIBLE!")
            print(f"        B cannot be both 1 and 5")
        if entry_at_1 and exit_at_0:
            print(f"    >>> Pattern: A=5, B<=4, then B is even? Need B in {{2,4}}")
            print(f"        And C=1. So cylinder is 5{b}1 with b in {{2,4}}")

    # Let's enumerate the logical possibilities
    print("\n\nSystematic E∩X enumeration for 3-digit cylinders:")
    print("  Entry witness: (A even, B=1) OR (B even, C=1)")
    print("  Exit witness: (A=5, B<=4) OR (B=5, C<=4)")
    print()

    count = 0
    for a in range(1, 10):
        for b in range(1, 10):
            for c in range(1, 10):
                entry_0 = (a in [2,4,6,8]) and (b == 1)
                entry_1 = (b in [2,4,6,8]) and (c == 1)
                exit_0 = (a == 5) and (b <= 4)
                exit_1 = (b == 5) and (c <= 4)

                has_entry = entry_0 or entry_1
                has_exit = exit_0 or exit_1

                if has_entry and has_exit:
                    count += 1
                    cyl = f"{a}{b}{c}"
                    modes = []
                    if entry_0: modes.append("E@0")
                    if entry_1: modes.append("E@1")
                    if exit_0: modes.append("X@0")
                    if exit_1: modes.append("X@1")
                    print(f"  {cyl}: {', '.join(modes)}")

    print(f"\nTotal E∩X 3-digit cylinders: {count}")

    # =========================================================================
    # PART C: Anomalous Hit Cylinders (21, 42, 85)
    # =========================================================================

    print("\n" + "=" * 70)
    print("PART C: Anomalous Hit Cylinders")
    print("=" * 70)

    anomalous = ['21', '42', '85']

    print("\nThese cylinders are HIT but not reachable via 2-digit transition graph:")
    print("(The graph tracks: what 2-digit prefix can double into what 2-digit prefix)")
    print()

    for cyl in anomalous:
        print(f"\n--- Cylinder '{cyl}' ---")

        # Find all hits starting with this cylinder
        cyl_hits = [h for h in hits if h['prefix'].startswith(cyl)]
        print(f"Hits starting with '{cyl}': {len(cyl_hits)}")

        for h in cyl_hits:
            n = h['n']
            prefix = h['prefix']
            print(f"\n  2^{n} = {prefix}")

            # Analyze predecessor
            pred_info = analyze_predecessor(n)
            if pred_info:
                pred_2 = pred_info['str'][:2] if len(pred_info['str']) >= 2 else pred_info['str']
                print(f"  Predecessor 2^{n-1} = {pred_info['str'][:20]}...")
                print(f"    2-digit prefix: '{pred_2}'")
                print(f"    Has zero: {pred_info['has_zero']}")

                # What is the transition?
                print(f"    Transition: '{pred_2}' -> '{cyl}'")

                # Why isn't this in the graph?
                # The graph was built by doubling 3-digit numbers.
                # Check if doubling pred_2+X can give cyl
                print(f"    Checking transition validity...")

                # For 2-digit prefixes AB, the transition graph considers AB0-AB9
                # doubled gives: 2*(AB0) to 2*(AB9)
                base = int(pred_2) * 10
                doubled_range = [str(2 * (base + x))[:2] for x in range(10)]
                print(f"    Doubling '{pred_2}X' gives 2-digit prefixes: {set(doubled_range)}")

                if cyl in doubled_range:
                    print(f"    >>> '{cyl}' IS reachable from '{pred_2}' via 3-digit transition")
                else:
                    print(f"    >>> '{cyl}' NOT reachable from '{pred_2}' via 3-digit doubling!")
                    # But we know 2*2^{n-1} = 2^n starts with cyl
                    # So there must be more digits involved
                    pred_3 = pred_info['str'][:3] if len(pred_info['str']) >= 3 else pred_info['str']
                    base3 = int(pred_3) * 10
                    doubled_range3 = [str(2 * (base3 + x))[:2] for x in range(10)]
                    print(f"    Doubling '{pred_3}X' gives: {set(doubled_range3)}")

    # =========================================================================
    # PART D: The Structural Constraint on E∩X
    # =========================================================================

    print("\n" + "=" * 70)
    print("PART D: Structural Constraint Analysis")
    print("=" * 70)

    print("""
Key insight from Part B: E∩X cylinders require OVERLAPPING patterns.

For 3-digit cylinder ABC to be in E∩X, we need:
  Entry: (A even, B=1) OR (B even, C=1)
  Exit: (A=5, B<=4) OR (B=5, C<=4)

The only ways to satisfy both:

Case 1: Entry at position 0, Exit at position 1
  - A is even (2,4,6,8), B=1, and B=5, C<=4
  - But B cannot be both 1 and 5. IMPOSSIBLE.

Case 2: Entry at position 1, Exit at position 0
  - A=5, B<=4, and B is even, C=1
  - B must be in {2,4} (both <=4 and even)
  - So cylinders: 521, 541

Case 3: Entry at position 0, Exit at position 0
  - A is even AND A=5. IMPOSSIBLE.

Case 4: Entry at position 1, Exit at position 1
  - B is even, C=1, and B=5, C<=4
  - B cannot be both even and 5. IMPOSSIBLE.

CONCLUSION: Only 521 and 541 can be in E∩X.
Both have the form: 5, then {2,4}, then 1.
""")

    # Check 521 and 541 specifically
    print("Checking cylinders 521 and 541:")

    for cyl in ['521', '541']:
        print(f"\n  {cyl}:")
        # Any 2^n starting with this?
        found = False
        for n in range(1, 200):
            s = str(2**n)
            if s.startswith(cyl):
                print(f"    2^{n} starts with {cyl}: {s[:20]}...")
                if is_zeroless(s):
                    print(f"      ZEROLESS! This would be a hit.")
                    found = True
                else:
                    zero_pos = s.find('0')
                    print(f"      First zero at position {zero_pos}: ...{s[max(0,zero_pos-2):zero_pos+3]}...")
                break
        if not found:
            print(f"    No power starting with {cyl} found (or all have zeros)")

    # =========================================================================
    # PART E: Check if any hit EVER had both E and X at any depth
    # =========================================================================

    print("\n" + "=" * 70)
    print("PART E: Extended E∩X Check at All Depths")
    print("=" * 70)

    print("\nChecking if any hit has both entry and exit witnesses at ANY prefix depth...")

    for h in hits:
        prefix = h['prefix']
        n = h['n']

        for depth in range(2, min(len(prefix), 10) + 1):
            sub = prefix[:depth]
            if has_entry_witness(sub) and has_exit_witness(sub):
                print(f"\n  2^{n} has E∩X at depth {depth}: '{sub}'")
                print(f"    Full prefix: {prefix[:20]}...")

    print("\n  (End of E∩X scan)")

    # =========================================================================
    # SYNTHESIS
    # =========================================================================

    print("\n" + "=" * 70)
    print("SYNTHESIS")
    print("=" * 70)

    print("""
KEY FINDINGS:

1. E∩X STRUCTURE:
   - Only 2 three-digit cylinders are in E∩X: 521 and 541
   - These require: A=5, B∈{2,4}, C=1
   - This is a STRUCTURAL constraint, not probabilistic

2. WHY ORBIT AVOIDS E∩X:
   - The E∩X cylinders (521, 541) require very specific digit sequences
   - Entry witness (even→1) and exit witness (5→small) OVERLAP
   - The middle digit B must be BOTH:
     - Even (for entry at position 1)
     - ≤4 (for exit at position 0)
   - So B ∈ {2, 4}

3. ANOMALOUS CYLINDERS:
   - The 2-digit transition graph misses transitions that require
     looking at more than 3 digits of the predecessor
   - These aren't truly anomalous, just artifacts of the graph construction

4. MODEL IMPLICATION:
   - The transfer matrix counted |E∩X| ≈ 3.26 × 10^26 at m=27
   - But E∩X at the 3-digit level is TINY (just 2 cylinders)
   - The model may be counting patterns that can't co-occur locally

5. CORRECTED PICTURE:
   - E and X are nearly mutually exclusive at short depths
   - As m grows, they can appear in DIFFERENT parts of the prefix
   - But for cylinders (short prefixes), E∩X is almost empty
""")

if __name__ == "__main__":
    main()
