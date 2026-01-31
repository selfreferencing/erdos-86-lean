"""
Experiment 56: Formalize the Forced-Zero Lemma

GPT 23A proposed a "Forced-Zero Lemma":

> If a cylinder w forces all predecessors to have a zero in a fixed digit
> position, then w is arithmetically unreachable.

Specifically, for cylinder w:
- Preimage interval I(w,k) = [w·10^k/2, (w+1)·10^k/2)
- If for all k≥0, every integer in I(w,k) shares a common prefix containing 0,
  then w has no zeroless predecessors.

This experiment:
1. Characterizes the "forced prefix" for each E∩X cylinder
2. Identifies the pattern: why do all E∩X cylinders force zero-containing predecessors?
3. Formalizes the lemma with explicit conditions
"""

from itertools import product
import math

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

def get_forced_prefix(target, num_digits=4):
    """
    For cylinder 'target', compute the forced prefix of all predecessors.

    Returns the common leading digits of all integers in I(target, k) for various k.
    """
    target_int = int(target)

    # I(target, 0) = [target/2, (target+1)/2)
    # The integers in this range have a specific leading structure

    lower = target_int / 2
    upper = (target_int + 1) / 2

    # The forced prefix is the common leading digits of lower and upper
    lower_str = f"{lower:.10f}".replace('.', '')[:num_digits + 5]
    upper_str = f"{upper:.10f}".replace('.', '')[:num_digits + 5]

    # Find common prefix
    common = []
    for i in range(min(len(lower_str), len(upper_str))):
        if lower_str[i] == upper_str[i]:
            common.append(lower_str[i])
        else:
            break

    return ''.join(common)

def analyze_forced_zero(target):
    """
    Analyze why a cylinder 'target' has only zero-containing predecessors.

    Returns explanation of the forced-zero mechanism.
    """
    target_int = int(target)

    # Half of target gives the predecessor range
    half_lower = target_int / 2
    half_upper = (target_int + 1) / 2

    # For different scales
    explanations = []

    for scale in range(5):
        k = 10 ** scale
        lower = int(math.ceil(half_lower * k))
        upper = int(math.floor(half_upper * k))

        if lower > upper:
            continue

        # Get the range of integers
        integers_in_range = list(range(lower, upper + 1))

        if not integers_in_range:
            continue

        # Check common prefix
        int_strs = [str(n) for n in integers_in_range]
        min_len = min(len(s) for s in int_strs)

        common_prefix = ""
        for i in range(min_len):
            chars = set(s[i] for s in int_strs)
            if len(chars) == 1:
                common_prefix += int_strs[0][i]
            else:
                break

        # Check if common prefix contains zero
        has_zero = '0' in common_prefix

        explanations.append({
            'scale': scale,
            'range': (lower, upper),
            'count': len(integers_in_range),
            'common_prefix': common_prefix,
            'has_zero': has_zero,
            'examples': int_strs[:5]
        })

    return explanations

def find_entry_exit_positions(cyl):
    """Find positions of entry and exit witnesses."""
    entry_pos = []
    exit_pos = []

    for i in range(len(cyl) - 1):
        if cyl[i] in '2468' and cyl[i+1] == '1':
            entry_pos.append(i)
        if cyl[i] == '5' and cyl[i+1] in '1234':
            exit_pos.append(i)

    return entry_pos, exit_pos

def main():
    print("=" * 70)
    print("Experiment 56: Formalize the Forced-Zero Lemma")
    print("=" * 70)

    # =========================================================================
    # PART A: Analyze depth-3 E∩X cylinders (521, 541)
    # =========================================================================

    print("\n" + "=" * 70)
    print("PART A: Depth-3 E∩X Cylinder Analysis")
    print("=" * 70)

    for cyl in ['521', '541']:
        print(f"\n--- Cylinder {cyl} ---")

        e_pos, x_pos = find_entry_exit_positions(cyl)
        print(f"  Entry witness positions: {e_pos}")
        print(f"  Exit witness positions: {x_pos}")

        explanations = analyze_forced_zero(cyl)

        for exp in explanations[:3]:
            print(f"\n  Scale 10^{exp['scale']}:")
            print(f"    Range: [{exp['range'][0]}, {exp['range'][1]}]")
            print(f"    Count: {exp['count']} integers")
            print(f"    Common prefix: '{exp['common_prefix']}'")
            print(f"    Has zero: {exp['has_zero']}")
            print(f"    Examples: {exp['examples']}")

    # =========================================================================
    # PART B: Pattern identification for depth-4 E∩X cylinders
    # =========================================================================

    print("\n" + "=" * 70)
    print("PART B: Depth-4 E∩X Pattern Analysis")
    print("=" * 70)

    # Enumerate all depth-4 E∩X cylinders
    ex_4 = []
    for d in product(range(1, 10), repeat=4):
        cyl = ''.join(str(x) for x in d)
        if has_entry_witness(cyl) and has_exit_witness(cyl):
            ex_4.append(cyl)

    print(f"\nTotal depth-4 E∩X cylinders: {len(ex_4)}")

    # Analyze patterns
    patterns = {}
    for cyl in ex_4:
        e_pos, x_pos = find_entry_exit_positions(cyl)
        pattern = (tuple(e_pos), tuple(x_pos))
        if pattern not in patterns:
            patterns[pattern] = []
        patterns[pattern].append(cyl)

    print(f"\nUnique (E_pos, X_pos) patterns: {len(patterns)}")

    for pattern, cyls in sorted(patterns.items()):
        print(f"\n  Pattern E@{pattern[0]}, X@{pattern[1]}: {len(cyls)} cylinders")
        print(f"    Examples: {cyls[:5]}")

        # Analyze forced-zero for first example
        exp = analyze_forced_zero(cyls[0])
        if exp:
            e = exp[0]
            print(f"    Forced prefix: '{e['common_prefix']}' (has zero: {e['has_zero']})")

    # =========================================================================
    # PART C: The Forced-Zero Lemma
    # =========================================================================

    print("\n" + "=" * 70)
    print("PART C: The Forced-Zero Lemma")
    print("=" * 70)

    print("""
FORCED-ZERO LEMMA (Informal):

Let w be an m-digit cylinder (a prefix constraint).
Define the preimage interval:
    I(w, k) = [w·10^k / 2, (w+1)·10^k / 2)

If for every k ≥ 0, all integers in I(w, k) share a common prefix
that contains the digit 0, then w has no zeroless predecessors.

PROOF SKETCH:
- To reach w by doubling, need N such that 2N starts with w
- 2N ∈ [w·10^k, (w+1)·10^k) iff N ∈ I(w, k)
- If every N in I(w, k) has a zero in its first j digits, then N is not zeroless
- Hence w is unreachable from the zeroless subshift
""")

    # =========================================================================
    # PART D: Characterize the E∩X forced-zero pattern
    # =========================================================================

    print("\n" + "=" * 70)
    print("PART D: E∩X Forced-Zero Pattern")
    print("=" * 70)

    print("""
OBSERVATION from depth-3 analysis:

For w = 521:
  - w/2 = 260.5, so predecessors are in [260.5, 261)
  - At scale k, predecessors are 260X, 2605X, 26050X, etc.
  - The prefix "260" always contains a zero

For w = 541:
  - w/2 = 270.5, so predecessors are in [270.5, 271)
  - At scale k, predecessors are 270X, 2705X, 27050X, etc.
  - The prefix "270" always contains a zero

PATTERN:
  - E∩X cylinders at depth 3 have form: 5, {2 or 4}, 1
  - Dividing by 2: 521/2 = 260.5, 541/2 = 270.5
  - The integer part 260 or 270 contains a zero

GENERAL PRINCIPLE:
  If w starts with 5 followed by an even digit d (2 or 4),
  then w/2 starts with 2{0+d/2} = 26 or 27,
  but the full form is 26X or 27X where X comes from the remaining digits.

  The key is that 521 → 260.X and 541 → 270.X,
  and both 260 and 270 contain zeros.
""")

    # Verify the pattern for all depth-3,4,5 E∩X cylinders
    print("\n" + "=" * 70)
    print("PART E: Verify Pattern for All E∩X Cylinders")
    print("=" * 70)

    for depth in [3, 4, 5]:
        print(f"\n--- Depth {depth} ---")

        zero_forced_count = 0
        non_zero_count = 0
        non_zero_examples = []

        for d in product(range(1, 10), repeat=depth):
            cyl = ''.join(str(x) for x in d)
            if not (has_entry_witness(cyl) and has_exit_witness(cyl)):
                continue

            # Check if forced prefix contains zero
            cyl_int = int(cyl)
            half = cyl_int / 2

            # Get the integer part as the forced leading digits
            forced_prefix = str(int(half))

            if '0' in forced_prefix:
                zero_forced_count += 1
            else:
                non_zero_count += 1
                if len(non_zero_examples) < 5:
                    non_zero_examples.append((cyl, forced_prefix))

        total = zero_forced_count + non_zero_count
        print(f"  Total E∩X: {total}")
        print(f"  Zero-forced: {zero_forced_count} ({100*zero_forced_count/total:.1f}%)")
        print(f"  Non-zero: {non_zero_count}")

        if non_zero_examples:
            print(f"  Non-zero examples (potential counterexamples):")
            for cyl, forced in non_zero_examples:
                print(f"    {cyl} → {forced} (no zero in forced prefix!)")

    # =========================================================================
    # SYNTHESIS
    # =========================================================================

    print("\n" + "=" * 70)
    print("SYNTHESIS: The Forced-Zero Lemma for E∩X")
    print("=" * 70)

    print("""
KEY FINDING:

The E∩X cylinders have a specific structure that FORCES zero-predecessors:

1. E∩X at depth m requires overlapping entry (even→1) and exit (5→small) patterns.

2. For small m, the patterns MUST overlap, constraining the digit sequence.

3. The constrained sequences (like 521, 541) have the property that
   w/2 = X.Y where X contains a zero.

4. Therefore, all integers in the preimage interval I(w, k) have a
   zero in their leading digits, making them non-zeroless.

FORMAL LEMMA:

Let w be an m-digit E∩X cylinder with overlapping witnesses
(witness gap < 2). Then:

  ⌊w/2⌋ contains the digit 0

Consequently, w is unreachable from the zeroless subshift.

PROOF OF UNREACHABILITY:
- For any scale k, the predecessors N ∈ I(w, k) satisfy
  N ∈ [w·10^k/2, (w+1)·10^k/2)
- The leading digits of N are ⌊w/2⌋ followed by additional digits
- Since ⌊w/2⌋ contains 0, N is not zeroless
- Hence no zeroless predecessor exists for w
""")

if __name__ == "__main__":
    main()
