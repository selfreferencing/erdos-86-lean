"""
Experiment 46: Normalization Analysis + O(1) Cylinder Investigation

Two parallel investigations:

PART A: Normalization/Shift Analysis
When the predecessor 2^{n-1} has leading digit ≥5, doubling adds a digit.
So an m-digit 2^n might come from:
  - An m-digit predecessor (leading digit 1-4, no shift)
  - An (m-1)-digit predecessor (leading digit 5-9, shifts up)

This creates a THIRD regime beyond carry_in = 0 or 1.
If the "shift" cases have different π_E, this could explain the ~1/3 factor.

PART B: O(1) Cylinder Analysis
Exp 30 showed only ~9 cylinders are ever hit. What makes them special?
Characterize the actual hit cylinders and see why only these survive.
"""

import math

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

def get_transition_zone(m):
    """Get the range of n where 2^n has exactly m digits."""
    theta = math.log10(2)
    n_min = math.ceil((m - 1) / theta)
    n_max = math.floor(m / theta - 1e-10)
    return range(n_min, n_max + 1)

def analyze_predecessor_regime(n):
    """
    Analyze which regime the predecessor 2^{n-1} is in.

    Returns dict with:
        - 'shifted': predecessor has fewer digits (leading digit was ≥5)
        - pred_lead, pred_digits, succ_digits, etc.
    """
    if n <= 1:
        return None

    pred = 2 ** (n - 1)
    succ = 2 ** n

    pred_str = str(pred)
    succ_str = str(succ)

    # Did a shift occur? (predecessor has fewer digits)
    shifted = len(succ_str) > len(pred_str)

    # What was the leading digit of predecessor?
    pred_lead = int(pred_str[0])

    return {
        'shifted': shifted,
        'pred_lead': pred_lead,
        'pred_digits': len(pred_str),
        'succ_digits': len(succ_str),
        'pred_str': pred_str,
        'succ_str': succ_str,
        'pred_zeroless': is_zeroless(pred_str),
        'succ_zeroless': is_zeroless(succ_str)
    }

def find_all_hits(max_m=27):
    """Find all zeroless powers up to m digits."""
    hits = []
    for n in range(1, 500):  # Check up to n=500
        power = 2 ** n
        power_str = str(power)
        m = len(power_str)
        if m > max_m:
            break
        if is_zeroless(power_str):
            hits.append({
                'n': n,
                'm': m,
                'prefix': power_str,
                'regime': analyze_predecessor_regime(n)
            })
    return hits

def main():
    print("=" * 70)
    print("Experiment 46: Normalization + O(1) Cylinder Analysis")
    print("=" * 70)

    # =========================================================================
    # PART A: NORMALIZATION / SHIFT ANALYSIS
    # =========================================================================

    print("\n" + "=" * 70)
    print("PART A: Normalization/Shift Regime Analysis")
    print("=" * 70)

    print("\nQuestion: Does the shift (predecessor has fewer digits) create")
    print("a third regime that could explain the ~1/3 factor?")

    hits = find_all_hits(27)

    # Categorize by regime
    shifted_hits = [h for h in hits if h['regime'] and h['regime']['shifted']]
    unshifted_hits = [h for h in hits if h['regime'] and not h['regime']['shifted']]

    print(f"\nTotal hits: {len(hits)}")
    print(f"  Shifted (pred had fewer digits): {len(shifted_hits)}")
    print(f"  Unshifted (pred had same digits): {len(unshifted_hits)}")

    # Analyze predecessor zeros by regime
    print("\n--- Predecessor Zero Analysis by Regime ---")

    shifted_pred_zero = sum(1 for h in shifted_hits
                           if h['regime'] and not h['regime']['pred_zeroless'])
    unshifted_pred_zero = sum(1 for h in unshifted_hits
                              if h['regime'] and not h['regime']['pred_zeroless'])

    print(f"\nShifted hits with predecessor containing zero: {shifted_pred_zero}/{len(shifted_hits)}")
    if shifted_hits:
        print(f"  Rate: {shifted_pred_zero/len(shifted_hits):.3f}")

    print(f"\nUnshifted hits with predecessor containing zero: {unshifted_pred_zero}/{len(unshifted_hits)}")
    if unshifted_hits:
        print(f"  Rate: {unshifted_pred_zero/len(unshifted_hits):.3f}")

    # Show individual hits with regime info
    print("\n--- Individual Hit Analysis (first 20) ---")
    print(f"\n{'n':>4} | {'m':>2} | {'Shift':>5} | {'PredLead':>8} | {'PredZero':>8} | Prefix")
    print("-" * 70)

    for h in hits[:20]:
        if h['regime']:
            shift = 'YES' if h['regime']['shifted'] else 'no'
            pred_lead = h['regime']['pred_lead']
            pred_zero = 'YES' if not h['regime']['pred_zeroless'] else 'no'
        else:
            shift = 'N/A'
            pred_lead = 'N/A'
            pred_zero = 'N/A'
        print(f"{h['n']:>4} | {h['m']:>2} | {shift:>5} | {pred_lead:>8} | {pred_zero:>8} | {h['prefix'][:15]}")

    # Analyze entry witness by regime
    print("\n--- Entry Witness by Regime ---")

    shifted_with_E = sum(1 for h in shifted_hits if has_entry_witness(h['prefix']))
    unshifted_with_E = sum(1 for h in unshifted_hits if has_entry_witness(h['prefix']))

    print(f"\nShifted with entry witness: {shifted_with_E}/{len(shifted_hits)}")
    print(f"Unshifted with entry witness: {unshifted_with_E}/{len(unshifted_hits)}")

    # Cross-tabulation: regime × predecessor-has-zero × entry-witness
    print("\n--- Cross-tabulation: Regime × PredZero × EntryWitness ---")

    for regime_name, regime_hits in [('Shifted', shifted_hits), ('Unshifted', unshifted_hits)]:
        if not regime_hits:
            continue
        print(f"\n{regime_name} regime ({len(regime_hits)} hits):")

        for pred_zero_label, pred_zero_filter in [('Pred has zero', lambda h: not h['regime']['pred_zeroless']),
                                                   ('Pred zeroless', lambda h: h['regime']['pred_zeroless'])]:
            subset = [h for h in regime_hits if pred_zero_filter(h)]
            with_E = sum(1 for h in subset if has_entry_witness(h['prefix']))
            print(f"  {pred_zero_label}: {len(subset)} hits, {with_E} with entry witness")

    # =========================================================================
    # PART B: O(1) CYLINDER ANALYSIS
    # =========================================================================

    print("\n" + "=" * 70)
    print("PART B: O(1) Cylinder Analysis")
    print("=" * 70)

    print("\nExp 30 showed only ~9 cylinders are ever hit.")
    print("What are these cylinders and what makes them special?")

    # Group hits by leading 1, 2, or 3 digits (cylinder)
    cylinders_1 = {}  # 1-digit cylinder (leading digit)
    cylinders_2 = {}  # 2-digit cylinder (leading 2 digits)
    cylinders_3 = {}  # 3-digit cylinder (leading 3 digits)

    for h in hits:
        prefix = h['prefix']

        c1 = prefix[0]
        cylinders_1[c1] = cylinders_1.get(c1, 0) + 1

        if len(prefix) >= 2:
            c2 = prefix[:2]
            cylinders_2[c2] = cylinders_2.get(c2, 0) + 1

        if len(prefix) >= 3:
            c3 = prefix[:3]
            cylinders_3[c3] = cylinders_3.get(c3, 0) + 1

    print("\n--- 1-Digit Cylinders (Leading Digit) ---")
    print(f"Total distinct: {len(cylinders_1)}")
    for c, count in sorted(cylinders_1.items(), key=lambda x: -x[1]):
        print(f"  '{c}': {count} hits")

    print("\n--- 2-Digit Cylinders (Leading 2 Digits) ---")
    print(f"Total distinct: {len(cylinders_2)}")
    for c, count in sorted(cylinders_2.items(), key=lambda x: -x[1])[:15]:
        print(f"  '{c}': {count} hits")
    if len(cylinders_2) > 15:
        print(f"  ... and {len(cylinders_2) - 15} more")

    print("\n--- 3-Digit Cylinders (Leading 3 Digits) ---")
    print(f"Total distinct: {len(cylinders_3)}")
    for c, count in sorted(cylinders_3.items(), key=lambda x: -x[1])[:15]:
        # Check for entry/exit witnesses in this cylinder
        has_E = has_entry_witness(c) if len(c) >= 2 else False
        has_X = has_exit_witness(c) if len(c) >= 2 else False
        markers = []
        if has_E: markers.append('E')
        if has_X: markers.append('X')
        marker_str = f" [{','.join(markers)}]" if markers else ""
        print(f"  '{c}': {count} hits{marker_str}")
    if len(cylinders_3) > 15:
        print(f"  ... and {len(cylinders_3) - 15} more")

    # Analyze which cylinders have entry/exit witnesses
    print("\n--- Cylinder Pattern Analysis ---")

    # For 3-digit cylinders, check E/X patterns
    cylinders_with_E = [c for c in cylinders_3 if has_entry_witness(c)]
    cylinders_with_X = [c for c in cylinders_3 if has_exit_witness(c)]
    cylinders_with_both = [c for c in cylinders_3 if has_entry_witness(c) and has_exit_witness(c)]

    print(f"\n3-digit cylinders with entry witness: {len(cylinders_with_E)}")
    print(f"3-digit cylinders with exit witness: {len(cylinders_with_X)}")
    print(f"3-digit cylinders with BOTH: {len(cylinders_with_both)}")
    if cylinders_with_both:
        print(f"  Cylinders: {cylinders_with_both}")

    # Check the "danger cylinder" hypothesis: are there patterns that appear
    # only at certain m values?
    print("\n--- Cylinder Persistence Across m ---")

    # Track which 2-digit cylinders appear at each m
    cylinders_by_m = {}
    for h in hits:
        m = h['m']
        if m not in cylinders_by_m:
            cylinders_by_m[m] = set()
        if len(h['prefix']) >= 2:
            cylinders_by_m[m].add(h['prefix'][:2])

    print(f"\n{'m':>3} | {'# Hits':>6} | 2-digit cylinders used")
    print("-" * 60)

    for m in sorted(cylinders_by_m.keys()):
        n_hits = sum(1 for h in hits if h['m'] == m)
        cyls = sorted(cylinders_by_m[m])
        print(f"{m:>3} | {n_hits:>6} | {', '.join(cyls)}")

    # Cumulative cylinder count
    print("\n--- Cumulative Distinct Cylinders ---")

    all_1 = set()
    all_2 = set()
    all_3 = set()

    print(f"\n{'m':>3} | {'1-dig':>5} | {'2-dig':>5} | {'3-dig':>5}")
    print("-" * 30)

    for m in sorted(set(h['m'] for h in hits)):
        for h in hits:
            if h['m'] == m:
                all_1.add(h['prefix'][0])
                if len(h['prefix']) >= 2:
                    all_2.add(h['prefix'][:2])
                if len(h['prefix']) >= 3:
                    all_3.add(h['prefix'][:3])
        print(f"{m:>3} | {len(all_1):>5} | {len(all_2):>5} | {len(all_3):>5}")

    # =========================================================================
    # SYNTHESIS
    # =========================================================================

    print("\n" + "=" * 70)
    print("SYNTHESIS")
    print("=" * 70)

    # Calculate the "effective third regime" rate
    total_with_regime = len(shifted_hits) + len(unshifted_hits)
    if total_with_regime > 0:
        shift_rate = len(shifted_hits) / total_with_regime
        print(f"\nShift rate: {len(shifted_hits)}/{total_with_regime} = {shift_rate:.3f}")

        # Does shift correlate with predecessor having zero?
        if shifted_hits:
            shifted_zero_rate = shifted_pred_zero / len(shifted_hits)
        else:
            shifted_zero_rate = 0
        if unshifted_hits:
            unshifted_zero_rate = unshifted_pred_zero / len(unshifted_hits)
        else:
            unshifted_zero_rate = 0

        print(f"\nPredecessor-has-zero rate:")
        print(f"  Shifted regime: {shifted_zero_rate:.3f}")
        print(f"  Unshifted regime: {unshifted_zero_rate:.3f}")

        # If shift creates asymmetry in predecessor zeros, this could explain part of the gap
        if abs(shifted_zero_rate - unshifted_zero_rate) > 0.1:
            print("\n>>> ASYMMETRY DETECTED: Shift regime has different predecessor-zero rate!")
            print("    This could contribute to the ~3× gap.")
        else:
            print("\n>>> No significant asymmetry between regimes.")

    print(f"\nTotal distinct cylinders at each depth:")
    print(f"  1-digit: {len(cylinders_1)} (possible: 9)")
    print(f"  2-digit: {len(cylinders_2)} (possible: 81)")
    print(f"  3-digit: {len(cylinders_3)} (possible: 729)")

    # The O(1) cylinder observation
    print(f"\nO(1) cylinder hypothesis:")
    print(f"  With only {len(cylinders_3)} distinct 3-digit cylinders ever hit,")
    print(f"  the orbit is confined to a tiny fraction of the possible space.")
    print(f"  This concentration could combine with other factors to explain the gap.")

if __name__ == "__main__":
    main()
