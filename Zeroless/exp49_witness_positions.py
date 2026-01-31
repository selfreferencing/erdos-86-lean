"""
Experiment 49: Entry/Exit Witness Position Analysis

Questions:
1. WHERE in the m-digit prefix do entry and exit witnesses appear?
2. Are they concentrated in certain positions (early? late?)?
3. Do E and X witnesses appear in SEPARATED positions, explaining why
   cylinder-level E∩X is nearly empty but full-prefix E∩X is common?

The "separated positions" hypothesis:
- E witness tends to appear at position i
- X witness tends to appear at position j
- If i and j rarely overlap, the model overcounts by assuming they can co-exist anywhere
"""

import math
from collections import defaultdict

def is_zeroless(s):
    """Check if string has no '0' digit."""
    return '0' not in s

def find_entry_witnesses(prefix):
    """
    Find ALL positions of entry witnesses: (2,4,6,8) followed by 1.
    Returns list of positions (0-indexed).
    """
    positions = []
    for i in range(len(prefix) - 1):
        if prefix[i] in '2468' and prefix[i+1] == '1':
            positions.append(i)
    return positions

def find_exit_witnesses(prefix):
    """
    Find ALL positions of exit witnesses: 5 followed by (1,2,3,4).
    Returns list of positions (0-indexed).
    """
    positions = []
    for i in range(len(prefix) - 1):
        if prefix[i] == '5' and prefix[i+1] in '1234':
            positions.append(i)
    return positions

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

def main():
    print("=" * 70)
    print("Experiment 49: Entry/Exit Witness Position Analysis")
    print("=" * 70)

    hits = find_all_hits(27)

    # =========================================================================
    # PART A: Where do witnesses appear in actual hits?
    # =========================================================================

    print("\n" + "=" * 70)
    print("PART A: Witness Positions in Actual Hits")
    print("=" * 70)

    entry_positions = []  # (relative_position, m, n) tuples
    exit_positions = []

    hits_with_E = []
    hits_with_X = []
    hits_with_both = []

    for h in hits:
        prefix = h['prefix']
        m = h['m']
        n = h['n']

        e_pos = find_entry_witnesses(prefix)
        x_pos = find_exit_witnesses(prefix)

        h['e_positions'] = e_pos
        h['x_positions'] = x_pos

        if e_pos:
            hits_with_E.append(h)
            for pos in e_pos:
                rel_pos = pos / (m - 1) if m > 1 else 0  # Normalize to [0, 1]
                entry_positions.append((pos, rel_pos, m, n))

        if x_pos:
            hits_with_X.append(h)
            for pos in x_pos:
                rel_pos = pos / (m - 1) if m > 1 else 0
                exit_positions.append((pos, rel_pos, m, n))

        if e_pos and x_pos:
            hits_with_both.append(h)

    print(f"\nTotal hits: {len(hits)}")
    print(f"Hits with entry witness: {len(hits_with_E)} ({len(hits_with_E)/len(hits):.1%})")
    print(f"Hits with exit witness: {len(hits_with_X)} ({len(hits_with_X)/len(hits):.1%})")
    print(f"Hits with BOTH: {len(hits_with_both)} ({len(hits_with_both)/len(hits):.1%})")

    # =========================================================================
    # PART B: Position distributions
    # =========================================================================

    print("\n" + "=" * 70)
    print("PART B: Position Distributions")
    print("=" * 70)

    # Absolute position distribution
    print("\n--- Entry Witness Absolute Positions ---")
    e_abs_dist = defaultdict(int)
    for pos, rel, m, n in entry_positions:
        e_abs_dist[pos] += 1
    print(f"Total entry witnesses found: {len(entry_positions)}")
    for pos in sorted(e_abs_dist.keys()):
        print(f"  Position {pos}: {e_abs_dist[pos]} ({e_abs_dist[pos]/len(entry_positions):.1%})")

    print("\n--- Exit Witness Absolute Positions ---")
    x_abs_dist = defaultdict(int)
    for pos, rel, m, n in exit_positions:
        x_abs_dist[pos] += 1
    print(f"Total exit witnesses found: {len(exit_positions)}")
    for pos in sorted(x_abs_dist.keys()):
        print(f"  Position {pos}: {x_abs_dist[pos]} ({x_abs_dist[pos]/len(exit_positions):.1%})")

    # Relative position (0 = start, 1 = end)
    print("\n--- Relative Position Summary ---")
    if entry_positions:
        avg_e_rel = sum(rel for _, rel, _, _ in entry_positions) / len(entry_positions)
        print(f"Entry witnesses: avg relative position = {avg_e_rel:.3f}")
        print(f"  (0 = start of prefix, 1 = end)")

    if exit_positions:
        avg_x_rel = sum(rel for _, rel, _, _ in exit_positions) / len(exit_positions)
        print(f"Exit witnesses: avg relative position = {avg_x_rel:.3f}")

    # =========================================================================
    # PART C: Hits with BOTH witnesses - position separation
    # =========================================================================

    print("\n" + "=" * 70)
    print("PART C: Position Separation in Hits with Both E and X")
    print("=" * 70)

    if hits_with_both:
        print(f"\n{len(hits_with_both)} hits have both entry and exit witnesses:")
        print(f"\n{'n':>4} | {'m':>3} | {'E pos':>10} | {'X pos':>10} | {'Min gap':>8} | Prefix")
        print("-" * 70)

        gaps = []
        for h in hits_with_both:
            e_pos = h['e_positions']
            x_pos = h['x_positions']

            # Minimum gap between any E and X position
            min_gap = min(abs(e - x) for e in e_pos for x in x_pos)
            gaps.append(min_gap)

            e_str = ','.join(str(p) for p in e_pos)
            x_str = ','.join(str(p) for p in x_pos)
            print(f"{h['n']:>4} | {h['m']:>3} | {e_str:>10} | {x_str:>10} | {min_gap:>8} | {h['prefix'][:20]}")

        print(f"\nGap statistics:")
        print(f"  Min gap: {min(gaps)}")
        print(f"  Max gap: {max(gaps)}")
        print(f"  Avg gap: {sum(gaps)/len(gaps):.2f}")

        # Do E and X ever OVERLAP (gap = 0 or 1)?
        overlapping = sum(1 for g in gaps if g <= 1)
        print(f"\n  Overlapping (gap <= 1): {overlapping}/{len(gaps)}")
        print(f"  Separated (gap >= 2): {len(gaps) - overlapping}/{len(gaps)}")
    else:
        print("\nNo hits have both entry and exit witnesses.")

    # =========================================================================
    # PART D: Detailed analysis of E∩X hits
    # =========================================================================

    print("\n" + "=" * 70)
    print("PART D: Detailed E∩X Hit Analysis")
    print("=" * 70)

    for h in hits_with_both:
        prefix = h['prefix']
        m = h['m']
        n = h['n']
        e_pos = h['e_positions']
        x_pos = h['x_positions']

        print(f"\n2^{n} = {prefix}")
        print(f"  m = {m} digits")

        # Show the patterns
        for pos in e_pos:
            pattern = prefix[pos:pos+2]
            print(f"  Entry witness at pos {pos}: '{pattern}' (even={prefix[pos]}, then 1)")

        for pos in x_pos:
            pattern = prefix[pos:pos+2]
            print(f"  Exit witness at pos {pos}: '{pattern}' (5, then {prefix[pos+1]})")

        # Visual representation
        markers = [' '] * m
        for pos in e_pos:
            markers[pos] = 'E'
            if markers[pos+1] == ' ':
                markers[pos+1] = 'e'
            elif markers[pos+1] == 'X':
                markers[pos+1] = '*'  # Overlap!
        for pos in x_pos:
            if markers[pos] == 'E':
                markers[pos] = '*'  # Overlap!
            elif markers[pos] == ' ':
                markers[pos] = 'X'
            if markers[pos+1] == ' ':
                markers[pos+1] = 'x'
            elif markers[pos+1] == 'e':
                markers[pos+1] = '*'

        print(f"  Digits:  {prefix}")
        print(f"  Markers: {''.join(markers)}")
        print(f"  (E=entry start, e=entry cont, X=exit start, x=exit cont, *=overlap)")

    # =========================================================================
    # PART E: Separation hypothesis test
    # =========================================================================

    print("\n" + "=" * 70)
    print("PART E: Separation Hypothesis Test")
    print("=" * 70)

    print("""
Hypothesis: E and X witnesses tend to appear in DIFFERENT regions of the prefix.

If true:
- E might cluster near the start (positions 0-5)
- X might cluster near the middle or end
- This would explain why cylinder-level E∩X is empty (only 2/729)
  but full-prefix E∩X is common at larger m

Testing: Compare where E vs X witnesses appear.
""")

    # For hits with both, compare E and X positions
    if hits_with_both:
        e_positions_in_both = []
        x_positions_in_both = []

        for h in hits_with_both:
            for pos in h['e_positions']:
                e_positions_in_both.append(pos)
            for pos in h['x_positions']:
                x_positions_in_both.append(pos)

        avg_e = sum(e_positions_in_both) / len(e_positions_in_both) if e_positions_in_both else 0
        avg_x = sum(x_positions_in_both) / len(x_positions_in_both) if x_positions_in_both else 0

        print(f"In hits with BOTH witnesses:")
        print(f"  Entry witnesses: avg position = {avg_e:.2f}")
        print(f"  Exit witnesses: avg position = {avg_x:.2f}")
        print(f"  Separation: {abs(avg_x - avg_e):.2f} positions on average")

        if avg_e < avg_x:
            print(f"\n  >>> Entry tends to appear EARLIER than exit")
        else:
            print(f"\n  >>> Exit tends to appear EARLIER than entry")

    # =========================================================================
    # PART F: What fraction of random prefixes have E∩X vs actual hits?
    # =========================================================================

    print("\n" + "=" * 70)
    print("PART F: E∩X Rate Comparison")
    print("=" * 70)

    # For each m, compute the fraction of hits that have both E and X
    print(f"\n{'m':>3} | {'Hits':>5} | {'E':>4} | {'X':>4} | {'E∩X':>4} | {'E∩X %':>7}")
    print("-" * 45)

    for m in range(3, 28):
        m_hits = [h for h in hits if h['m'] == m]
        if not m_hits:
            continue

        n_hits = len(m_hits)
        n_e = sum(1 for h in m_hits if h['e_positions'])
        n_x = sum(1 for h in m_hits if h['x_positions'])
        n_ex = sum(1 for h in m_hits if h['e_positions'] and h['x_positions'])

        ex_pct = n_ex / n_hits * 100 if n_hits > 0 else 0
        print(f"{m:>3} | {n_hits:>5} | {n_e:>4} | {n_x:>4} | {n_ex:>4} | {ex_pct:>6.1f}%")

    # =========================================================================
    # SYNTHESIS
    # =========================================================================

    print("\n" + "=" * 70)
    print("SYNTHESIS")
    print("=" * 70)

    total_e_pos = len(entry_positions)
    total_x_pos = len(exit_positions)

    print(f"""
KEY FINDINGS:

1. POSITION CONCENTRATION:
   - Entry witnesses: {total_e_pos} found across {len(hits_with_E)} hits
   - Exit witnesses: {total_x_pos} found across {len(hits_with_X)} hits
""")

    if entry_positions:
        print(f"   - Entry avg relative position: {avg_e_rel:.3f}")
    if exit_positions:
        print(f"   - Exit avg relative position: {avg_x_rel:.3f}")

    if hits_with_both:
        print(f"""
2. SEPARATION IN E∩X HITS:
   - {len(hits_with_both)} hits have both witnesses
   - Average gap between E and X: {sum(gaps)/len(gaps):.2f} positions
   - Overlapping (gap <= 1): {overlapping}/{len(gaps)}

3. IMPLICATION FOR MODEL:
""")
        if sum(gaps)/len(gaps) > 2:
            print("""   The E and X witnesses tend to be SEPARATED by several positions.
   This explains:
   - Cylinder-level E∩X is nearly empty (patterns can't overlap in 3 digits)
   - Full-prefix E∩X is common (patterns appear in different positions)
   - The model may overcount because it assumes independence""")
        else:
            print("""   The E and X witnesses often appear CLOSE together.
   The separation hypothesis may not fully explain the gap.""")

if __name__ == "__main__":
    main()
