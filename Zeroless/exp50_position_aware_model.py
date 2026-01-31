"""
Experiment 50: Position-Aware E∩X Model

The naive transfer matrix model assumes E and X witnesses can appear at ANY positions
independently. But Exp 48-49 showed:
- E and X are structurally incompatible at short range (can't overlap in ≤3 digits)
- In actual hits, E and X are separated by ~4.43 positions on average
- 86% of E∩X hits have gap ≥ 2

This experiment:
1. Computes naive |E∩X| (patterns anywhere, independent)
2. Computes position-constrained |E∩X| (patterns must be separated)
3. Quantifies the overcounting factor
4. Tests if this explains the ~3× gap
"""

import math
from itertools import product
from collections import defaultdict

def has_entry_at_pos(prefix, pos):
    """Check if entry witness (even→1) starts at position pos."""
    if pos + 1 >= len(prefix):
        return False
    return prefix[pos] in '2468' and prefix[pos+1] == '1'

def has_exit_at_pos(prefix, pos):
    """Check if exit witness (5→small) starts at position pos."""
    if pos + 1 >= len(prefix):
        return False
    return prefix[pos] == '5' and prefix[pos+1] in '1234'

def find_all_entry_positions(prefix):
    """Find all positions where entry witness occurs."""
    return [i for i in range(len(prefix)-1) if has_entry_at_pos(prefix, i)]

def find_all_exit_positions(prefix):
    """Find all positions where exit witness occurs."""
    return [i for i in range(len(prefix)-1) if has_exit_at_pos(prefix, i)]

def min_gap(e_positions, x_positions):
    """Minimum gap between any entry and exit position."""
    if not e_positions or not x_positions:
        return float('inf')
    return min(abs(e - x) for e in e_positions for x in x_positions)

def enumerate_zeroless_prefixes(m):
    """Generate all m-digit zeroless prefixes."""
    if m > 7:
        return None  # Too many to enumerate
    for digits in product(range(1, 10), repeat=m):
        yield ''.join(str(d) for d in digits)

def main():
    print("=" * 70)
    print("Experiment 50: Position-Aware E∩X Model")
    print("=" * 70)

    print("""
The naive model assumes E and X patterns are independent.
The position-aware model requires they be SEPARATED.

If separation constraint reduces |E∩X| by factor ~3, we've found the gap source.
""")

    # =========================================================================
    # PART A: Naive vs Position-Constrained Counts
    # =========================================================================

    print("=" * 70)
    print("PART A: Naive vs Position-Constrained E∩X Counts")
    print("=" * 70)

    results = []

    for m in range(3, 8):
        print(f"\n--- m = {m} ---")

        total_prefixes = 0
        has_E = 0
        has_X = 0
        has_EX_naive = 0  # Has both E and X (anywhere)
        has_EX_gap0 = 0   # E and X can overlap (gap = 0)
        has_EX_gap1 = 0   # E and X separated by at least 1
        has_EX_gap2 = 0   # E and X separated by at least 2
        has_EX_gap3 = 0   # E and X separated by at least 3
        has_EX_gap4 = 0   # E and X separated by at least 4

        for prefix in enumerate_zeroless_prefixes(m):
            total_prefixes += 1

            e_pos = find_all_entry_positions(prefix)
            x_pos = find_all_exit_positions(prefix)

            if e_pos:
                has_E += 1
            if x_pos:
                has_X += 1

            if e_pos and x_pos:
                has_EX_naive += 1
                gap = min_gap(e_pos, x_pos)

                if gap >= 0:
                    has_EX_gap0 += 1
                if gap >= 1:
                    has_EX_gap1 += 1
                if gap >= 2:
                    has_EX_gap2 += 1
                if gap >= 3:
                    has_EX_gap3 += 1
                if gap >= 4:
                    has_EX_gap4 += 1

        # Compute rates
        rate_E = has_E / total_prefixes
        rate_X = has_X / total_prefixes
        rate_EX_naive = has_EX_naive / total_prefixes
        rate_EX_indep = rate_E * rate_X  # If independent

        print(f"  Total zeroless {m}-digit prefixes: {total_prefixes}")
        print(f"  Has entry witness (E): {has_E} ({rate_E:.4f})")
        print(f"  Has exit witness (X): {has_X} ({rate_X:.4f})")
        print(f"  Has both (E∩X naive): {has_EX_naive} ({rate_EX_naive:.4f})")
        print(f"  Independence prediction: {rate_E * rate_X:.4f}")

        if has_EX_naive > 0:
            print(f"\n  Gap-constrained counts:")
            print(f"    Any gap (≥0): {has_EX_gap0} (100%)")
            print(f"    Gap ≥ 1: {has_EX_gap1} ({has_EX_gap1/has_EX_naive:.1%})")
            print(f"    Gap ≥ 2: {has_EX_gap2} ({has_EX_gap2/has_EX_naive:.1%})")
            print(f"    Gap ≥ 3: {has_EX_gap3} ({has_EX_gap3/has_EX_naive:.1%})")
            print(f"    Gap ≥ 4: {has_EX_gap4} ({has_EX_gap4/has_EX_naive:.1%})")

        results.append({
            'm': m,
            'total': total_prefixes,
            'E': has_E,
            'X': has_X,
            'EX_naive': has_EX_naive,
            'EX_gap2': has_EX_gap2,
            'EX_gap3': has_EX_gap3,
            'EX_gap4': has_EX_gap4,
        })

    # =========================================================================
    # PART B: Overcounting Factor Analysis
    # =========================================================================

    print("\n" + "=" * 70)
    print("PART B: Overcounting Factor Analysis")
    print("=" * 70)

    print(f"\n{'m':>3} | {'E∩X naive':>10} | {'Gap≥2':>10} | {'Gap≥3':>10} | {'Gap≥4':>10} | {'Ratio (naive/gap2)':>18}")
    print("-" * 75)

    for r in results:
        m = r['m']
        naive = r['EX_naive']
        gap2 = r['EX_gap2']
        gap3 = r['EX_gap3']
        gap4 = r['EX_gap4']

        ratio = naive / gap2 if gap2 > 0 else float('inf')

        print(f"{m:>3} | {naive:>10} | {gap2:>10} | {gap3:>10} | {gap4:>10} | {ratio:>18.2f}")

    # =========================================================================
    # PART C: Position-Aware Transfer Matrix Concept
    # =========================================================================

    print("\n" + "=" * 70)
    print("PART C: Position-Aware Transfer Matrix Concept")
    print("=" * 70)

    print("""
The naive transfer matrix tracks:
- State = (has_seen_E, last_digit_info_for_E, has_seen_X, last_digit_info_for_X)

A position-aware matrix would track:
- Position of first E witness (if any)
- Position of first X witness (if any)
- Require |pos_E - pos_X| ≥ MIN_GAP

For large m, the key question is:
  What fraction of E∩X prefixes have separated witnesses?

If this fraction is ~1/3, the position constraint explains the gap.
""")

    # Estimate the asymptotic fraction
    print("\nAsymptotic estimate:")
    print("  At large m, both E and X appear with high probability (R_{m,1} → 1)")
    print("  The question is: what's the probability they're SEPARATED?")

    # For each m, compute the fraction of E∩X that's separated
    print(f"\n{'m':>3} | {'P(gap≥2 | E∩X)':>15} | {'P(gap≥3 | E∩X)':>15} | {'P(gap≥4 | E∩X)':>15}")
    print("-" * 60)

    for r in results:
        m = r['m']
        naive = r['EX_naive']
        if naive > 0:
            p_gap2 = r['EX_gap2'] / naive
            p_gap3 = r['EX_gap3'] / naive
            p_gap4 = r['EX_gap4'] / naive
            print(f"{m:>3} | {p_gap2:>15.4f} | {p_gap3:>15.4f} | {p_gap4:>15.4f}")
        else:
            print(f"{m:>3} | {'N/A':>15} | {'N/A':>15} | {'N/A':>15}")

    # =========================================================================
    # PART D: Does Separation Explain the ~3× Gap?
    # =========================================================================

    print("\n" + "=" * 70)
    print("PART D: Does Separation Explain the ~3× Gap?")
    print("=" * 70)

    print("""
The model predicts E[isolated hits] = L_m × |E∩X| / 10^{m+1} ≈ 2.94 at m=27.
We need this to be < 1, requiring |E∩X| to be ~3× smaller.

If the "true" E∩X only counts patterns with gap ≥ K, then:
  |E∩X_true| = |E∩X_naive| × P(gap ≥ K | E∩X)

For the gap to be explained, we need:
  P(gap ≥ K | E∩X) ≈ 1/3

From the data above:
""")

    # Analyze the trend
    for r in results:
        if r['EX_naive'] > 0:
            m = r['m']
            p_gap2 = r['EX_gap2'] / r['EX_naive']
            p_gap3 = r['EX_gap3'] / r['EX_naive']
            p_gap4 = r['EX_gap4'] / r['EX_naive']

            print(f"  m={m}: P(gap≥2)={p_gap2:.3f}, P(gap≥3)={p_gap3:.3f}, P(gap≥4)={p_gap4:.3f}")

            if abs(p_gap3 - 0.33) < 0.1:
                print(f"    >>> Gap≥3 gives ~1/3 reduction!")
            if abs(p_gap4 - 0.33) < 0.1:
                print(f"    >>> Gap≥4 gives ~1/3 reduction!")

    # =========================================================================
    # PART E: Detailed Position Distribution
    # =========================================================================

    print("\n" + "=" * 70)
    print("PART E: Position Distribution in E∩X Prefixes")
    print("=" * 70)

    # For m=6 or 7, show where E and X tend to appear
    for m in [5, 6, 7]:
        print(f"\n--- m = {m}: Position distribution ---")

        e_pos_dist = defaultdict(int)
        x_pos_dist = defaultdict(int)
        gap_dist = defaultdict(int)

        count = 0
        for prefix in enumerate_zeroless_prefixes(m):
            e_pos = find_all_entry_positions(prefix)
            x_pos = find_all_exit_positions(prefix)

            if e_pos and x_pos:
                count += 1
                for p in e_pos:
                    e_pos_dist[p] += 1
                for p in x_pos:
                    x_pos_dist[p] += 1
                gap_dist[min_gap(e_pos, x_pos)] += 1

        print(f"  Total E∩X prefixes: {count}")

        if count > 0:
            print(f"\n  Entry witness positions:")
            for pos in sorted(e_pos_dist.keys()):
                pct = e_pos_dist[pos] / count * 100
                bar = '#' * int(pct / 2)
                print(f"    Pos {pos}: {e_pos_dist[pos]:>5} ({pct:>5.1f}%) {bar}")

            print(f"\n  Exit witness positions:")
            for pos in sorted(x_pos_dist.keys()):
                pct = x_pos_dist[pos] / count * 100
                bar = '#' * int(pct / 2)
                print(f"    Pos {pos}: {x_pos_dist[pos]:>5} ({pct:>5.1f}%) {bar}")

            print(f"\n  Gap distribution:")
            for gap in sorted(gap_dist.keys()):
                pct = gap_dist[gap] / count * 100
                bar = '#' * int(pct / 2)
                print(f"    Gap {gap}: {gap_dist[gap]:>5} ({pct:>5.1f}%) {bar}")

    # =========================================================================
    # SYNTHESIS
    # =========================================================================

    print("\n" + "=" * 70)
    print("SYNTHESIS")
    print("=" * 70)

    # Compute average reduction factor
    reduction_factors = []
    for r in results:
        if r['EX_naive'] > 0 and r['EX_gap2'] > 0:
            reduction_factors.append(r['EX_naive'] / r['EX_gap2'])

    if reduction_factors:
        avg_reduction = sum(reduction_factors) / len(reduction_factors)
        print(f"""
KEY FINDINGS:

1. NAIVE VS CONSTRAINED COUNTS:
   - Average overcounting factor (naive / gap≥2): {avg_reduction:.2f}×

2. DOES THIS EXPLAIN THE ~3× GAP?
""")
        if 2.5 <= avg_reduction <= 3.5:
            print("""   YES! The position separation constraint reduces |E∩X| by ~3×.
   The naive model overcounts by including states where E and X overlap,
   but the dynamics prevent such overlaps.

   This is the source of the 19-digit gap:
   - Naive model: threshold at m ≈ 46
   - Position-aware model: threshold at m ≈ 27
   - The ~3× reduction comes from requiring gap ≥ 2 between witnesses.""")
        elif avg_reduction < 2.5:
            print(f"""   PARTIAL: Reduction factor is {avg_reduction:.2f}×, less than needed ~3×.
   Position separation contributes but doesn't fully explain the gap.
   Other factors must also contribute.""")
        else:
            print(f"""   STRONGER THAN NEEDED: Reduction factor is {avg_reduction:.2f}×, more than ~3×.
   Position separation over-explains the gap, or the constraint is too strict.""")

        print(f"""
3. IMPLICATION FOR THE TRANSFER MATRIX:
   - The naive transfer matrix counts |E∩X| = 3.26 × 10^26 at m=27
   - A position-aware matrix would give |E∩X_true| ≈ |E∩X| / {avg_reduction:.1f}
   - This would shift the threshold from m=46 to approximately m=27

4. STRUCTURAL INSIGHT:
   - E witness (even→1) and X witness (5→small) are locally incompatible
   - They can only co-exist in the same prefix if SEPARATED
   - This is a geometric/combinatorial constraint, not probabilistic
""")

if __name__ == "__main__":
    main()
