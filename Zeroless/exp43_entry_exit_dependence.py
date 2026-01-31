"""
Experiment 43: Entry-Exit Dependence Analysis

Investigates whether entry and exit events are correlated in actual hits.
This could explain the 19-digit gap between the k=1 model (m=46) and
empirical threshold (m=27).

Key question: Is P(E ∩ X | hit) < P(E | hit) × P(X | hit)?
If so, the model overcounts and the effective threshold is earlier.
"""

import math

def is_zeroless(s):
    """Check if string has no '0' digit."""
    return '0' not in s

def get_m_digit_prefix(n, m):
    """Get the first m digits of 2^n as a string."""
    # Use logarithms for large n
    if n > 100:
        log_val = n * math.log10(2)
        frac = log_val - int(log_val)
        # Get first m+5 digits via 10^frac
        mantissa = 10 ** (frac + m + 4)
        return str(int(mantissa))[:m]
    else:
        return str(2**n)[:m]

def has_entry_witness(prefix):
    """
    Check if prefix has entry witness: (2,4,6,8) followed by 1.
    This indicates the state could have been reached from a predecessor with visible zero.
    """
    for i in range(len(prefix) - 1):
        if prefix[i] in '2468' and prefix[i+1] == '1':
            return True
    return False

def has_exit_witness(prefix):
    """
    Check if prefix has exit witness: 5 followed by (1,2,3,4).
    This indicates the state will produce a zero on doubling.
    """
    for i in range(len(prefix) - 1):
        if prefix[i] == '5' and prefix[i+1] in '1234':
            return True
    return False

def predecessor_has_visible_zero(n, m):
    """
    Check if the ACTUAL predecessor (2^{n-1}) has a zero in its m-digit prefix
    when viewed at the appropriate scale.

    The predecessor 2^{n-1} may have m-1 or m digits depending on normalization.
    """
    if n <= 1:
        return False

    # Get 2^{n-1}
    pred = 2 ** (n - 1)
    pred_str = str(pred)

    # The predecessor's visible prefix depends on whether normalization occurred
    # If 2^n has m digits and 2^{n-1} has m-1 digits, the comparison is shifted

    # For simplicity, check if predecessor has zero in first m digits
    pred_prefix = pred_str[:m] if len(pred_str) >= m else pred_str
    return '0' in pred_prefix

def successor_has_visible_zero(n, m):
    """
    Check if the ACTUAL successor (2^{n+1}) has a zero in its m-digit prefix
    when viewed at the appropriate scale.
    """
    # Get 2^{n+1}
    succ = 2 ** (n + 1)
    succ_str = str(succ)

    # Check if successor has zero in first m digits
    succ_prefix = succ_str[:m] if len(succ_str) >= m else succ_str
    return '0' in succ_prefix

def find_transition_zone_hits(m, max_n=10000):
    """
    Find all n where 2^n has exactly m digits and is entirely zeroless.
    """
    theta = math.log10(2)
    n_min = math.ceil((m - 1) / theta)
    n_max = math.floor(m / theta - 1e-10)

    hits = []
    for n in range(max(1, n_min), min(max_n, n_max + 1)):
        power = 2 ** n
        power_str = str(power)
        if len(power_str) == m and is_zeroless(power_str):
            hits.append(n)

    return hits

def analyze_hit(n, m):
    """
    Analyze a single hit: check entry witness, exit witness,
    actual predecessor zero, actual successor zero.
    """
    power = 2 ** n
    prefix = str(power)[:m]

    entry_witness = has_entry_witness(prefix)
    exit_witness = has_exit_witness(prefix)
    pred_zero = predecessor_has_visible_zero(n, m)
    succ_zero = successor_has_visible_zero(n, m)

    return {
        'n': n,
        'prefix': prefix,
        'entry_witness': entry_witness,
        'exit_witness': exit_witness,
        'pred_zero': pred_zero,
        'succ_zero': succ_zero
    }

def main():
    print("=" * 70)
    print("Experiment 43: Entry-Exit Dependence Analysis")
    print("=" * 70)

    print("\nGoal: Check if entry and exit are correlated in actual hits.")
    print("If negatively correlated, explains why model threshold (m=46)")
    print("differs from empirical threshold (m=27).")

    # Analyze hits for various m
    all_hits = []

    print("\n" + "=" * 70)
    print("Collecting hits for m = 2..27")
    print("=" * 70)

    for m in range(2, 28):
        hits = find_transition_zone_hits(m)
        for n in hits:
            analysis = analyze_hit(n, m)
            analysis['m'] = m
            all_hits.append(analysis)

    print(f"\nTotal hits found: {len(all_hits)}")

    # Compute statistics
    print("\n" + "=" * 70)
    print("Entry/Exit Witness Statistics (based on prefix patterns)")
    print("=" * 70)

    n_total = len(all_hits)
    n_entry = sum(1 for h in all_hits if h['entry_witness'])
    n_exit = sum(1 for h in all_hits if h['exit_witness'])
    n_both = sum(1 for h in all_hits if h['entry_witness'] and h['exit_witness'])

    p_entry = n_entry / n_total if n_total > 0 else 0
    p_exit = n_exit / n_total if n_total > 0 else 0
    p_both = n_both / n_total if n_total > 0 else 0
    p_independent = p_entry * p_exit

    print(f"\nP(entry witness | hit) = {n_entry}/{n_total} = {p_entry:.4f}")
    print(f"P(exit witness | hit) = {n_exit}/{n_total} = {p_exit:.4f}")
    print(f"P(both | hit) = {n_both}/{n_total} = {p_both:.4f}")
    print(f"P(entry) × P(exit) = {p_independent:.4f}")

    if p_independent > 0:
        ratio = p_both / p_independent
        print(f"\nRatio: P(both) / [P(entry)×P(exit)] = {ratio:.4f}")
        if ratio < 0.8:
            print(">>> NEGATIVE CORRELATION: Entry and exit are less likely to co-occur")
        elif ratio > 1.2:
            print(">>> POSITIVE CORRELATION: Entry and exit tend to co-occur")
        else:
            print(">>> ROUGHLY INDEPENDENT")

    # Compute statistics for actual predecessor/successor zeros
    print("\n" + "=" * 70)
    print("Actual Predecessor/Successor Zero Statistics")
    print("=" * 70)

    n_pred_zero = sum(1 for h in all_hits if h['pred_zero'])
    n_succ_zero = sum(1 for h in all_hits if h['succ_zero'])
    n_both_zero = sum(1 for h in all_hits if h['pred_zero'] and h['succ_zero'])

    p_pred = n_pred_zero / n_total if n_total > 0 else 0
    p_succ = n_succ_zero / n_total if n_total > 0 else 0
    p_both_z = n_both_zero / n_total if n_total > 0 else 0
    p_indep_z = p_pred * p_succ

    print(f"\nP(predecessor has zero | hit) = {n_pred_zero}/{n_total} = {p_pred:.4f}")
    print(f"P(successor has zero | hit) = {n_succ_zero}/{n_total} = {p_succ:.4f}")
    print(f"P(both have zeros | hit) = {n_both_zero}/{n_total} = {p_both_z:.4f}")
    print(f"P(pred)×P(succ) = {p_indep_z:.4f}")

    if p_indep_z > 0:
        ratio_z = p_both_z / p_indep_z
        print(f"\nRatio: P(both zeros) / [P(pred)×P(succ)] = {ratio_z:.4f}")

    # Breakdown by m
    print("\n" + "=" * 70)
    print("Breakdown by m (entry witness, exit witness, both)")
    print("=" * 70)

    print(f"\n{'m':>3} | {'Hits':>5} | {'Entry':>5} | {'Exit':>5} | {'Both':>5} | {'E&X Rate':>8}")
    print("-" * 50)

    for m in range(2, 28):
        m_hits = [h for h in all_hits if h['m'] == m]
        if not m_hits:
            continue
        n_m = len(m_hits)
        n_e = sum(1 for h in m_hits if h['entry_witness'])
        n_x = sum(1 for h in m_hits if h['exit_witness'])
        n_ex = sum(1 for h in m_hits if h['entry_witness'] and h['exit_witness'])
        rate = n_ex / n_m if n_m > 0 else 0
        print(f"{m:>3} | {n_m:>5} | {n_e:>5} | {n_x:>5} | {n_ex:>5} | {rate:>8.3f}")

    # Show individual hits
    print("\n" + "=" * 70)
    print("Individual Hit Analysis (first 20)")
    print("=" * 70)

    print(f"\n{'n':>5} | {'m':>3} | {'Prefix':>12} | {'E':>1} | {'X':>1} | {'P0':>2} | {'S0':>2}")
    print("-" * 45)

    for h in all_hits[:20]:
        e = 'Y' if h['entry_witness'] else 'N'
        x = 'Y' if h['exit_witness'] else 'N'
        p = 'Y' if h['pred_zero'] else 'N'
        s = 'Y' if h['succ_zero'] else 'N'
        print(f"{h['n']:>5} | {h['m']:>3} | {h['prefix'][:12]:>12} | {e:>1} | {x:>1} | {p:>2} | {s:>2}")

    # Check the 6 isolated hit candidates at m=3
    print("\n" + "=" * 70)
    print("Analysis of 6 Isolated Hit Candidates at m=3")
    print("=" * 70)

    candidates = ['152', '154', '215', '415', '521', '541']

    print(f"\n{'Prefix':>6} | {'Entry':>5} | {'Exit':>5} | {'Both':>5}")
    print("-" * 35)

    for c in candidates:
        e = has_entry_witness(c)
        x = has_exit_witness(c)
        both = e and x
        print(f"{c:>6} | {'Y' if e else 'N':>5} | {'Y' if x else 'N':>5} | {'Y' if both else 'N':>5}")

    # Summary
    print("\n" + "=" * 70)
    print("SUMMARY")
    print("=" * 70)

    print(f"\nEntry-Exit witness correlation ratio: {ratio:.4f}" if 'ratio' in dir() else "")

    if p_both < p_independent * 0.9:
        print("\n*** FINDING: Negative correlation detected ***")
        print("Entry and exit witnesses are LESS likely to co-occur than expected.")
        print("This could explain part of the 19-digit gap (model threshold m=46 vs empirical m=27).")
        gap_factor = p_independent / p_both if p_both > 0 else float('inf')
        print(f"Correlation explains a factor of {gap_factor:.2f}x reduction in E[isolated hits].")
    else:
        print("\n*** FINDING: No significant negative correlation ***")
        print("Entry and exit witnesses are roughly independent or positively correlated.")
        print("The 19-digit gap must be explained by other mechanisms.")

if __name__ == "__main__":
    main()
