"""
Experiment 44: Deterministic vs Existential Entry Analysis

GPT 21A's key insight: The 19-digit gap comes from the existential quantifier in E_{m,1}.
The model counts states where SOME predecessor has visible zero, but the orbit realizes
only ONE specific inverse branch.

This experiment tests the diagnostic ratio:
    κ_m = |E'_{m,1} ∩ X_{m,1}| / |E_{m,1} ∩ X_{m,1}|

where:
- E_{m,1} = states with entry witness (existential: some predecessor has zero)
- E'_{m,1} = states where THE ACTUAL predecessor has visible zero (deterministic)

If κ ≈ 1/3 around m=27, we've identified the mechanism for the 19-digit gap.
"""

import math

def is_zeroless(s):
    """Check if string has no '0' digit."""
    return '0' not in s

def has_entry_witness(prefix):
    """
    Check if prefix has entry witness: (2,4,6,8) followed by 1.
    This is the EXISTENTIAL condition: some predecessor could have had a zero.
    """
    for i in range(len(prefix) - 1):
        if prefix[i] in '2468' and prefix[i+1] == '1':
            return True
    return False

def has_exit_witness(prefix):
    """
    Check if prefix has exit witness: 5 followed by (1,2,3,4).
    This means the successor will have a zero.
    """
    for i in range(len(prefix) - 1):
        if prefix[i] == '5' and prefix[i+1] in '1234':
            return True
    return False

def actual_predecessor_has_zero(n, m):
    """
    Check if the ACTUAL predecessor 2^{n-1} has a zero in its visible prefix.
    This is the DETERMINISTIC condition.

    Key insight from GPT 21A: The existential model counts all states reachable
    from SOME predecessor with zero. But the orbit only realizes ONE predecessor.
    """
    if n <= 1:
        return False

    pred = 2 ** (n - 1)
    pred_str = str(pred)

    # The predecessor's visible window depends on normalization
    # If 2^n has m digits and 2^{n-1} has m-1 digits, the predecessor
    # "saw" a shorter window, but we compare on the same scale

    # Check if predecessor has zero in first m digits
    pred_prefix = pred_str[:m] if len(pred_str) >= m else pred_str
    return '0' in pred_prefix

def actual_successor_has_zero(n, m):
    """Check if the ACTUAL successor 2^{n+1} has a zero in its visible prefix."""
    succ = 2 ** (n + 1)
    succ_str = str(succ)
    succ_prefix = succ_str[:m] if len(succ_str) >= m else succ_str
    return '0' in succ_prefix

def find_transition_zone_hits(m, max_n=10000):
    """Find all n where 2^n has exactly m digits and is entirely zeroless."""
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
    Analyze a single hit for both existential and deterministic entry.
    """
    power = 2 ** n
    prefix = str(power)[:m]

    # Existential conditions (from pattern matching)
    entry_witness = has_entry_witness(prefix)  # E_{m,1}
    exit_witness = has_exit_witness(prefix)    # X_{m,1}

    # Deterministic conditions (from actual orbit)
    pred_zero = actual_predecessor_has_zero(n, m)  # E'_{m,1}
    succ_zero = actual_successor_has_zero(n, m)    # X'_{m,1}

    return {
        'n': n,
        'prefix': prefix,
        'entry_witness': entry_witness,    # Existential entry
        'exit_witness': exit_witness,      # Existential exit
        'pred_zero': pred_zero,            # Deterministic entry
        'succ_zero': succ_zero,            # Deterministic exit
    }

def main():
    print("=" * 70)
    print("Experiment 44: Deterministic vs Existential Entry Analysis")
    print("=" * 70)

    print("\nGPT 21A's diagnostic test:")
    print("If κ_m = |E' ∩ X| / |E ∩ X| ≈ 1/3, the inverse-branch mechanism explains the gap.")
    print("\nKey distinction:")
    print("  E_{m,1} = EXISTENTIAL: pattern '(2,4,6,8) followed by 1' exists")
    print("  E'_{m,1} = DETERMINISTIC: actual predecessor 2^{n-1} has visible zero")

    # Collect all hits
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

    # Compute the key ratios
    print("\n" + "=" * 70)
    print("EXISTENTIAL vs DETERMINISTIC Entry Comparison")
    print("=" * 70)

    n_total = len(all_hits)

    # Existential counts
    n_E = sum(1 for h in all_hits if h['entry_witness'])
    n_X = sum(1 for h in all_hits if h['exit_witness'])
    n_EX = sum(1 for h in all_hits if h['entry_witness'] and h['exit_witness'])

    # Deterministic counts
    n_E_prime = sum(1 for h in all_hits if h['pred_zero'])
    n_X_prime = sum(1 for h in all_hits if h['succ_zero'])
    n_EX_prime = sum(1 for h in all_hits if h['pred_zero'] and h['succ_zero'])

    # Mixed counts (deterministic entry + existential exit, etc.)
    n_E_prime_X = sum(1 for h in all_hits if h['pred_zero'] and h['exit_witness'])
    n_E_X_prime = sum(1 for h in all_hits if h['entry_witness'] and h['succ_zero'])

    print(f"\n{'Condition':<35} | {'Count':>6} | {'Rate':>8}")
    print("-" * 55)
    print(f"{'Total hits':<35} | {n_total:>6} | {'1.000':>8}")
    print()
    print(f"{'EXISTENTIAL entry (E)':<35} | {n_E:>6} | {n_E/n_total:.4f}")
    print(f"{'EXISTENTIAL exit (X)':<35} | {n_X:>6} | {n_X/n_total:.4f}")
    print(f"{'EXISTENTIAL both (E ∩ X)':<35} | {n_EX:>6} | {n_EX/n_total:.4f}")
    print()
    print(f"{'DETERMINISTIC entry (E-prime)':<35} | {n_E_prime:>6} | {n_E_prime/n_total:.4f}")
    print(f"{'DETERMINISTIC exit (X-prime)':<35} | {n_X_prime:>6} | {n_X_prime/n_total:.4f}")
    print(f"{'DETERMINISTIC both (E-prime & X-prime)':<35} | {n_EX_prime:>6} | {n_EX_prime/n_total:.4f}")
    print()
    print(f"{'MIXED: Det-entry + Exist-exit':<35} | {n_E_prime_X:>6} | {n_E_prime_X/n_total:.4f}")
    print(f"{'MIXED: Exist-entry + Det-exit':<35} | {n_E_X_prime:>6} | {n_E_X_prime/n_total:.4f}")

    # THE KEY DIAGNOSTIC RATIOS
    print("\n" + "=" * 70)
    print("KEY DIAGNOSTIC RATIOS (GPT 21A's Test)")
    print("=" * 70)

    if n_E > 0:
        kappa_E = n_E_prime / n_E
        print(f"\nκ_entry = |E'| / |E| = {n_E_prime}/{n_E} = {kappa_E:.4f}")
        if 0.25 <= kappa_E <= 0.40:
            print("  >>> IN TARGET RANGE (~1/3)! Inverse-branch mechanism plausible.")
        elif kappa_E < 0.25:
            print("  >>> BELOW target. More than 3 inverse regimes?")
        else:
            print("  >>> ABOVE target. Fewer than 3 inverse regimes?")

    if n_X > 0:
        kappa_X = n_X_prime / n_X
        print(f"\nκ_exit = |X'| / |X| = {n_X_prime}/{n_X} = {kappa_X:.4f}")

    if n_EX > 0:
        kappa_EX = n_EX_prime / n_EX
        print(f"\nκ_both = |E' ∩ X'| / |E ∩ X| = {n_EX_prime}/{n_EX} = {kappa_EX:.4f}")
        print("  (This is the most relevant ratio for isolated hits)")

    if n_EX > 0:
        kappa_mixed = n_E_prime_X / n_EX
        print(f"\nκ_mixed = |E' ∩ X| / |E ∩ X| = {n_E_prime_X}/{n_EX} = {kappa_mixed:.4f}")
        print("  (Deterministic entry + existential exit)")
        if 0.25 <= kappa_mixed <= 0.40:
            print("  >>> IN TARGET RANGE (~1/3)! This would explain the gap.")

    # Breakdown by m
    print("\n" + "=" * 70)
    print("Breakdown by m")
    print("=" * 70)

    print(f"\n{'m':>3} | {'Hits':>5} | {'E':>4} | {'Ep':>4} | {'X':>4} | {'Xp':>4} | {'E&X':>4} | {'Ep&X':>5} | {'kappa':>6}")
    print("-" * 70)

    for m in range(2, 28):
        m_hits = [h for h in all_hits if h['m'] == m]
        if not m_hits:
            continue

        n_m = len(m_hits)
        n_E_m = sum(1 for h in m_hits if h['entry_witness'])
        n_E_prime_m = sum(1 for h in m_hits if h['pred_zero'])
        n_X_m = sum(1 for h in m_hits if h['exit_witness'])
        n_X_prime_m = sum(1 for h in m_hits if h['succ_zero'])
        n_EX_m = sum(1 for h in m_hits if h['entry_witness'] and h['exit_witness'])
        n_E_prime_X_m = sum(1 for h in m_hits if h['pred_zero'] and h['exit_witness'])

        kappa_m = n_E_prime_X_m / n_EX_m if n_EX_m > 0 else float('nan')
        kappa_str = f"{kappa_m:.3f}" if n_EX_m > 0 else "N/A"

        print(f"{m:>3} | {n_m:>5} | {n_E_m:>4} | {n_E_prime_m:>4} | {n_X_m:>4} | {n_X_prime_m:>4} | {n_EX_m:>4} | {n_E_prime_X_m:>5} | {kappa_str:>6}")

    # Individual hit analysis
    print("\n" + "=" * 70)
    print("Individual Hit Analysis (showing E vs E' discrepancy)")
    print("=" * 70)

    # Find hits where E and E' differ
    discrepancies = [h for h in all_hits if h['entry_witness'] != h['pred_zero']]

    print(f"\nHits where EXISTENTIAL ≠ DETERMINISTIC entry: {len(discrepancies)}/{len(all_hits)}")
    print(f"\n{'n':>5} | {'m':>3} | {'Prefix':>15} | {'E':>1} | {'Ep':>2} | {'X':>1} | {'Xp':>2} | Note")
    print("-" * 70)

    for h in discrepancies[:25]:
        e = 'Y' if h['entry_witness'] else 'N'
        e_prime = 'Y' if h['pred_zero'] else 'N'
        x = 'Y' if h['exit_witness'] else 'N'
        x_prime = 'Y' if h['succ_zero'] else 'N'

        if h['entry_witness'] and not h['pred_zero']:
            note = "E but not E': pattern exists but pred zeroless"
        elif h['pred_zero'] and not h['entry_witness']:
            note = "E' but not E: pred has zero but no pattern"
        else:
            note = ""

        print(f"{h['n']:>5} | {h['m']:>3} | {h['prefix'][:15]:>15} | {e:>1} | {e_prime:>2} | {x:>1} | {x_prime:>2} | {note}")

    # Summary
    print("\n" + "=" * 70)
    print("SUMMARY")
    print("=" * 70)

    if n_EX > 0 and n_E_prime_X > 0:
        kappa_mixed = n_E_prime_X / n_EX
        print(f"\n*** KEY FINDING ***")
        print(f"\nκ_mixed = |E' ∩ X| / |E ∩ X| = {kappa_mixed:.4f}")

        if 0.25 <= kappa_mixed <= 0.40:
            print("\n>>> RESULT: κ ≈ 1/3 - GPT 21A's inverse-branch mechanism is CONFIRMED!")
            print("The 19-digit gap is explained by the existential quantifier overcounting.")
            print("There are ~3 inverse regimes, only 1 supports true entry-from-zero.")
        elif kappa_mixed < 0.25:
            print("\n>>> RESULT: κ < 1/3 - More than 3 inverse regimes, or other mechanism.")
        elif kappa_mixed > 0.5:
            print("\n>>> RESULT: κ > 1/2 - Inverse-branch mechanism is too weak to explain the gap.")
            print("Other factors must contribute to the 19-digit gap.")
        else:
            print("\n>>> RESULT: κ between 1/3 and 1/2 - Partial support for inverse-branch mechanism.")

    # Also check if E' is much smaller than E
    if n_E > 0:
        reduction = 1 - n_E_prime / n_E
        print(f"\nEntry reduction: E' is {reduction*100:.1f}% smaller than E")
        print(f"  (Existential overcounts deterministic by factor {n_E/n_E_prime:.2f})" if n_E_prime > 0 else "")

if __name__ == "__main__":
    main()
