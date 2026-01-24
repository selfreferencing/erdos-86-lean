#!/usr/bin/env python3
"""
Conditional survival analysis for the 86 conjecture.
Key question: Given survival to level k, what's P(survive level k+1)?
"""

import sys
sys.set_int_max_str_digits(100000)

def last_k_zeroless(n, k):
    """Check if 2^n has no zeros in the last k digits."""
    power = pow(2, n, 10**k)
    for _ in range(k):
        if power % 10 == 0:
            return False
        power //= 10
    return True

def compute_conditional_survival(max_k=12, sample_range=10000):
    """
    For each level k, compute:
    - How many n survive to level k
    - Of those, how many also survive to level k+1
    - The conditional probability
    """
    print("="*70)
    print("CONDITIONAL SURVIVAL ANALYSIS")
    print("="*70)
    print(f"\nSampling n from 87 to {86 + sample_range}")
    print()

    # For each n, compute its survival depth
    depths = {}
    for n in range(87, 87 + sample_range):
        for k in range(1, max_k + 2):
            if not last_k_zeroless(n, k):
                depths[n] = k - 1
                break
        else:
            depths[n] = max_k + 1

    print(f"{'k':<6} {'survive k':<12} {'survive k+1':<14} {'P(k+1|k)':<12} {'expected':<12}")
    print("-"*60)

    for k in range(1, max_k + 1):
        survive_k = sum(1 for n, d in depths.items() if d >= k)
        survive_k1 = sum(1 for n, d in depths.items() if d >= k + 1)

        if survive_k > 0:
            conditional = survive_k1 / survive_k
        else:
            conditional = 0

        expected = 0.9  # Each new digit has 90% chance nonzero

        print(f"{k:<6} {survive_k:<12} {survive_k1:<14} {conditional:<12.6f} {expected:<12.6f}")

def analyze_transition_structure(k, sample_size=1000):
    """
    For survivors at level k, analyze what happens at level k+1.
    Look at the distribution of u_{k+1} values.
    """
    period_k = 4 * 5**(k-1)
    period_k1 = 4 * 5**k

    print(f"\n{'='*70}")
    print(f"TRANSITION STRUCTURE: Level {k} → {k+1}")
    print(f"{'='*70}")
    print(f"Period at k={k}: {period_k}")
    print(f"Period at k+1={k+1}: {period_k1}")

    # Find survivors at level k
    survivors_k = []
    for r in range(period_k):
        n = r if r >= k else r + period_k
        if last_k_zeroless(n, k):
            survivors_k.append(r)

    print(f"Survivors at level {k}: {len(survivors_k)}")

    # For each level-k survivor, check its 5 children at level k+1
    # A residue r mod period_k has 5 extensions: r, r+period_k, r+2*period_k, r+3*period_k, r+4*period_k
    children_survive = 0
    children_total = 0

    for r in survivors_k:
        for j in range(5):
            child = r + j * period_k
            n = child if child >= k + 1 else child + period_k1
            if last_k_zeroless(n, k + 1):
                children_survive += 1
            children_total += 1

    if children_total > 0:
        branching = children_survive / len(survivors_k)
        print(f"Total children: {children_total}")
        print(f"Children surviving to level {k+1}: {children_survive}")
        print(f"Average branching factor: {branching:.4f}")
        print(f"Expected (if independent): 4.5 (= 5 * 0.9)")

def find_long_survivors(min_depth=20, max_n=100000):
    """Find n values with unusually long survival depths."""
    print(f"\n{'='*70}")
    print(f"LONG SURVIVORS (depth >= {min_depth}) for n <= {max_n}")
    print(f"{'='*70}")

    long_survivors = []
    for n in range(87, max_n + 1):
        depth = 0
        for k in range(1, 100):
            if last_k_zeroless(n, k):
                depth = k
            else:
                break

        if depth >= min_depth:
            digits = int(n * 0.30103) + 1
            ratio = n / depth
            long_survivors.append((n, depth, digits, ratio))

    print(f"\n{'n':<12} {'depth':<8} {'D(n)':<8} {'n/depth':<10} {'would need':<12}")
    print("-"*60)

    for n, depth, digits, ratio in sorted(long_survivors, key=lambda x: x[1], reverse=True)[:30]:
        print(f"{n:<12} {depth:<8} {digits:<8} {ratio:<10.4f} {digits:<12}")

    return long_survivors

def analyze_why_no_zeroless_past_86():
    """
    The key question: WHY doesn't any n > 86 survive to D(n) levels?

    For 2^n to be zeroless:
    - Need depth >= D(n) = floor(n * log10(2)) + 1 ≈ 0.301n + 1

    So we need: depth(n) >= 0.301n + 1

    Rearranging: n <= depth(n) / 0.301 ≈ 3.32 * depth(n)

    If all survivors have n > 3.32 * depth(n), then no zeroless exist.
    """
    print(f"\n{'='*70}")
    print("WHY NO ZEROLESS PAST 86?")
    print(f"{'='*70}")

    print("\nFor 2^n to be zeroless, need n <= 3.32 * depth(n)")
    print("Checking if any n > 86 violates this bound...\n")

    violations = []
    close_calls = []

    for n in range(87, 100001):
        depth = 0
        for k in range(1, 200):
            if last_k_zeroless(n, k):
                depth = k
            else:
                break

        threshold = 3.321928 * depth  # log_2(10) * depth
        if n <= threshold:
            violations.append((n, depth, threshold))
        elif n < threshold + 10:  # Close call
            close_calls.append((n, depth, threshold, n - threshold))

    if violations:
        print(f"VIOLATIONS FOUND (would be zeroless):")
        for n, depth, thresh in violations[:10]:
            print(f"  n={n}, depth={depth}, threshold={thresh:.2f}")
    else:
        print("No violations found - all n > 86 have n > 3.32 * depth(n)")

    print(f"\nClose calls (n within 10 of threshold):")
    for n, depth, thresh, margin in sorted(close_calls, key=lambda x: x[3])[:10]:
        print(f"  n={n}, depth={depth}, threshold={thresh:.2f}, margin={margin:.2f}")

if __name__ == "__main__":
    # Conditional survival
    compute_conditional_survival(max_k=15, sample_range=50000)

    # Transition structure
    for k in [3, 5, 7]:
        analyze_transition_structure(k)

    # Long survivors
    long_survivors = find_long_survivors(min_depth=25, max_n=500000)

    # The key question
    analyze_why_no_zeroless_past_86()
