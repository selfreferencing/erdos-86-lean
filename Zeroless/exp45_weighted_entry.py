"""
Experiment 45: Weighted Entry Operator (π_E) Computation

GPT 21A/21B's key insight: The existential entry set E_{m,1} overcounts by ~3×
because the inverse doubling map branches into ~3 carry/normalization regimes,
but the orbit realizes only one.

This experiment computes:
    π_E(A) = P(true predecessor has visible zero | state A)
           = weight of zero-predecessor branches / total branch weight

If average(π_E) ≈ 1/3 over E ∩ X, we've identified the mechanism.

The inverse doubling transducer:
- Given output digit d_out with carry_out, what inputs could produce it?
- 2 × d_in + carry_in = d_out + 10 × carry_out
- So d_in = (d_out + 10 × carry_out - carry_in) / 2
- Requires result to be integer in [0,9]
"""

import math
from itertools import product

def inverse_double_digit(d_out, carry_out):
    """
    Given output digit d_out and outgoing carry carry_out,
    find all valid (d_in, carry_in) pairs.

    Equation: 2 * d_in + carry_in = d_out + 10 * carry_out
    """
    target = d_out + 10 * carry_out
    solutions = []

    for carry_in in [0, 1]:
        if (target - carry_in) % 2 == 0:
            d_in = (target - carry_in) // 2
            if 0 <= d_in <= 9:
                solutions.append((d_in, carry_in))

    return solutions

def build_inverse_transducer():
    """
    Build the inverse doubling transducer.

    For each (d_out, carry_out), list all (d_in, carry_in) pairs.
    """
    transducer = {}
    for d_out in range(10):
        for carry_out in [0, 1]:
            transducer[(d_out, carry_out)] = inverse_double_digit(d_out, carry_out)
    return transducer

def enumerate_predecessors(prefix, transducer):
    """
    Given an m-digit zeroless prefix, enumerate all possible predecessor prefixes.

    A predecessor is valid if we can find a consistent carry chain.
    We track: (predecessor_prefix, final_carry_in)

    The carry_out from position i becomes carry_in to position i-1.
    We start from the rightmost digit and work left.
    """
    m = len(prefix)
    digits = [int(d) for d in prefix]

    # We'll enumerate all consistent predecessor sequences
    # State: list of (predecessor_digit, carry_in) for each position
    # Work from right to left

    # For each possible final carry_out (into position beyond our window)
    predecessors = []

    for final_carry_out in [0, 1]:
        # Build predecessors position by position from right to left
        # partial_preds[i] = list of (pred_digits[i:], carry_into_pos_i)

        # Start at rightmost position (index m-1)
        # carry_out from this position is final_carry_out
        partial = []

        for d_in, carry_in in transducer[(digits[m-1], final_carry_out)]:
            partial.append(([d_in], carry_in))

        # Work leftward
        for pos in range(m-2, -1, -1):
            new_partial = []
            for pred_so_far, carry_out_from_next in partial:
                # carry_out from position pos+1 = carry_in to position pos
                # But we need carry_out FROM position pos
                # The carry_out_from_next is actually the carry_in to pos+1
                # which equals carry_out from pos

                # Wait, let me think about this more carefully.
                # At position i, we have d_out[i] and we need to find d_in[i].
                # The carry_out from position i goes to position i-1.
                # The carry_in to position i comes from position i+1.

                # So when processing from right to left:
                # - We already determined carry_in for the previous (rightward) position
                # - That carry_in equals carry_out from the current position
                # - We need to find d_in and carry_in for current position

                carry_out = carry_out_from_next  # carry_out from pos = carry_in to pos+1

                for d_in, carry_in in transducer[(digits[pos], carry_out)]:
                    new_partial.append(([d_in] + pred_so_far, carry_in))

            partial = new_partial
            if not partial:
                break

        # Each element in partial is now (full_predecessor, carry_in_to_first_digit)
        for pred_digits, carry_in_first in partial:
            pred_str = ''.join(str(d) for d in pred_digits)
            predecessors.append({
                'prefix': pred_str,
                'carry_in_first': carry_in_first,
                'final_carry_out': final_carry_out,
                'has_zero': '0' in pred_str
            })

    return predecessors

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

def is_zeroless(s):
    """Check if string has no '0' digit."""
    return '0' not in s

def compute_pi_E(prefix, transducer):
    """
    Compute π_E(prefix) = weighted probability that true predecessor has zero.

    Weight each predecessor branch equally (uniform prior on hidden state).
    """
    predecessors = enumerate_predecessors(prefix, transducer)

    if not predecessors:
        return 0.0, 0, 0

    total_weight = len(predecessors)
    zero_weight = sum(1 for p in predecessors if p['has_zero'])

    return zero_weight / total_weight, zero_weight, total_weight

def enumerate_zeroless_prefixes(m, max_count=10000):
    """Enumerate all m-digit zeroless prefixes (up to max_count)."""
    if m <= 6:
        # Full enumeration for small m
        prefixes = []
        for first_digit in range(1, 10):  # First digit 1-9
            for rest in product(range(1, 10), repeat=m-1):
                prefix = str(first_digit) + ''.join(str(d) for d in rest)
                prefixes.append(prefix)
        return prefixes
    else:
        # Sample for larger m
        import random
        random.seed(42)
        prefixes = []
        for _ in range(max_count):
            prefix = ''.join(str(random.randint(1, 9)) for _ in range(m))
            prefixes.append(prefix)
        return prefixes

def main():
    print("=" * 70)
    print("Experiment 45: Weighted Entry Operator (π_E) Computation")
    print("=" * 70)

    print("\nGPT 21A/21B hypothesis:")
    print("The existential entry set E_{m,1} overcounts by ~3× because")
    print("the inverse doubling map has ~3 branches, only ~1/3 have zero predecessor.")
    print("\nIf average(π_E) ≈ 1/3 over E ∩ X, we've found the mechanism.")

    # Build the inverse transducer
    transducer = build_inverse_transducer()

    print("\n" + "=" * 70)
    print("Inverse Doubling Transducer")
    print("=" * 70)

    print("\nFor each (output_digit, carry_out), valid (input_digit, carry_in):")
    for d_out in range(10):
        for carry_out in [0, 1]:
            solutions = transducer[(d_out, carry_out)]
            sol_str = ", ".join(f"({d},{c})" for d, c in solutions)
            print(f"  ({d_out}, {carry_out}) <- {sol_str}")

    # Analyze for various m
    print("\n" + "=" * 70)
    print("π_E Analysis by m")
    print("=" * 70)

    results_by_m = {}

    for m in range(2, 8):
        print(f"\n--- m = {m} ---")

        prefixes = enumerate_zeroless_prefixes(m)
        print(f"Total zeroless {m}-digit prefixes: {len(prefixes)}")

        # Compute π_E for each prefix
        pi_E_values = []
        e_and_x_prefixes = []
        e_only_prefixes = []
        x_only_prefixes = []

        for prefix in prefixes:
            pi_E, zero_count, total_count = compute_pi_E(prefix, transducer)
            has_E = has_entry_witness(prefix)
            has_X = has_exit_witness(prefix)

            pi_E_values.append({
                'prefix': prefix,
                'pi_E': pi_E,
                'zero_count': zero_count,
                'total_branches': total_count,
                'has_E': has_E,
                'has_X': has_X
            })

            if has_E and has_X:
                e_and_x_prefixes.append(pi_E_values[-1])
            elif has_E:
                e_only_prefixes.append(pi_E_values[-1])
            elif has_X:
                x_only_prefixes.append(pi_E_values[-1])

        # Statistics
        n_E = sum(1 for p in pi_E_values if p['has_E'])
        n_X = sum(1 for p in pi_E_values if p['has_X'])
        n_EX = len(e_and_x_prefixes)

        print(f"  With entry witness (E): {n_E}")
        print(f"  With exit witness (X): {n_X}")
        print(f"  With both (E ∩ X): {n_EX}")

        if n_EX > 0:
            avg_pi_E_EX = sum(p['pi_E'] for p in e_and_x_prefixes) / n_EX
            print(f"\n  *** Average π_E over E ∩ X: {avg_pi_E_EX:.4f} ***")

            if 0.25 <= avg_pi_E_EX <= 0.40:
                print(f"  >>> IN TARGET RANGE (~1/3)! Mechanism confirmed.")
            elif avg_pi_E_EX < 0.25:
                print(f"  >>> Below 1/3 - even stronger suppression")
            else:
                print(f"  >>> Above 1/3 - weaker suppression than needed")

            results_by_m[m] = {
                'n_prefixes': len(prefixes),
                'n_E': n_E,
                'n_X': n_X,
                'n_EX': n_EX,
                'avg_pi_E': avg_pi_E_EX
            }

        # Show some examples
        if n_EX > 0 and m <= 4:
            print(f"\n  Sample E ∩ X prefixes:")
            for p in e_and_x_prefixes[:5]:
                print(f"    {p['prefix']}: π_E = {p['pi_E']:.3f} ({p['zero_count']}/{p['total_branches']} branches with zero)")

        # Also compute average π_E over all prefixes with E (not just E ∩ X)
        if n_E > 0:
            e_prefixes = [p for p in pi_E_values if p['has_E']]
            avg_pi_E_E = sum(p['pi_E'] for p in e_prefixes) / n_E
            print(f"\n  Average π_E over E (entry witness): {avg_pi_E_E:.4f}")

    # Summary table
    print("\n" + "=" * 70)
    print("SUMMARY: Average π_E over E ∩ X by m")
    print("=" * 70)

    print(f"\n{'m':>3} | {'|E∩X|':>8} | {'avg π_E':>10} | {'Target ~1/3':>12}")
    print("-" * 45)

    for m, data in sorted(results_by_m.items()):
        target_check = "✓" if 0.25 <= data['avg_pi_E'] <= 0.40 else ""
        print(f"{m:>3} | {data['n_EX']:>8} | {data['avg_pi_E']:>10.4f} | {target_check:>12}")

    # Detailed branch analysis for small examples
    print("\n" + "=" * 70)
    print("Detailed Branch Analysis (m=3 examples)")
    print("=" * 70)

    # Known isolated hit candidates at m=3
    candidates = ['152', '154', '215', '415', '521', '541']

    print("\nKnown m=3 isolated hit candidates:")
    for prefix in candidates:
        predecessors = enumerate_predecessors(prefix, transducer)
        pi_E, zero_count, total = compute_pi_E(prefix, transducer)
        has_E = has_entry_witness(prefix)
        has_X = has_exit_witness(prefix)

        print(f"\n  {prefix}: E={'Y' if has_E else 'N'}, X={'Y' if has_X else 'N'}, π_E={pi_E:.3f}")
        print(f"    Total branches: {total}, with zero predecessor: {zero_count}")

        for p in predecessors[:4]:
            zero_mark = " [ZERO]" if p['has_zero'] else ""
            print(f"      <- {p['prefix']} (c_in={p['carry_in_first']}, c_out={p['final_carry_out']}){zero_mark}")
        if len(predecessors) > 4:
            print(f"      ... and {len(predecessors)-4} more")

    # Final summary
    print("\n" + "=" * 70)
    print("CONCLUSION")
    print("=" * 70)

    if results_by_m:
        avg_overall = sum(d['avg_pi_E'] for d in results_by_m.values()) / len(results_by_m)
        print(f"\nOverall average π_E across all m: {avg_overall:.4f}")

        if 0.25 <= avg_overall <= 0.40:
            print("\n*** MECHANISM CONFIRMED ***")
            print("The inverse-branch hypothesis explains the 19-digit gap.")
            print(f"Average π_E ≈ {avg_overall:.2f} means the existential entry set")
            print(f"overcounts by factor ~{1/avg_overall:.1f}.")
            print(f"This would shift threshold from m=46 to m≈{46 - int(19 * avg_overall / 0.33)}.")
        elif avg_overall > 0.5:
            print("\n*** MECHANISM NOT CONFIRMED ***")
            print("π_E is too high - inverse-branch alone doesn't explain the gap.")
            print("Other factors must contribute.")
        else:
            print("\n*** STRONGER EFFECT THAN EXPECTED ***")
            print(f"π_E ≈ {avg_overall:.2f} suggests even more suppression than ~1/3.")

if __name__ == "__main__":
    main()
