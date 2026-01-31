"""
Experiment 55: Find the Transition Depth for E∩X Reachability

GPT 23A suggested: compute in-degree in G_m for E∩X cylinders at m=6..11
to find the exact depth where E∩X becomes arithmetically possible.

We know:
- m=3,4,5: 0% of E∩X cylinders are reachable (100% blocked)
- m≥12: E∩X occurs in actual hits

Question: At what depth does E∩X first become arithmetically possible?
"""

from itertools import product

def is_zeroless(s):
    return '0' not in s

def has_entry_witness(prefix):
    """Entry witness: even followed by 1."""
    for i in range(len(prefix) - 1):
        if prefix[i] in '2468' and prefix[i+1] == '1':
            return True
    return False

def has_exit_witness(prefix):
    """Exit witness: 5 followed by 1,2,3,4."""
    for i in range(len(prefix) - 1):
        if prefix[i] == '5' and prefix[i+1] in '1234':
            return True
    return False

def find_zeroless_predecessor(target, max_extra_digits=4):
    """
    Find if there exists a zeroless N such that 2*N starts with target.

    Checks scales k=0,1,2,...,max_extra_digits.
    Returns the predecessor if found, None otherwise.
    """
    target_int = int(target)

    for extra in range(max_extra_digits + 1):
        scale = 10 ** extra
        # 2*N starts with target means N ∈ [target*scale/2, (target+1)*scale/2)
        lower = (target_int * scale + 1) // 2  # ceil
        upper = ((target_int + 1) * scale) // 2  # floor

        for n in range(lower, upper + 1):
            n_str = str(n)
            if is_zeroless(n_str):
                # Verify: does 2*n start with target?
                doubled = str(2 * n)
                if doubled.startswith(target):
                    return n

    return None

def enumerate_EX_cylinders(depth):
    """Generate all E∩X cylinders at given depth."""
    for digits in product(range(1, 10), repeat=depth):
        cyl = ''.join(str(d) for d in digits)
        if has_entry_witness(cyl) and has_exit_witness(cyl):
            yield cyl

def count_EX_cylinders(depth):
    """Count E∩X cylinders at given depth."""
    count = 0
    for digits in product(range(1, 10), repeat=depth):
        cyl = ''.join(str(d) for d in digits)
        if has_entry_witness(cyl) and has_exit_witness(cyl):
            count += 1
    return count

def main():
    print("=" * 70)
    print("Experiment 55: Transition Depth for E∩X Reachability")
    print("=" * 70)

    print("""
Question: At what depth does E∩X first become arithmetically possible?

For each depth m, we check every E∩X cylinder to see if it has
a zeroless predecessor (i.e., non-zero in-degree in the transition graph).
""")

    results = []

    for depth in range(3, 12):
        print(f"\n--- Depth {depth} ---")

        # Count total E∩X cylinders
        total_ex = count_EX_cylinders(depth)
        print(f"  Total E∩X cylinders: {total_ex}")

        if total_ex == 0:
            print("  (none)")
            results.append({'depth': depth, 'total': 0, 'reachable': 0})
            continue

        if total_ex > 50000:
            print(f"  (too many to check exhaustively, sampling...)")
            # Sample approach for large depths
            reachable_count = 0
            checked = 0
            reachable_examples = []

            for cyl in enumerate_EX_cylinders(depth):
                if checked >= 1000:  # Check first 1000
                    break
                pred = find_zeroless_predecessor(cyl, max_extra_digits=3)
                if pred is not None:
                    reachable_count += 1
                    if len(reachable_examples) < 5:
                        reachable_examples.append((cyl, pred))
                checked += 1

            print(f"  Checked: {checked}")
            print(f"  Reachable in sample: {reachable_count}")
            if reachable_examples:
                print(f"  Examples:")
                for cyl, pred in reachable_examples:
                    print(f"    {cyl} <- 2*{pred} = {2*pred}")

            results.append({'depth': depth, 'total': total_ex,
                          'reachable': reachable_count, 'checked': checked})
        else:
            # Exhaustive check
            reachable_count = 0
            reachable_examples = []

            for cyl in enumerate_EX_cylinders(depth):
                pred = find_zeroless_predecessor(cyl, max_extra_digits=3)
                if pred is not None:
                    reachable_count += 1
                    if len(reachable_examples) < 5:
                        reachable_examples.append((cyl, pred))

            print(f"  Reachable: {reachable_count}/{total_ex} ({100*reachable_count/total_ex:.1f}%)")

            if reachable_examples:
                print(f"  First reachable E∩X cylinders:")
                for cyl, pred in reachable_examples:
                    print(f"    {cyl} <- 2*{pred} = {2*pred}")

            results.append({'depth': depth, 'total': total_ex, 'reachable': reachable_count})

            if reachable_count > 0 and all(r.get('reachable', 0) == 0 for r in results[:-1]):
                print(f"\n  >>> TRANSITION DEPTH FOUND: m = {depth}")
                print(f"  >>> First depth where E∩X is arithmetically possible!")

    # Summary
    print("\n" + "=" * 70)
    print("SUMMARY: Transition Depth")
    print("=" * 70)

    print(f"\n{'Depth':>6} | {'E∩X Total':>12} | {'Reachable':>12} | {'Blocked %':>10}")
    print("-" * 50)

    transition_found = None
    for r in results:
        depth = r['depth']
        total = r['total']
        reachable = r.get('reachable', 0)
        checked = r.get('checked', total)

        if total > 0:
            blocked_pct = 100 * (1 - reachable / checked)
            print(f"{depth:>6} | {total:>12} | {reachable:>12} | {blocked_pct:>9.1f}%")

            if reachable > 0 and transition_found is None:
                transition_found = depth
        else:
            print(f"{depth:>6} | {total:>12} | {'N/A':>12} | {'N/A':>10}")

    if transition_found:
        print(f"\n*** TRANSITION DEPTH: m = {transition_found} ***")
        print(f"    E∩X becomes arithmetically possible at depth {transition_found}.")
    else:
        print(f"\n*** E∩X remains 100% blocked through depth {results[-1]['depth']} ***")

if __name__ == "__main__":
    main()
