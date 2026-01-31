"""
Experiment 53: Does the Arithmetic Constraint Generalize?

At depth 3, E∩X cylinders (521, 541) are unreachable because
their predecessors contain zeros.

Question: Does this pattern hold at deeper levels?
- Find all E∩X cylinders at depth 4, 5
- Check if they have zeroless predecessors
- Determine if arithmetic constraint explains all E∩X avoidance
"""

from itertools import product

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

def find_zeroless_predecessor(target, max_extra_digits=3):
    """
    Find if there exists a zeroless N such that 2*N starts with target.

    Returns the predecessor if found, None otherwise.
    """
    target_int = int(target)
    target_len = len(target)

    # 2*N starts with target means:
    # target * 10^k <= 2*N < (target+1) * 10^k
    # target/2 * 10^k <= N < (target+1)/2 * 10^k

    for extra in range(max_extra_digits + 1):
        scale = 10 ** extra
        lower = (target_int * scale) // 2
        upper = ((target_int + 1) * scale) // 2

        for n in range(lower, upper + 1):
            doubled = 2 * n
            doubled_str = str(doubled)
            if doubled_str.startswith(target) and is_zeroless(str(n)):
                return n

    return None

def main():
    print("=" * 70)
    print("Experiment 53: Deep E∩X Reachability")
    print("=" * 70)

    for depth in [3, 4, 5]:
        print(f"\n" + "=" * 70)
        print(f"Depth {depth}")
        print("=" * 70)

        # Find all E∩X cylinders
        ex_cylinders = []
        for digits in product(range(1, 10), repeat=depth):
            cyl = ''.join(str(d) for d in digits)
            if has_entry_witness(cyl) and has_exit_witness(cyl):
                ex_cylinders.append(cyl)

        print(f"\nTotal E∩X cylinders: {len(ex_cylinders)}")

        if len(ex_cylinders) == 0:
            print("  (none)")
            continue

        # Check reachability for each
        reachable = []
        unreachable = []

        for cyl in ex_cylinders:
            pred = find_zeroless_predecessor(cyl)
            if pred is not None:
                reachable.append((cyl, pred))
            else:
                unreachable.append(cyl)

        print(f"Reachable (have zeroless predecessor): {len(reachable)}")
        print(f"Unreachable (no zeroless predecessor): {len(unreachable)}")

        if reachable:
            print(f"\n  Reachable E∩X cylinders:")
            for cyl, pred in reachable[:10]:
                print(f"    {cyl} <- 2*{pred} = {2*pred}")

        if unreachable:
            print(f"\n  Unreachable E∩X cylinders:")
            for cyl in unreachable[:10]:
                # Show why unreachable
                target_int = int(cyl)
                approx_pred = target_int / 2
                print(f"    {cyl}: predecessor ~{approx_pred:.1f}...")

        # Summary
        if len(reachable) == 0:
            print(f"\n  >>> ALL E∩X cylinders at depth {depth} are UNREACHABLE!")
            print(f"  >>> Arithmetic constraint fully explains avoidance.")
        else:
            print(f"\n  >>> {len(reachable)}/{len(ex_cylinders)} E∩X cylinders ARE reachable")
            print(f"  >>> Arithmetic constraint is PARTIAL at depth {depth}")

    # =========================================================================
    # SYNTHESIS
    # =========================================================================

    print("\n" + "=" * 70)
    print("SYNTHESIS")
    print("=" * 70)

    print("""
At depth 3: 2 E∩X cylinders, 0 reachable (100% blocked by arithmetic)
At depth 4: ? E∩X cylinders, ? reachable
At depth 5: ? E∩X cylinders, ? reachable

If arithmetic blocks ALL E∩X at all depths:
  -> The model's E∩X count is entirely fictitious
  -> There's no "correction factor" - the count should be ZERO

If arithmetic blocks SOME E∩X at larger depths:
  -> The constraint weakens as depth increases
  -> Eventually E∩X becomes possible (we know this happens at m~12+)
  -> The "separation constraint" becomes the relevant correction
""")

if __name__ == "__main__":
    main()
