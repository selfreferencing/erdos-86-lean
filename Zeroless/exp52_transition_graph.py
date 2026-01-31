"""
Experiment 52: Cylinder Transition Graph

Question: Can the orbit EVER reach E∩X cylinders (521, 541)?

Method:
1. Build the 3-digit cylinder transition graph: A -> B if doubling a number
   starting with A can produce a number starting with B
2. Check if 521 and 541 are reachable from the initial cylinders
3. Identify the reachable set and compare to hit cylinders
"""

from collections import defaultdict, deque

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

def get_transition_targets(cylinder, extra_digits=2):
    """
    Given a 3-digit cylinder ABC, find all possible 3-digit cylinders
    that 2*ABCXY... could start with (for various continuations XY...).

    We check continuations with 'extra_digits' additional digits.
    """
    targets = set()

    # Try all possible continuations
    base = int(cylinder)
    for continuation in range(10 ** extra_digits):
        # Form the number ABC followed by continuation digits
        num = base * (10 ** extra_digits) + continuation
        doubled = 2 * num
        doubled_str = str(doubled)

        if len(doubled_str) >= 3:
            prefix = doubled_str[:3]
            if is_zeroless(prefix):
                targets.add(prefix)

    return targets

def build_transition_graph(depth=3, extra_digits=2):
    """Build the transition graph for all zeroless cylinders."""

    # All zeroless 3-digit cylinders
    cylinders = []
    for a in range(1, 10):
        for b in range(1, 10):
            for c in range(1, 10):
                cylinders.append(f"{a}{b}{c}")

    # Build adjacency list
    graph = defaultdict(set)

    for cyl in cylinders:
        targets = get_transition_targets(cyl, extra_digits)
        for t in targets:
            graph[cyl].add(t)

    return graph, cylinders

def find_reachable(graph, start_set, max_steps=100):
    """BFS to find all cylinders reachable from start_set."""
    reachable = set(start_set)
    frontier = deque(start_set)

    steps = 0
    while frontier and steps < max_steps:
        steps += 1
        next_frontier = []
        while frontier:
            current = frontier.popleft()
            for neighbor in graph[current]:
                if neighbor not in reachable:
                    reachable.add(neighbor)
                    next_frontier.append(neighbor)
        frontier = deque(next_frontier)

    return reachable

def get_initial_cylinders():
    """Get the 3-digit prefixes of the first several powers of 2."""
    initial = set()
    for n in range(1, 100):
        s = str(2**n)
        if len(s) >= 3:
            prefix = s[:3]
            if is_zeroless(prefix):
                initial.add(prefix)
    return initial

def main():
    print("=" * 70)
    print("Experiment 52: Cylinder Transition Graph")
    print("=" * 70)

    # =========================================================================
    # PART A: Build the transition graph
    # =========================================================================

    print("\n" + "=" * 70)
    print("PART A: Building Transition Graph")
    print("=" * 70)

    graph, all_cylinders = build_transition_graph(depth=3, extra_digits=2)

    print(f"\nTotal zeroless 3-digit cylinders: {len(all_cylinders)}")

    # Count edges
    total_edges = sum(len(targets) for targets in graph.values())
    print(f"Total transitions: {total_edges}")
    print(f"Average out-degree: {total_edges / len(all_cylinders):.2f}")

    # =========================================================================
    # PART B: Check E∩X cylinder reachability
    # =========================================================================

    print("\n" + "=" * 70)
    print("PART B: E∩X Cylinder Reachability")
    print("=" * 70)

    ex_cylinders = ['521', '541']

    for cyl in ex_cylinders:
        print(f"\n--- Cylinder {cyl} ---")

        # What can reach 521/541?
        predecessors = [c for c in all_cylinders if cyl in graph[c]]
        print(f"  Predecessors (cylinders that can transition to {cyl}): {len(predecessors)}")
        if predecessors:
            print(f"    Examples: {predecessors[:10]}")

        # What can 521/541 reach?
        successors = list(graph[cyl])
        print(f"  Successors (cylinders reachable from {cyl}): {len(successors)}")
        if successors:
            print(f"    Examples: {successors[:10]}")

    # =========================================================================
    # PART C: Forward reachability from actual orbit
    # =========================================================================

    print("\n" + "=" * 70)
    print("PART C: Forward Reachability from Actual Orbit")
    print("=" * 70)

    # Get initial cylinders from actual powers of 2
    initial = get_initial_cylinders()
    print(f"\nInitial cylinders (from 2^n, n=1..99): {len(initial)}")
    print(f"  Cylinders: {sorted(initial)}")

    # Find all reachable cylinders
    reachable = find_reachable(graph, initial)
    print(f"\nReachable cylinders (BFS from initial): {len(reachable)}")

    # Check if E∩X cylinders are reachable
    print(f"\nE∩X cylinder reachability:")
    for cyl in ex_cylinders:
        status = "REACHABLE" if cyl in reachable else "NOT REACHABLE"
        print(f"  {cyl}: {status}")

    # =========================================================================
    # PART D: Compare reachable vs actually hit
    # =========================================================================

    print("\n" + "=" * 70)
    print("PART D: Reachable vs Actually Hit")
    print("=" * 70)

    # Get actually hit cylinders
    hit_cylinders = set()
    for n in range(1, 500):
        s = str(2**n)
        if len(s) >= 3 and is_zeroless(s):
            hit_cylinders.add(s[:3])
        if len(s) > 30:
            break

    print(f"\nActually hit cylinders: {len(hit_cylinders)}")
    print(f"Graph-reachable cylinders: {len(reachable)}")

    hit_and_reachable = hit_cylinders & reachable
    hit_not_reachable = hit_cylinders - reachable
    reachable_not_hit = reachable - hit_cylinders

    print(f"\nHit AND reachable: {len(hit_and_reachable)}")
    print(f"Hit but NOT reachable: {len(hit_not_reachable)}")
    if hit_not_reachable:
        print(f"  These: {sorted(hit_not_reachable)}")

    print(f"Reachable but NOT hit: {len(reachable_not_hit)}")
    if len(reachable_not_hit) <= 20:
        print(f"  These: {sorted(reachable_not_hit)}")

    # =========================================================================
    # PART E: Analyze what makes E∩X unreachable
    # =========================================================================

    print("\n" + "=" * 70)
    print("PART E: Why Are E∩X Cylinders Unreachable?")
    print("=" * 70)

    print("""
To reach cylinder 521 or 541, we need some ABC such that 2*ABCXY starts with 521 or 541.

Let's check what predecessors these have:
""")

    for target in ex_cylinders:
        print(f"\n--- To reach {target} ---")

        # What 3-digit prefixes, when doubled, give this target?
        predecessors_detailed = []
        for a in range(1, 10):
            for b in range(1, 10):
                for c in range(1, 10):
                    cyl = f"{a}{b}{c}"
                    targets = get_transition_targets(cyl, extra_digits=2)
                    if target in targets:
                        predecessors_detailed.append(cyl)

        print(f"  Predecessors: {predecessors_detailed}")

        if predecessors_detailed:
            # Are any of these predecessors reachable?
            reachable_preds = [p for p in predecessors_detailed if p in reachable]
            print(f"  Reachable predecessors: {reachable_preds}")

            if not reachable_preds:
                print(f"  >>> No reachable predecessor! {target} is isolated.")
        else:
            print(f"  >>> No predecessors at all! {target} cannot be reached by doubling.")

    # =========================================================================
    # PART F: The mathematical constraint
    # =========================================================================

    print("\n" + "=" * 70)
    print("PART F: Mathematical Analysis")
    print("=" * 70)

    print("""
For 2*N to start with 521:
  521 * 10^k <= 2*N < 522 * 10^k
  260.5 * 10^k <= N < 261 * 10^k

So N must start with 260 or 261 (approximately).

But 260 contains a 0! It's not zeroless.
And 261 when doubled gives 522, not 521.

Let's verify:
""")

    for target in ['521', '541']:
        print(f"\n--- Target: {target} ---")

        # What N (3-digit prefix) when doubled gives target?
        target_int = int(target)

        # 2*N starts with target means:
        # target * 10^k <= 2*N < (target+1) * 10^k
        # target/2 * 10^k <= N < (target+1)/2 * 10^k

        lower = target_int / 2
        upper = (target_int + 1) / 2

        print(f"  N must be in range [{lower}, {upper}) × 10^k")
        print(f"  For 3-digit N: {lower*1:.1f} to {upper*1:.1f}")
        print(f"  For 4-digit N: {lower*10:.1f} to {upper*10:.1f}")

        # Check 3-digit
        for n in range(int(lower), int(upper) + 1):
            n_str = str(n)
            doubled = str(2 * n)
            zl = "zeroless" if is_zeroless(n_str) else "HAS ZERO"
            print(f"    {n} → 2*{n} = {doubled} ({zl})")

        # Check 4-digit
        for n in range(int(lower*10), int(upper*10) + 1):
            n_str = str(n)
            doubled = str(2 * n)
            if doubled.startswith(target):
                zl = "zeroless" if is_zeroless(n_str) else "HAS ZERO"
                print(f"    {n} → 2*{n} = {doubled} ({zl})")

    # =========================================================================
    # SYNTHESIS
    # =========================================================================

    print("\n" + "=" * 70)
    print("SYNTHESIS")
    print("=" * 70)

    print(f"""
KEY FINDINGS:

1. TRANSITION GRAPH STRUCTURE:
   - {len(all_cylinders)} zeroless 3-digit cylinders
   - {total_edges} transitions (avg out-degree {total_edges/len(all_cylinders):.1f})

2. E∩X CYLINDER REACHABILITY:
   - 521: {"REACHABLE" if '521' in reachable else "NOT REACHABLE"}
   - 541: {"REACHABLE" if '541' in reachable else "NOT REACHABLE"}

3. MATHEMATICAL REASON:
   - To reach 521, predecessor N must be ~260.5
   - 260 contains a zero → not zeroless
   - Similarly for 541 (predecessor ~270.5, and 270 has zero)

4. IMPLICATION:
   - E∩X cylinders (521, 541) are MATHEMATICALLY unreachable
   - No zeroless number, when doubled, produces 521xxx or 541xxx
   - This is WHY the orbit avoids E∩X: it's not probabilistic, it's arithmetic

5. THE ORBIT'S E∩X AVOIDANCE IS FORCED BY ARITHMETIC:
   - E∩X at depth 3 requires prefix 521 or 541
   - These require predecessors containing 0
   - Zeroless orbit cannot reach them
""")

if __name__ == "__main__":
    main()
