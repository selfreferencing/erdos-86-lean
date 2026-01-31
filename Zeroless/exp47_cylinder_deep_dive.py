"""
Experiment 47: Deep Dive into O(1) Cylinder Phenomenon

Multiple lightweight investigations:
A. List and characterize all 29 hit 3-digit cylinders
B. Build the 2-digit cylinder transition graph under doubling
C. Forward reachability: which cylinders can be reached from 2^1?
D. Cross-reference hit cylinders with E∩X membership
E. Cylinder persistence across m values
F. Compare hit cylinders to random sample of unhit cylinders
"""

import math
from collections import defaultdict

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

def double_prefix(prefix):
    """
    Compute what prefix results from doubling.
    Returns the leading digits of 2 * (prefix as integer).
    """
    val = int(prefix)
    doubled = 2 * val
    return str(doubled)

def get_successor_cylinder(prefix, k):
    """
    Given a k-digit prefix, what k-digit cylinder does 2*prefix land in?
    Accounts for possible digit growth.
    """
    doubled = double_prefix(prefix)
    if len(doubled) > len(prefix):
        # Digit count increased (leading digit was >= 5)
        return doubled[:k]
    else:
        return doubled[:k]

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

def build_transition_graph_2digit():
    """
    Build transition graph for 2-digit cylinders.
    Node = 2-digit zeroless prefix (e.g., '12', '99')
    Edge A -> B if doubling some number starting with A gives something starting with B.

    For each 2-digit prefix AB, we need to consider:
    - What range of 3-digit numbers start with AB?
    - When doubled, what 2-digit prefixes can result?
    """
    # All zeroless 2-digit prefixes
    prefixes_2 = [f"{a}{b}" for a in range(1, 10) for b in range(1, 10)]

    graph = defaultdict(set)

    for prefix in prefixes_2:
        # Consider numbers of the form prefix + X where X is any digit
        # This gives range [prefix*10, prefix*10+9]
        # When doubled: [2*prefix*10, 2*prefix*10+19]

        base = int(prefix) * 10
        for extra in range(10):
            num = base + extra
            doubled = 2 * num
            doubled_str = str(doubled)

            # The successor 2-digit prefix
            succ_2 = doubled_str[:2]

            # Only add if successor is zeroless
            if is_zeroless(succ_2):
                graph[prefix].add(succ_2)

    return graph, prefixes_2

def compute_reachable(graph, start_nodes):
    """BFS to find all reachable nodes from start_nodes."""
    reachable = set(start_nodes)
    frontier = list(start_nodes)

    while frontier:
        node = frontier.pop()
        for neighbor in graph.get(node, []):
            if neighbor not in reachable:
                reachable.add(neighbor)
                frontier.append(neighbor)

    return reachable

def main():
    print("=" * 70)
    print("Experiment 47: Deep Dive into O(1) Cylinder Phenomenon")
    print("=" * 70)

    hits = find_all_hits(27)

    # =========================================================================
    # PART A: Characterize all hit cylinders
    # =========================================================================

    print("\n" + "=" * 70)
    print("PART A: All Hit Cylinders (3-digit)")
    print("=" * 70)

    cylinders_3 = {}
    for h in hits:
        if len(h['prefix']) >= 3:
            c3 = h['prefix'][:3]
            if c3 not in cylinders_3:
                cylinders_3[c3] = []
            cylinders_3[c3].append(h)

    print(f"\nTotal distinct 3-digit cylinders hit: {len(cylinders_3)}")
    print(f"\n{'Cylinder':<10} | {'Hits':>4} | {'E':>1} | {'X':>1} | {'E&X':>3} | m values")
    print("-" * 60)

    for cyl in sorted(cylinders_3.keys()):
        hit_list = cylinders_3[cyl]
        has_E = has_entry_witness(cyl)
        has_X = has_exit_witness(cyl)
        e_str = 'Y' if has_E else 'N'
        x_str = 'Y' if has_X else 'N'
        ex_str = 'Y' if (has_E and has_X) else 'N'
        m_vals = sorted(set(h['m'] for h in hit_list))
        m_str = ','.join(str(m) for m in m_vals[:5])
        if len(m_vals) > 5:
            m_str += '...'
        print(f"{cyl:<10} | {len(hit_list):>4} | {e_str:>1} | {x_str:>1} | {ex_str:>3} | {m_str}")

    # Summary stats
    cyl_with_E = sum(1 for c in cylinders_3 if has_entry_witness(c))
    cyl_with_X = sum(1 for c in cylinders_3 if has_exit_witness(c))
    cyl_with_EX = sum(1 for c in cylinders_3 if has_entry_witness(c) and has_exit_witness(c))

    print(f"\nSummary:")
    print(f"  With entry witness (E): {cyl_with_E}/{len(cylinders_3)} = {cyl_with_E/len(cylinders_3):.1%}")
    print(f"  With exit witness (X): {cyl_with_X}/{len(cylinders_3)} = {cyl_with_X/len(cylinders_3):.1%}")
    print(f"  With both (E ∩ X): {cyl_with_EX}/{len(cylinders_3)} = {cyl_with_EX/len(cylinders_3):.1%}")

    # =========================================================================
    # PART B: 2-digit Transition Graph
    # =========================================================================

    print("\n" + "=" * 70)
    print("PART B: 2-Digit Cylinder Transition Graph")
    print("=" * 70)

    graph_2, all_prefixes_2 = build_transition_graph_2digit()

    print(f"\nTotal 2-digit zeroless prefixes: {len(all_prefixes_2)}")
    print(f"Nodes with outgoing edges: {len(graph_2)}")

    # Count edges
    total_edges = sum(len(v) for v in graph_2.values())
    print(f"Total edges: {total_edges}")
    print(f"Average out-degree: {total_edges / len(graph_2):.2f}")

    # Show some transitions
    print("\nSample transitions:")
    for prefix in ['16', '32', '64', '12', '25', '51']:
        successors = sorted(graph_2.get(prefix, set()))
        print(f"  {prefix} -> {', '.join(successors)}")

    # =========================================================================
    # PART C: Forward Reachability from Initial Powers
    # =========================================================================

    print("\n" + "=" * 70)
    print("PART C: Forward Reachability")
    print("=" * 70)

    # The orbit starts from 2^1 = 2, 2^2 = 4, etc.
    # Initial 2-digit prefixes from small powers
    initial_2digit = set()
    for n in range(1, 20):
        p = str(2**n)
        if len(p) >= 2 and is_zeroless(p[:2]):
            initial_2digit.add(p[:2])

    print(f"\nInitial 2-digit cylinders (from 2^1 to 2^19): {sorted(initial_2digit)}")

    reachable_2 = compute_reachable(graph_2, initial_2digit)
    print(f"\nReachable 2-digit cylinders: {len(reachable_2)}/81")
    print(f"Reachable: {sorted(reachable_2)}")

    # Compare to actually hit cylinders
    actually_hit_2 = set()
    for h in hits:
        if len(h['prefix']) >= 2:
            actually_hit_2.add(h['prefix'][:2])

    print(f"\nActually hit 2-digit cylinders: {len(actually_hit_2)}")
    print(f"Actually hit: {sorted(actually_hit_2)}")

    # Check containment
    hit_not_reachable = actually_hit_2 - reachable_2
    reachable_not_hit = reachable_2 - actually_hit_2

    print(f"\nHit but not graph-reachable: {hit_not_reachable}")
    print(f"Graph-reachable but never hit: {reachable_not_hit}")

    # =========================================================================
    # PART D: Cross-reference with E∩X
    # =========================================================================

    print("\n" + "=" * 70)
    print("PART D: E∩X Analysis of Hit Cylinders")
    print("=" * 70)

    # For 3-digit cylinders, count how many are in various categories
    all_zeroless_3 = [f"{a}{b}{c}" for a in range(1,10) for b in range(1,10) for c in range(1,10)]

    in_E = [c for c in all_zeroless_3 if has_entry_witness(c)]
    in_X = [c for c in all_zeroless_3 if has_exit_witness(c)]
    in_EX = [c for c in all_zeroless_3 if has_entry_witness(c) and has_exit_witness(c)]

    print(f"\nAll 3-digit zeroless prefixes: {len(all_zeroless_3)}")
    print(f"  In E (entry witness): {len(in_E)} ({len(in_E)/len(all_zeroless_3):.1%})")
    print(f"  In X (exit witness): {len(in_X)} ({len(in_X)/len(all_zeroless_3):.1%})")
    print(f"  In E ∩ X: {len(in_EX)} ({len(in_EX)/len(all_zeroless_3):.1%})")

    hit_cyl_3 = set(cylinders_3.keys())

    hit_in_E = hit_cyl_3 & set(in_E)
    hit_in_X = hit_cyl_3 & set(in_X)
    hit_in_EX = hit_cyl_3 & set(in_EX)

    print(f"\nHit cylinders (29):")
    print(f"  In E: {len(hit_in_E)} ({len(hit_in_E)/len(hit_cyl_3):.1%})")
    print(f"  In X: {len(hit_in_X)} ({len(hit_in_X)/len(hit_cyl_3):.1%})")
    print(f"  In E ∩ X: {len(hit_in_EX)} ({len(hit_in_EX)/len(hit_cyl_3):.1%})")

    # Are hit cylinders enriched for E∩X compared to baseline?
    baseline_EX_rate = len(in_EX) / len(all_zeroless_3)
    hit_EX_rate = len(hit_in_EX) / len(hit_cyl_3)
    enrichment = hit_EX_rate / baseline_EX_rate if baseline_EX_rate > 0 else float('inf')

    print(f"\nE∩X enrichment in hit cylinders: {enrichment:.2f}x")

    # =========================================================================
    # PART E: Cylinder Persistence Across m
    # =========================================================================

    print("\n" + "=" * 70)
    print("PART E: Cylinder Persistence Across m Values")
    print("=" * 70)

    # For each 2-digit cylinder, which m values does it appear in?
    cyl_2_by_m = defaultdict(set)
    for h in hits:
        if len(h['prefix']) >= 2:
            cyl_2_by_m[h['prefix'][:2]].add(h['m'])

    # Distribution of persistence
    persistence_dist = defaultdict(int)
    for cyl, m_set in cyl_2_by_m.items():
        persistence_dist[len(m_set)] += 1

    print(f"\nPersistence distribution (2-digit cylinders):")
    print(f"  (How many m values does each cylinder appear in?)")
    for count in sorted(persistence_dist.keys()):
        cyls = [c for c, ms in cyl_2_by_m.items() if len(ms) == count]
        print(f"  {count} m-values: {persistence_dist[count]} cylinders ({', '.join(sorted(cyls)[:5])}{'...' if len(cyls) > 5 else ''})")

    # Most persistent cylinders
    print(f"\nMost persistent 2-digit cylinders:")
    for cyl, m_set in sorted(cyl_2_by_m.items(), key=lambda x: -len(x[1]))[:10]:
        print(f"  {cyl}: appears in m = {sorted(m_set)}")

    # =========================================================================
    # PART F: Compare Hit vs Unhit Cylinders
    # =========================================================================

    print("\n" + "=" * 70)
    print("PART F: Hit vs Unhit Cylinder Comparison")
    print("=" * 70)

    unhit_cyl_3 = set(all_zeroless_3) - hit_cyl_3

    # Digit distributions
    def digit_stats(cylinders):
        """Compute digit frequency in a set of 3-digit cylinders."""
        freq = defaultdict(int)
        for c in cylinders:
            for d in c:
                freq[d] += 1
        total = sum(freq.values())
        return {d: freq[d]/total for d in '123456789'}

    hit_stats = digit_stats(hit_cyl_3)
    unhit_stats = digit_stats(unhit_cyl_3)

    print(f"\nDigit frequency comparison:")
    print(f"{'Digit':<6} | {'Hit':>8} | {'Unhit':>8} | {'Diff':>8}")
    print("-" * 40)
    for d in '123456789':
        diff = hit_stats.get(d, 0) - unhit_stats.get(d, 0)
        print(f"{d:<6} | {hit_stats.get(d, 0):>8.3f} | {unhit_stats.get(d, 0):>8.3f} | {diff:>+8.3f}")

    # Leading digit distribution
    hit_lead = defaultdict(int)
    unhit_lead = defaultdict(int)
    for c in hit_cyl_3:
        hit_lead[c[0]] += 1
    for c in unhit_cyl_3:
        unhit_lead[c[0]] += 1

    print(f"\nLeading digit distribution:")
    print(f"{'Lead':>4} | {'Hit':>6} | {'Unhit':>6} | {'Hit %':>8} | {'Unhit %':>8}")
    print("-" * 50)
    for d in '123456789':
        h = hit_lead.get(d, 0)
        u = unhit_lead.get(d, 0)
        hp = h / len(hit_cyl_3) * 100 if hit_cyl_3 else 0
        up = u / len(unhit_cyl_3) * 100 if unhit_cyl_3 else 0
        print(f"{d:>4} | {h:>6} | {u:>6} | {hp:>7.1f}% | {up:>7.1f}%")

    # =========================================================================
    # PART G: Strongly Connected Components
    # =========================================================================

    print("\n" + "=" * 70)
    print("PART G: Strongly Connected Components (2-digit)")
    print("=" * 70)

    # Simple SCC finder using Kosaraju's algorithm
    def find_sccs(graph, nodes):
        # First DFS to get finish order
        visited = set()
        finish_order = []

        def dfs1(node):
            if node in visited:
                return
            visited.add(node)
            for neighbor in graph.get(node, []):
                dfs1(neighbor)
            finish_order.append(node)

        for node in nodes:
            dfs1(node)

        # Build reverse graph
        reverse = defaultdict(set)
        for node in nodes:
            for neighbor in graph.get(node, []):
                reverse[neighbor].add(node)

        # Second DFS in reverse finish order
        visited = set()
        sccs = []

        def dfs2(node, component):
            if node in visited:
                return
            visited.add(node)
            component.append(node)
            for neighbor in reverse.get(node, []):
                dfs2(neighbor, component)

        for node in reversed(finish_order):
            if node not in visited:
                component = []
                dfs2(node, component)
                sccs.append(component)

        return sccs

    # Find SCCs in the 2-digit graph
    all_nodes_2 = set(all_prefixes_2)
    # Add nodes that appear as targets
    for targets in graph_2.values():
        all_nodes_2.update(targets)
    # Filter to zeroless only
    all_nodes_2 = {n for n in all_nodes_2 if is_zeroless(n) and len(n) == 2}

    sccs = find_sccs(graph_2, all_nodes_2)

    print(f"\nTotal SCCs: {len(sccs)}")

    # Size distribution
    size_dist = defaultdict(int)
    for scc in sccs:
        size_dist[len(scc)] += 1

    print(f"\nSCC size distribution:")
    for size in sorted(size_dist.keys(), reverse=True)[:10]:
        count = size_dist[size]
        if size <= 5:
            examples = [scc for scc in sccs if len(scc) == size][:2]
            ex_str = "; ".join([",".join(sorted(e)) for e in examples])
            print(f"  Size {size}: {count} SCCs (e.g., {ex_str})")
        else:
            print(f"  Size {size}: {count} SCCs")

    # Largest SCC
    largest_scc = max(sccs, key=len)
    print(f"\nLargest SCC has {len(largest_scc)} nodes")
    print(f"  Members: {sorted(largest_scc)[:20]}{'...' if len(largest_scc) > 20 else ''}")

    # How many hit cylinders are in the largest SCC?
    hit_in_largest = actually_hit_2 & set(largest_scc)
    print(f"\nHit 2-digit cylinders in largest SCC: {len(hit_in_largest)}/{len(actually_hit_2)}")
    print(f"  ({', '.join(sorted(hit_in_largest))})")

    # =========================================================================
    # SYNTHESIS
    # =========================================================================

    print("\n" + "=" * 70)
    print("SYNTHESIS")
    print("=" * 70)

    print(f"""
Key Findings:

1. CYLINDER CHARACTERIZATION:
   - 29 distinct 3-digit cylinders hit (out of 729 = 4.0%)
   - {cyl_with_EX} have both entry and exit witnesses ({cyl_with_EX/len(cylinders_3):.0%})
   - E∩X enrichment: {enrichment:.2f}x over baseline

2. TRANSITION GRAPH:
   - 2-digit graph has {len(graph_2)} nodes with edges
   - Average out-degree: {total_edges / len(graph_2):.2f}
   - {len(reachable_2)} cylinders graph-reachable from initial powers
   - {len(actually_hit_2)} cylinders actually hit

3. REACHABILITY:
   - Hit but not graph-reachable: {hit_not_reachable or 'None'}
   - Graph-reachable but never hit: {len(reachable_not_hit)} cylinders
   - The orbit visits only a SUBSET of graph-reachable cylinders

4. SCC STRUCTURE:
   - Largest SCC: {len(largest_scc)} nodes
   - {len(hit_in_largest)}/{len(actually_hit_2)} hit cylinders are in largest SCC

5. HIT vs UNHIT:
   - Hit cylinders may have different digit distribution
   - Leading digit '1' appears in {hit_lead.get('1', 0)} hit vs {unhit_lead.get('1', 0)} unhit
""")

if __name__ == "__main__":
    main()
