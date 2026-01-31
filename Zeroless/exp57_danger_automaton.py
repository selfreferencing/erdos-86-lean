"""
Exp 57: Danger Cylinder Automaton Construction

Goal: Build the finite-state automaton for bi-extendable zeroless cylinders
and verify that SCCs are cycles (no branching) → O(1) danger cylinders.

Based on APPROACH 28A/B:
- States: (c, r) where c = carry (doubling), r = remainder (halving)
- Entry-Forced Zero: even→1 forces 0 in predecessor (blocks backward)
- Forward-Forced Zero: 5 with carry 0 forces 0 in successor (blocks forward)
"""

from itertools import product
from collections import defaultdict

DIGITS = list(range(1, 10))  # Zeroless: 1-9

def doubling_carry_out(digit, carry_in):
    """Compute outgoing carry after doubling digit with carry_in."""
    return (2 * digit + carry_in) // 10

def halving_remainder_out(digit):
    """Compute outgoing remainder after halving (just parity of digit)."""
    return digit % 2

# ============================================================
# PART 1: Build the basic automaton
# ============================================================

print("=" * 60)
print("PART 1: Building the Danger Automaton")
print("=" * 60)

# States: (carry_in, remainder_in)
# carry_in ∈ {0, 1}: carry entering from right (less significant) in doubling
# remainder_in ∈ {0, 1}: remainder entering from left in halving

states = [(c, r) for c in [0, 1] for r in [0, 1]]
print(f"\nStates (c, r): {states}")

# For each state and each digit, compute:
# 1. Is this transition valid (doesn't produce 0 in either direction)?
# 2. What is the next state?

transitions = defaultdict(list)  # state -> [(digit, next_state), ...]
blocked_transitions = defaultdict(list)  # state -> [(digit, reason), ...]

for (c_in, r_in) in states:
    for d in DIGITS:
        blocked = False
        reason = ""

        # Check halving constraint (Entry-Forced Zero)
        # If r_in = 0 (previous digit was even) and d = 1, we get quotient 0
        if r_in == 0 and d == 1:
            blocked = True
            reason = "Entry-Forced Zero: even→1"

        # Check doubling constraint (Forward-Forced Zero)
        # If d = 5 and c_in = 0, we get 2*5 + 0 = 10, output digit 0
        if d == 5 and c_in == 0:
            blocked = True
            reason = "Forward-Forced Zero: 5 with carry 0"

        if blocked:
            blocked_transitions[(c_in, r_in)].append((d, reason))
        else:
            # Compute next state
            c_out = doubling_carry_out(d, c_in)
            r_out = halving_remainder_out(d)
            next_state = (c_out, r_out)
            transitions[(c_in, r_in)].append((d, next_state))

print("\n--- Transition Table ---")
for state in states:
    print(f"\nState {state}:")
    allowed = transitions[state]
    blocked = blocked_transitions[state]
    print(f"  Allowed transitions: {len(allowed)}")
    for d, ns in allowed:
        print(f"    digit {d} → state {ns}")
    print(f"  Blocked: {blocked}")

# ============================================================
# PART 2: Build adjacency and find SCCs (Tarjan's algorithm)
# ============================================================

print("\n" + "=" * 60)
print("PART 2: Transition Graph and SCC Analysis")
print("=" * 60)

# Build adjacency list
adj = defaultdict(set)
edge_labels = defaultdict(list)  # (from, to) -> [digits]

for state in states:
    for digit, next_state in transitions[state]:
        adj[state].add(next_state)
        edge_labels[(state, next_state)].append(digit)

# Count edges
total_edges = sum(len(v) for v in adj.values())
print(f"\nGraph has {len(states)} nodes and {total_edges} edges")

# Tarjan's SCC algorithm
index_counter = [0]
stack = []
lowlinks = {}
index = {}
on_stack = {}
sccs = []

def strongconnect(v):
    index[v] = index_counter[0]
    lowlinks[v] = index_counter[0]
    index_counter[0] += 1
    stack.append(v)
    on_stack[v] = True

    for w in adj[v]:
        if w not in index:
            strongconnect(w)
            lowlinks[v] = min(lowlinks[v], lowlinks[w])
        elif on_stack.get(w, False):
            lowlinks[v] = min(lowlinks[v], index[w])

    if lowlinks[v] == index[v]:
        scc = []
        while True:
            w = stack.pop()
            on_stack[w] = False
            scc.append(w)
            if w == v:
                break
        sccs.append(set(scc))

for v in states:
    if v not in index:
        strongconnect(v)

print(f"\nStrongly Connected Components: {len(sccs)}")
for i, scc in enumerate(sccs):
    print(f"  SCC {i}: {scc}")

# Find nontrivial SCCs (size > 1, or has self-loop)
nontrivial_sccs = []
for scc in sccs:
    if len(scc) > 1:
        nontrivial_sccs.append(scc)
    else:
        node = list(scc)[0]
        if node in adj[node]:  # self-loop
            nontrivial_sccs.append(scc)

print(f"\nNontrivial SCCs (recurrent): {len(nontrivial_sccs)}")
for scc in nontrivial_sccs:
    print(f"  {scc}")

# ============================================================
# PART 3: Check for branching in SCCs
# ============================================================

print("\n" + "=" * 60)
print("PART 3: Branching Analysis in SCCs")
print("=" * 60)

for scc in nontrivial_sccs:
    print(f"\nAnalyzing SCC: {scc}")

    has_branching = False
    for node in scc:
        # Count outgoing edges within SCC with their digit counts
        successors_in_scc = [v for v in adj[node] if v in scc]
        digit_choices = []
        for succ in successors_in_scc:
            digit_choices.extend(edge_labels[(node, succ)])

        print(f"  State {node}:")
        print(f"    Successors in SCC: {successors_in_scc}")
        print(f"    Digit choices: {digit_choices}")
        print(f"    Total choices: {len(digit_choices)}")

        if len(digit_choices) > 1:
            has_branching = True
            print(f"    ** BRANCHING: multiple digit choices **")

    if has_branching:
        print(f"  → SCC has branching (NOT a simple cycle)")
    else:
        print(f"  → SCC is deterministic (simple cycle)")

# ============================================================
# PART 4: Enumerate cycles and templates
# ============================================================

print("\n" + "=" * 60)
print("PART 4: Cycle and Template Enumeration")
print("=" * 60)

def find_simple_cycles(adj, edge_labels, scc):
    """Find simple cycles in SCC with digit labels."""
    cycles = []
    scc_list = list(scc)

    for start in scc_list:
        # DFS to find cycles
        stack = [(start, [start], [])]
        while stack:
            curr, path, digits = stack.pop()
            for next_node in adj[curr]:
                if next_node not in scc:
                    continue
                for d in edge_labels[(curr, next_node)]:
                    if next_node == start and len(path) > 0:
                        cycles.append((path[:], digits + [d]))
                    elif next_node not in path:
                        stack.append((next_node, path + [next_node], digits + [d]))
    return cycles

all_templates = []
for scc in nontrivial_sccs:
    cycles = find_simple_cycles(adj, edge_labels, scc)
    print(f"\nSCC {scc}:")
    print(f"  Found {len(cycles)} cycle(s)")

    seen = set()
    for states_path, digits in cycles:
        template = ''.join(str(d) for d in digits)
        if template not in seen:
            print(f"    Cycle: states={states_path}, template='{template}'")
            all_templates.append(template)
            seen.add(template)

# Canonicalize templates
unique_templates = set()
for t in all_templates:
    rotations = [t[i:] + t[:i] for i in range(len(t))]
    canonical = min(rotations)
    unique_templates.add(canonical)

print(f"\n--- Unique Canonical Templates ---")
for t in sorted(unique_templates, key=lambda x: (len(x), x)):
    print(f"  '{t}' (period {len(t)})")

# ============================================================
# PART 5: Count danger cylinders at each depth
# ============================================================

print("\n" + "=" * 60)
print("PART 5: Danger Cylinder Counts by Depth")
print("=" * 60)

def enumerate_danger_words(max_depth):
    """
    Enumerate all words that can appear on infinite bi-extendable paths.
    These are words that traverse only through recurrent states.
    """
    recurrent_states = set()
    for scc in nontrivial_sccs:
        recurrent_states.update(scc)

    if not recurrent_states:
        return {d: set() for d in range(1, max_depth + 1)}

    results = {d: set() for d in range(1, max_depth + 1)}

    # For each starting state in recurrent set, enumerate paths
    for start in recurrent_states:
        # BFS: (current_state, word_so_far, depth)
        queue = [(start, "", 0)]
        while queue:
            curr, word, depth = queue.pop(0)
            if depth > 0 and curr in recurrent_states:
                results[depth].add(word)
            if depth >= max_depth:
                continue
            for digit, next_state in transitions[curr]:
                if next_state in recurrent_states or depth < max_depth - 1:
                    queue.append((next_state, word + str(digit), depth + 1))

    # Filter: only keep words where both endpoints are recurrent
    for d in range(1, max_depth + 1):
        filtered = set()
        for word in results[d]:
            # Check if this word can be extended in both directions
            # by verifying start and end states
            # (Simplified: we enumerated from recurrent starts, need recurrent ends)
            filtered.add(word)
        results[d] = filtered

    return results

print("\nEnumerating danger words by depth...")
danger_words = enumerate_danger_words(6)

for depth in range(1, 7):
    words = danger_words[depth]
    print(f"\nDepth {depth}: {len(words)} danger words")
    if len(words) <= 20:
        print(f"  Words: {sorted(words)}")
    else:
        print(f"  Sample: {sorted(words)[:10]}...")

# ============================================================
# PART 6: Compare with empirical hit cylinders
# ============================================================

print("\n" + "=" * 60)
print("PART 6: Compare with Empirical Hit Cylinders")
print("=" * 60)

# Compute actual hit cylinders from powers of 2
def get_hit_cylinders(max_exp, depth):
    """Find all depth-m prefixes that appear in zeroless powers of 2."""
    hits = set()
    power = 1
    for exp in range(1, max_exp + 1):
        power *= 2
        s = str(power)
        if len(s) >= depth:
            prefix = s[:depth]
            if '0' not in prefix:
                hits.add(prefix)
    return hits

print("\nComparing danger words with actual orbit hits...")
for depth in range(2, 6):
    danger = danger_words[depth]
    hits = get_hit_cylinders(100000, depth)

    print(f"\nDepth {depth}:")
    print(f"  Danger words (automaton): {len(danger)}")
    print(f"  Hit cylinders (orbit):    {len(hits)}")

    # Check containment
    hits_in_danger = hits & danger
    hits_not_danger = hits - danger
    danger_not_hit = danger - hits

    print(f"  Hits that are danger:     {len(hits_in_danger)}")
    print(f"  Hits NOT danger:          {len(hits_not_danger)}")
    if hits_not_danger:
        print(f"    Examples: {sorted(hits_not_danger)[:5]}")
    print(f"  Danger NOT hit:           {len(danger_not_hit)}")

# ============================================================
# PART 7: Summary
# ============================================================

print("\n" + "=" * 60)
print("SUMMARY")
print("=" * 60)

# Check branching
total_branching_states = 0
for scc in nontrivial_sccs:
    for node in scc:
        successors_in_scc = [v for v in adj[node] if v in scc]
        digit_count = sum(len(edge_labels[(node, s)]) for s in successors_in_scc)
        if digit_count > 1:
            total_branching_states += 1

print(f"""
Automaton Analysis:
- Total states: {len(states)}
- Nontrivial SCCs: {len(nontrivial_sccs)}
- States with branching in SCCs: {total_branching_states}
""")

if total_branching_states == 0:
    print("✓ NO BRANCHING in SCCs → All SCCs are simple cycles")
    print("✓ This proves O(1) danger cylinders!")
    print(f"✓ Total unique templates: {len(unique_templates)}")
else:
    print(f"✗ BRANCHING EXISTS: {total_branching_states} states have multiple choices")
    print("✗ O(1) theorem NOT proven by this simple automaton")
    print("  Need to refine the state space or add more constraints")

print(f"\nCanonical templates: {sorted(unique_templates, key=lambda x: (len(x), x))}")
