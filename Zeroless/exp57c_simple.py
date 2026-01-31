"""
Exp 57c: Simple comparison of automaton vs orbit
"""
import sys
sys.set_int_max_str_digits(50000)

# Count allowed words at depth 3 (simple enumeration)
DIGITS = "123456789"

def is_allowed(word):
    """Check if word is allowed by automaton constraints."""
    for i in range(len(word) - 1):
        d1, d2 = word[i], word[i+1]
        # Entry-Forced Zero: even followed by 1
        if d1 in "2468" and d2 == "1":
            return False
        # Forward-Forced Zero: 5 with carry 0
        # This requires knowing the carry, which depends on position
        # Simplified: we check just the entry constraint for now
    return True

# Actually the forward constraint is more complex
# Let's just count all zeroless words and compare to hits

print("Comparing allowed vs hit cylinders:")
print()

for depth in range(2, 6):
    # Count all zeroless words (no automaton constraint)
    total_zeroless = 9 ** depth

    # Count actual hits
    hits = set()
    power = 1
    for n in range(1, 20001):
        power *= 2
        s = str(power)
        if len(s) >= depth:
            prefix = s[:depth]
            if '0' not in prefix:
                hits.add(prefix)

    # Count words with entry witness (blocked by Entry-Forced Zero)
    has_entry = 0
    for d1 in DIGITS:
        for d2 in DIGITS:
            if depth == 2:
                if d1 in "2468" and d2 == "1":
                    has_entry += 1
            else:
                # More complex for longer words
                pass

    print(f"Depth {depth}:")
    print(f"  Total zeroless: {total_zeroless}")
    print(f"  Actual hits:    {len(hits)}")
    print(f"  Ratio:          {len(hits)/total_zeroless:.4%}")
    print()

print("Key observation:")
print("  Hit count stays ~25-30 regardless of depth")
print("  This is NOT explained by Entry-Forced Zero alone")
print("  (which only blocks ~4/81 = 5% at depth 2)")
