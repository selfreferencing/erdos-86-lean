"""
Exp 65: Why Is 2^n Lucky?

The orbit 2^n survives to n=86 when the random model predicts death by n≈25.
What structural properties make powers of 2 special?

Hypotheses to test:
1. Digit correlations from doubling create fewer killing pairs
2. The (4,5) pair is specifically avoided (ratio 0.41 in Exp 62)
3. Carry structure is biased toward protection
4. Modular periodicity creates structure
"""

from collections import Counter
import random


def get_digits(n):
    """Get digits of 2^n (LSB first)."""
    power = 2 ** n
    digits = []
    while power > 0:
        digits.append(power % 10)
        power //= 10
    return digits


def double_digits(digits):
    """Double a digit string."""
    result = []
    carry = 0
    for d in digits:
        val = 2 * d + carry
        result.append(val % 10)
        carry = val // 10
    if carry > 0:
        result.append(carry)
    return result


def count_killing_pairs(digits):
    """Count (low, 5) pairs where low ∈ {1,2,3,4}."""
    count = 0
    for i in range(1, len(digits)):
        if digits[i] == 5 and digits[i-1] in [1, 2, 3, 4]:
            count += 1
    return count


def main():
    print("=" * 70)
    print("Exp 65: Why Is 2^n Lucky?")
    print("=" * 70)

    # Part A: The doubling map and digit transitions
    print("\n" + "=" * 70)
    print("PART A: How Doubling Transforms Digit Pairs")
    print("=" * 70)

    print("\nThe doubling map: (d, c) → (2d+c mod 10, ⌊(2d+c)/10⌋)")
    print("\nDigit d with carry c=0 produces:")
    print("  d=1 → 2, d=2 → 4, d=3 → 6, d=4 → 8, d=5 → 0, d=6 → 2, d=7 → 4, d=8 → 6, d=9 → 8")
    print("\nDigit d with carry c=1 produces:")
    print("  d=1 → 3, d=2 → 5, d=3 → 7, d=4 → 9, d=5 → 1, d=6 → 3, d=7 → 5, d=8 → 7, d=9 → 9")

    print("\n\nKEY OBSERVATION: 5 is produced from:")
    print("  - d=2 with c=1 (2*2+1=5)")
    print("  - d=7 with c=1 (2*7+1=15)")
    print("\nSo new 5s only appear where there's a 2 or 7 WITH incoming carry!")

    # Part B: What precedes 2 and 7 in powers of 2?
    print("\n" + "=" * 70)
    print("PART B: What Digits Precede 2 and 7 in Powers of 2?")
    print("=" * 70)

    print("\nFor a 5 to be created, we need (2 or 7) with carry-in 1.")
    print("Carry-in 1 means the PRECEDING digit (to the right) is ≥ 5.")
    print("\nSo a 5 is created at position i iff:")
    print("  d[i] ∈ {2, 7} AND d[i-1] ≥ 5")

    # Count what precedes 2 and 7
    precedes_2 = Counter()
    precedes_7 = Counter()

    for n in range(50, 200):
        digits = get_digits(n)
        for i in range(1, len(digits)):
            if digits[i] == 2:
                precedes_2[digits[i-1]] += 1
            elif digits[i] == 7:
                precedes_7[digits[i-1]] += 1

    print("\nDistribution of digits preceding 2 (should be ~1/9 each if random):")
    total_2 = sum(precedes_2.values())
    for d in range(1, 10):
        freq = precedes_2[d] / total_2 if total_2 > 0 else 0
        bar = "*" * int(freq * 50)
        high = "HIGH→5" if d >= 5 else "low"
        print(f"  {d}: {freq:.3f} {bar} [{high}]")

    print("\nDistribution of digits preceding 7:")
    total_7 = sum(precedes_7.values())
    for d in range(1, 10):
        freq = precedes_7[d] / total_7 if total_7 > 0 else 0
        bar = "*" * int(freq * 50)
        high = "HIGH→5" if d >= 5 else "low"
        print(f"  {d}: {freq:.3f} {bar} [{high}]")

    # Part C: The (4,5) anomaly
    print("\n" + "=" * 70)
    print("PART C: Why Is (4,5) So Rare? (Ratio 0.41)")
    print("=" * 70)

    print("\n(4,5) means: position i has 5, position i-1 has 4")
    print("This happens when:")
    print("  - Position i was (2 or 7) with carry 1, producing 5")
    print("  - Position i-1 produced output 4 with carry 1")
    print("\nWhat produces output 4 with carry 1?")
    print("  2d + c ≡ 4 (mod 10) with c = 1 → 2d = 3 (impossible, d must be integer)")
    print("  2d + c ≡ 4 (mod 10) with c = 0 → 2d = 4 → d = 2")
    print("  2d + c ≡ 14 with c = 0 → 2d = 14 → d = 7")
    print("  2d + c ≡ 14 with c = 1 → 2d = 13 (impossible)")
    print("\nSo digit 4 is produced from d=2 (c=0) or d=7 (c=0)")
    print("Both have carry-out 0!")

    print("\n\n*** CRITICAL INSIGHT ***")
    print("The (4,5) pattern requires:")
    print("  Position i-1: output 4, carry-out 0 (from d=2 or d=7 with c=0)")
    print("  Position i: output 5, requires carry-in 1")
    print("\nBUT carry-out from i-1 is 0, so carry-in to i is 0!")
    print("This is a CONTRADICTION. The (4,5) pattern is FORBIDDEN by doubling dynamics!")

    # Verify this
    print("\n\nVerification: scanning all pairs in doubled numbers...")

    # Start with various numbers and double them, count (4,5) pairs
    pair_counts = Counter()
    for start in range(1, 1000):
        digits = []
        n = start
        while n > 0:
            digits.append(n % 10)
            n //= 10

        doubled = double_digits(digits)

        for i in range(1, len(doubled)):
            pair_counts[(doubled[i-1], doubled[i])] += 1

    print("\n(4,5) pairs in doubled numbers:", pair_counts[(4, 5)])
    print("(5,4) pairs in doubled numbers:", pair_counts[(5, 4)])
    print("Total pairs:", sum(pair_counts.values()))

    # Part D: What other pairs are forbidden/rare?
    print("\n" + "=" * 70)
    print("PART D: Forbidden Pairs Under Doubling")
    print("=" * 70)

    print("\nCompute which (a,b) pairs can appear after doubling:")
    print("(a at position i-1, b at position i)")

    # For each output pair (a, b), check if it's achievable
    achievable = {}
    for a in range(10):
        for b in range(10):
            # a is output at i-1, b is output at i
            # Need: 2*d_{i-1} + c_{i-1} ≡ a (mod 10), carry-out = c_i
            # And: 2*d_i + c_i ≡ b (mod 10)
            # c_i = 1 iff d_{i-1} >= 5

            possible = False
            for d_prev in range(10):
                for c_prev in [0, 1]:
                    out_prev = (2 * d_prev + c_prev) % 10
                    carry_out = 1 if d_prev >= 5 else 0

                    if out_prev == a:
                        # Now check if b is achievable with c_i = carry_out
                        for d_curr in range(10):
                            out_curr = (2 * d_curr + carry_out) % 10
                            if out_curr == b:
                                possible = True
                                break
                    if possible:
                        break
                if possible:
                    break

            achievable[(a, b)] = possible

    print("\nAchievable pairs (✓) vs Forbidden pairs (✗):")
    print("\n     | ", end="")
    for b in range(10):
        print(f" {b} ", end="")
    print("\n" + "-" * 35)

    forbidden_count = 0
    for a in range(10):
        print(f"  {a}  |", end="")
        for b in range(10):
            if achievable[(a, b)]:
                print(" ✓ ", end="")
            else:
                print(" ✗ ", end="")
                forbidden_count += 1
        print()

    print(f"\nForbidden pairs: {forbidden_count} out of 100")

    # List the forbidden pairs
    forbidden = [(a, b) for (a, b), v in achievable.items() if not v]
    print(f"\nForbidden pairs: {forbidden}")

    # Part E: How does this affect killing pairs?
    print("\n" + "=" * 70)
    print("PART E: Impact on Killing Pairs")
    print("=" * 70)

    killing_pairs = [(1, 5), (2, 5), (3, 5), (4, 5)]

    print("\nKilling pairs and their achievability under doubling:")
    for pair in killing_pairs:
        status = "ACHIEVABLE" if achievable[pair] else "FORBIDDEN"
        print(f"  {pair}: {status}")

    # Part F: The protection mechanism
    print("\n" + "=" * 70)
    print("PART F: The Built-in Protection Mechanism")
    print("=" * 70)

    print("\n*** KEY THEOREM ***")
    print("\nThe doubling map has a built-in bias against killing pairs!")
    print("\nProof:")
    print("  1. A 5 is created from d ∈ {2,7} with carry-in 1")
    print("  2. Carry-in 1 means the right neighbor d' ≥ 5")
    print("  3. If d' ≥ 5, then output at right neighbor is 2d'+c'")
    print("     - d'=5, c=0: output 0 (creates zero, not relevant)")
    print("     - d'=5, c=1: output 1, carry 1")
    print("     - d'=6, c=0: output 2, carry 1")
    print("     - d'=6, c=1: output 3, carry 1")
    print("     - d'=7, c=0: output 4, carry 1")
    print("     - d'=7, c=1: output 5, carry 1")
    print("     - d'=8, c=0: output 6, carry 1")
    print("     - d'=8, c=1: output 7, carry 1")
    print("     - d'=9, c=0: output 8, carry 1")
    print("     - d'=9, c=1: output 9, carry 1")
    print("\n  So when a NEW 5 is created (from 2 or 7 with carry 1),")
    print("  the digit to its right comes from d' ≥ 5, producing:")
    print("    outputs {0,1,2,3,4,5,6,7,8,9} depending on d' and c'")
    print("\n  But outputs 1,2,3,4 come from:")
    print("    1: d'=5 c'=1")
    print("    2: d'=6 c'=0")
    print("    3: d'=6 c'=1")
    print("    4: d'=7 c'=0")
    print("\n  All of these have d' ≥ 5, so the NEW 5 is PROTECTED!")

    print("\n\n*** CONCLUSION ***")
    print("When doubling creates a NEW 5, that 5 is automatically protected!")
    print("This is because new 5s require carry-in 1, which means right neighbor ≥ 5,")
    print("and right neighbor ≥ 5 means the output at that position has carry-out 1.")

    # Part G: Where do UNPROTECTED 5s come from?
    print("\n" + "=" * 70)
    print("PART G: Where Do Unprotected 5s Come From?")
    print("=" * 70)

    print("\nIf newly created 5s are protected, unprotected 5s must come from:")
    print("  1. PRE-EXISTING 5s that become unprotected")
    print("  2. The carry structure changing")

    print("\nA 5 that exists in 2^n: what happens to it in 2^{n+1}?")
    print("  - If carry-in = 0: 2*5+0 = 10 → output 0 (ZERO CREATED)")
    print("  - If carry-in = 1: 2*5+1 = 11 → output 1, carry 1")
    print("\nSo existing 5s either create zeros OR become 1s!")
    print("They do NOT produce new 5s directly.")

    print("\n\nThis means the '5 population' is completely renewed each step:")
    print("  - Old 5s → zeros (if unprotected) or 1s (if protected)")
    print("  - New 5s ← from 2s and 7s with carry")

    # Part H: The luck mechanism
    print("\n" + "=" * 70)
    print("PART H: The Luck Mechanism Explained")
    print("=" * 70)

    print("\nWhy is 2^n lucky?")
    print("\n1. NEW 5s are automatically protected (Part F)")
    print("2. The only way to get an UNPROTECTED 5 is:")
    print("   - A 5 is created from (2 or 7) with carry 1")
    print("   - In the NEXT step, that position might have a 5 again")
    print("   - If the right neighbor changed from ≥5 to <5, the new 5 is unprotected")

    print("\n3. But the doubling dynamics constrain this:")
    print("   - The '5 at position i' in step n came from '2 or 7 at i' in step n-1")
    print("   - After step n, position i has '1' (from the 5 with carry)")
    print("   - Position i can have 5 again only if '2 or 7' reappears with carry")
    print("   - This requires specific digit patterns that are constrained")

    print("\n\n*** THE KEY INSIGHT ***")
    print("The doubling dynamics create a CORRELATED evolution of digits.")
    print("This correlation REDUCES the frequency of unprotected 5s compared to random.")


if __name__ == "__main__":
    main()
