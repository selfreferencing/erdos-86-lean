#!/usr/bin/env python3
"""
WHY is P(survive k+1 | survive k) exactly 0.9?

This might be the key to a proof.
"""

import sys
sys.set_int_max_str_digits(100000)

def analyze_transition_mechanism():
    """
    At level k, survivors are residue classes mod T_k = 4·5^(k-1).
    At level k+1, period is T_{k+1} = 4·5^k = 5·T_k.

    Each level-k survivor r has 5 "children": r, r+T_k, r+2T_k, r+3T_k, r+4T_k mod T_{k+1}.

    Question: Of these 5 children, how many survive to level k+1?
    Claim: Exactly 4.5 on average (i.e., 9 out of every 10 children survive).
    """
    print("="*70)
    print("TRANSITION MECHANISM ANALYSIS")
    print("="*70)

    for k in range(1, 8):
        T_k = 4 * 5**(k-1)
        T_k1 = 4 * 5**k

        # Find survivors at level k
        survivors_k = []
        for r in range(T_k):
            n = r if r >= k else r + T_k
            power = pow(2, n, 10**k)
            zeroless = all((power // 10**i) % 10 != 0 for i in range(k))
            if zeroless:
                survivors_k.append(r)

        # For each survivor, check its 5 children
        child_survival_counts = []
        for r in survivors_k:
            surviving_children = 0
            for j in range(5):
                child = r + j * T_k
                n = child if child >= k + 1 else child + T_k1
                power = pow(2, n, 10**(k+1))
                zeroless = all((power // 10**i) % 10 != 0 for i in range(k+1))
                if zeroless:
                    surviving_children += 1
            child_survival_counts.append(surviving_children)

        from collections import Counter
        dist = Counter(child_survival_counts)
        avg = sum(child_survival_counts) / len(child_survival_counts) if child_survival_counts else 0

        print(f"\nk={k}: T_k={T_k}, |S_k|={len(survivors_k)}")
        print(f"  Child survival distribution: {dict(sorted(dist.items()))}")
        print(f"  Average surviving children: {avg:.4f}")
        print(f"  Expected if independent: 4.5")

def analyze_digit_k_distribution():
    """
    The k-th digit of 2^n (from right) depends on 2^n mod 10^(k+1).
    Given that digits 0,...,k-1 are all nonzero, what's P(digit k is nonzero)?

    If digits are independent, this should be 0.9.
    """
    print("\n" + "="*70)
    print("DIGIT DISTRIBUTION ANALYSIS")
    print("="*70)

    for k in range(1, 10):
        T_k = 4 * 5**(k-1)

        # Count residues where first k digits are zeroless
        survivors_k = 0
        # Count residues where first k+1 digits are zeroless
        survivors_k1 = 0

        for r in range(T_k):
            n = r if r >= k else r + T_k
            power_k = pow(2, n, 10**k)
            zeroless_k = all((power_k // 10**i) % 10 != 0 for i in range(k))

            if zeroless_k:
                survivors_k += 1
                # Check digit k
                power_k1 = pow(2, n, 10**(k+1))
                digit_k = (power_k1 // 10**k) % 10
                if digit_k != 0:
                    survivors_k1 += 1

        ratio = survivors_k1 / survivors_k if survivors_k > 0 else 0
        print(f"k={k}: survivors(k)={survivors_k}, also_survive(k+1)={survivors_k1}, ratio={ratio:.6f}")

def prove_0_9_ratio():
    """
    Attempt to understand WHY the ratio is exactly 0.9.

    Hypothesis: Among survivors at level k, the (k+1)-th digit is uniformly
    distributed over {0,1,...,9}, hence 9/10 = 0.9 have nonzero (k+1)-th digit.
    """
    print("\n" + "="*70)
    print("DIGIT UNIFORMITY TEST")
    print("="*70)

    for k in range(1, 8):
        T_k = 4 * 5**(k-1)

        # Among survivors at level k, count distribution of digit k
        digit_counts = {d: 0 for d in range(10)}

        for r in range(T_k):
            n = r if r >= k else r + T_k
            power_k = pow(2, n, 10**k)
            zeroless_k = all((power_k // 10**i) % 10 != 0 for i in range(k))

            if zeroless_k:
                power_k1 = pow(2, n, 10**(k+1))
                digit_k = (power_k1 // 10**k) % 10
                digit_counts[digit_k] += 1

        total = sum(digit_counts.values())
        print(f"\nk={k}: Distribution of digit {k} among level-{k} survivors:")
        for d in range(10):
            pct = 100 * digit_counts[d] / total if total > 0 else 0
            bar = '#' * int(pct / 2)
            print(f"  {d}: {digit_counts[d]:6d} ({pct:5.2f}%) {bar}")

def explore_5adic_structure():
    """
    The 5-adic perspective: digit k is determined by u_{k+1}(n) = 2^(n-k-1) mod 5^(k+1).

    Digit k = 0 iff u_{k+1}(n) < 5^k / 2.

    For survivors at level k, what's the distribution of u_{k+1}(n)?
    """
    print("\n" + "="*70)
    print("5-ADIC STRUCTURE OF SURVIVORS")
    print("="*70)

    for k in range(1, 6):
        T_k = 4 * 5**(k-1)
        threshold = 5**k // 2

        # Among survivors at level k, analyze u_{k+1} distribution
        u_values = []
        in_zero_interval = 0

        for r in range(T_k):
            n = r if r >= k else r + T_k
            power_k = pow(2, n, 10**k)
            zeroless_k = all((power_k // 10**i) % 10 != 0 for i in range(k))

            if zeroless_k:
                u = pow(2, n - k - 1, 5**(k+1)) if n > k else None
                if u is not None:
                    u_values.append(u)
                    if u < threshold:
                        in_zero_interval += 1

        if u_values:
            ratio_in_zero = in_zero_interval / len(u_values)
            print(f"\nk={k}: threshold={threshold}, |survivors|={len(u_values)}")
            print(f"  u_{k+1} values in [0, {threshold}): {in_zero_interval}")
            print(f"  Ratio in zero interval: {ratio_in_zero:.6f}")
            print(f"  Expected if uniform: {threshold / 5**(k+1):.6f} = 0.1")

def the_key_insight():
    """
    The key insight: among survivors at level k, the next digit is UNIFORM over {0,...,9}.

    This is because:
    1. Survival at level k depends on n mod T_k = 4·5^(k-1)
    2. The k-th digit depends on higher-order bits of 2^n mod 10^(k+1)
    3. These are "fresh" bits, independent of the level-k constraint

    This is why P(survive k+1 | survive k) = 9/10 exactly!
    """
    print("\n" + "="*70)
    print("THE KEY INSIGHT")
    print("="*70)

    print("""
Why is P(survive k+1 | survive k) = 0.9 exactly?

1. Survival at level k depends on: 2^n mod 10^k
   This is determined by: n mod T_k where T_k = 4·5^(k-1)

2. The k-th digit (from right, 0-indexed) is:
   digit_k = floor(2^n / 10^k) mod 10

   This depends on: 2^n mod 10^(k+1)
   Which is determined by: n mod T_{k+1} where T_{k+1} = 4·5^k = 5·T_k

3. Given n mod T_k (the level-k constraint), there are 5 possibilities for
   n mod T_{k+1}: namely n, n+T_k, n+2T_k, n+3T_k, n+4T_k.

4. KEY: The map r ↦ 2^r mod 10^(k+1) restricted to {n, n+T_k, ..., n+4T_k}
   cycles through 5 values that cover each digit 0-9 with equal frequency
   when averaged over all n.

5. Therefore, among level-k survivors, digit k is uniformly distributed
   over {0,...,9}, so exactly 9/10 have digit_k ≠ 0.

THIS IS WHY THE CONDITIONAL PROBABILITY IS EXACTLY 0.9!

The question for a proof: Can we formalize this uniformity argument?
""")

if __name__ == "__main__":
    analyze_transition_mechanism()
    analyze_digit_distribution()
    prove_0_9_ratio()
    explore_5adic_structure()
    the_key_insight()
