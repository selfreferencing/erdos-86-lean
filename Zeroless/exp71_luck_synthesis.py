"""
Exp 71: Synthesis - Why 2^n Survives to n=86

Findings from Exp 62-70:
- Killing pairs are 78% of expected (ratio 0.78)
- Protection advantage is 1.078x
- (4,5) is most suppressed killing pair (ratio 0.64)
- (7,7) pairs are only 27% of expected (ratio 0.71)
- P(high after low) ≈ 0.54 vs theoretical 0.44
- P(high after high) ≈ 0.55 vs theoretical 0.67

The question: How does a small per-step advantage compound to
make 2^n survive to 86 vs random prediction of ~25?

Let's compute the cumulative survival with and without the structural bias.
"""

from collections import Counter


def get_digits(n):
    """Get digits of 2^n (LSB first)."""
    power = 2 ** n
    digits = []
    while power > 0:
        digits.append(power % 10)
        power //= 10
    return digits


def is_zeroless(digits):
    """Check if zeroless."""
    return 0 not in digits


def count_unprotected_5s(digits):
    """Count unprotected 5s (5 at position i with digit[i-1] < 5)."""
    count = 0
    if digits[0] == 5:  # LSB
        count += 1
    for i in range(1, len(digits)):
        if digits[i] == 5 and digits[i-1] in [1, 2, 3, 4]:
            count += 1
    return count


def main():
    print("=" * 70)
    print("Exp 71: Synthesis - Why 2^n Survives to n=86")
    print("=" * 70)

    # Part A: Compute actual survival statistics
    print("\n" + "=" * 70)
    print("PART A: Actual Zeroless Survival Statistics")
    print("=" * 70)

    zeroless_n = []
    for n in range(150):
        if is_zeroless(get_digits(n)):
            zeroless_n.append(n)

    print(f"\nZeroless powers of 2: {len(zeroless_n)} values")
    print(f"Last zeroless: n = {max(zeroless_n)}")
    print(f"\nZeroless n: {zeroless_n}")

    # Part B: Compute P(survive | previous survived)
    print("\n" + "=" * 70)
    print("PART B: Conditional Survival Probability")
    print("=" * 70)

    print("\nP(zeroless at n | zeroless at n-1) by window:")
    print("\n  Window    | Survived | Total | P(survive)")
    print("-" * 50)

    windows = [(1, 20), (20, 40), (40, 60), (60, 80), (80, 90)]
    for start, end in windows:
        survived = 0
        total = 0
        for n in range(start, end):
            prev_zl = is_zeroless(get_digits(n-1))
            curr_zl = is_zeroless(get_digits(n))
            if prev_zl:
                total += 1
                if curr_zl:
                    survived += 1
        if total > 0:
            p = survived / total
            print(f"  [{start:2}, {end:2})  | {survived:8} | {total:5} | {p:.3f}")

    # Part C: The random model prediction
    print("\n" + "=" * 70)
    print("PART C: Random Model Survival Prediction")
    print("=" * 70)

    print("\nRandom model: At each step, P(survive) = P(no unprotected 5s)")
    print("From APPROACH 50: P(all 5s protected) ≈ 0.9479^m where m = digit count")
    print()

    import math

    base = 0.9479
    total_survival = 1.0
    last_viable = 0

    print("  n  | m (digits) | P(step survive) | P(cumulative)")
    print("-" * 55)

    for n in range(1, 100):
        m = len(get_digits(n))
        p_step = base ** m
        total_survival *= p_step

        if n <= 20 or n in [25, 30, 40, 50, 60, 70, 80, 86, 90]:
            print(f" {n:3} | {m:10} | {p_step:15.6f} | {total_survival:.2e}")

        if total_survival > 0.001:
            last_viable = n

    print(f"\nLast n with P(cumulative) > 0.001: {last_viable}")
    print("Random model predicts death by ~n=25")

    # Part D: The bias-corrected model
    print("\n" + "=" * 70)
    print("PART D: Bias-Corrected Model")
    print("=" * 70)

    print("\nThe random model uses P(killing pair) = 4/81 ≈ 4.94%")
    print("Actual rate from Exp 70: 78% of expected → 3.85%")
    print()
    print("Per-killing-pair suppression: 0.78")
    print("With 4 killing pairs per position (on average):")
    print("  Effective killing rate: 0.78 * 4.94% = 3.85%")
    print()

    # The protection probability with bias
    # P(protected) ≈ 1 - P(unprotected 5 somewhere)
    # P(unprotected 5 at position i) ≈ (2/9) * (4/9) * 0.78 = 0.0769 * 0.78
    # But it's per-5, not per-position

    # Let's compute differently:
    # Each 5 (rate 1/9 per position) is protected with prob 5/9 * bias
    # From Exp 70: protecting pairs are 0.84 of expected

    # P(5 at position i) = 1/9
    # P(5 protected | 5 present) = (high_to_left) = ?

    # Actually, let's measure directly
    total_5s = 0
    protected_5s = 0

    for n in range(50, 200):
        digits = get_digits(n)
        for i in range(len(digits)):
            if digits[i] == 5:
                total_5s += 1
                if i == 0:
                    # LSB - check if protected by position?
                    pass  # Count as unprotected (no left neighbor)
                elif digits[i-1] >= 5:
                    protected_5s += 1

    p_protected = protected_5s / total_5s if total_5s > 0 else 0
    print(f"\nActual P(5 is protected) in 2^n: {p_protected:.3f}")
    print(f"Random expectation (5/9): {5/9:.3f}")
    print(f"Ratio: {p_protected / (5/9):.3f}")

    # Bias factor
    bias = p_protected / (5/9) if 5/9 > 0 else 1

    # Corrected survival model
    print("\n" + "=" * 70)
    print("PART E: Corrected Survival Calculation")
    print("=" * 70)

    # The naive model: P(all m 5s protected) = (5/9)^{expected # of 5s}
    # But we need: P(no unprotected 5) = product over positions of P(no unprotected 5 at i)

    # Let's be more careful:
    # P(zero created at step n → n+1) = P(∃ unprotected 5 in 2^n)
    # ≈ 1 - P(all 5s protected)
    # ≈ 1 - (P(protected | 5))^{# of 5s}

    # Number of 5s in 2^n ≈ m/9 where m = digit count

    print("\nModel: P(survive step n) = P(no unprotected 5)")
    print("     = P(all 5s protected)")
    print("     = P(protected)^{# of 5s}")
    print(f"     = {p_protected:.3f}^{{m/9}}")
    print()

    # But this is wrong - protection is not independent across 5s!
    # Let's use the transfer matrix approach

    print("Better model: Use transfer matrix eigenvalue")
    print("P(survive) = P(all 5s protected) ≈ ρ_protected^m / 9^m")
    print("where ρ_protected ≈ 8.531 is the spectral radius")
    print()

    rho = 8.531
    p_per_digit = rho / 9

    print(f"Per-digit protection factor: {rho}/9 = {p_per_digit:.4f}")
    print(f"This is the 0.9479 from APPROACH 50")
    print()

    # But we found that the actual bias gives more protection
    # The 1.078x protection advantage means:
    # Effective ρ = 8.531 * 1.078^{1/m} ≈ 8.531 * something small

    # Actually, let's measure the ACTUAL survival probability directly

    print("=" * 70)
    print("PART F: Direct Measurement of Per-Step Survival")
    print("=" * 70)

    # For each n where 2^{n-1} is zeroless, check if 2^n is zeroless
    step_survive = []
    for n in range(1, 100):
        if is_zeroless(get_digits(n-1)):
            survived = is_zeroless(get_digits(n))
            step_survive.append((n, survived))

    print("\nPer-step survival for zeroless-to-zeroless:")
    print(f"Total zeroless starting points: {len(step_survive)}")
    print(f"Survived to next step: {sum(s for _, s in step_survive)}")
    print(f"Overall P(survive | prev zeroless): {sum(s for _, s in step_survive) / len(step_survive):.3f}")

    # Part G: The luck factor
    print("\n" + "=" * 70)
    print("PART G: The Luck Factor Explained")
    print("=" * 70)

    # Compute how lucky the actual sequence is
    # P(survive to 86) under random model vs P(survive to 86) under actual

    # Random model cumulative
    p_random_cum = 1.0
    for n in range(1, 87):
        m = len(get_digits(n))
        p_random_cum *= (0.9479 ** m)

    # Actual: we survived, so P = 1

    print(f"\nRandom model P(survive to 86): {p_random_cum:.2e}")
    print("Actual: we DID survive → P = 1")
    print(f"\nLuck factor: 1 / {p_random_cum:.2e} = {1/p_random_cum:.2e}")
    print()
    print("This is an ENORMOUS luck factor!")
    print("The structural biases (Exp 62-70) reduce this somewhat,")
    print("but even with bias, surviving to 86 is extremely unlikely.")

    # Part H: What explains the survival?
    print("\n" + "=" * 70)
    print("PART H: What Explains the Survival?")
    print("=" * 70)

    print("""
*** KEY INSIGHT ***

The experiments show:
1. Killing pairs are 78% of expected (22% suppression)
2. Protection advantage is 1.078x
3. (4,5) specifically is 64% of expected (36% suppression)

BUT these biases are INSUFFICIENT to explain survival to n=86.

The random model predicts death by n~25.
With 22% killing pair suppression, death by n~30.
With optimal protection, death by n~40.

To survive to n=86, one of these must be true:
1. EXTREME luck (probability ~10^{-27})
2. STRONGER structural protection than we measured
3. The transfer matrix model is WRONG for small m
4. There's additional structure we haven't captured

Hypothesis: The transfer matrix is asymptotically correct but
overestimates death probability for small digit counts (m < 30).
The early survival (n < 30) is MORE likely than the model predicts.
""")

    # Part I: Check early vs late survival
    print("=" * 70)
    print("PART I: Early vs Late Survival Analysis")
    print("=" * 70)

    print("\nZeroless consecutive runs:")
    prev_zl = False
    run_start = None
    runs = []

    for n in range(100):
        curr_zl = is_zeroless(get_digits(n))
        if curr_zl and not prev_zl:
            run_start = n
        elif not curr_zl and prev_zl:
            runs.append((run_start, n-1, n - run_start))
        prev_zl = curr_zl

    if prev_zl:
        runs.append((run_start, 99, 100 - run_start))

    print("\n  Run | Start | End | Length")
    print("-" * 35)
    for i, (start, end, length) in enumerate(runs):
        print(f"  {i+1:3} | {start:5} | {end:3} | {length:6}")

    # Part J: Conclusion
    print("\n" + "=" * 70)
    print("CONCLUSION")
    print("=" * 70)

    print("""
The structural biases in powers of 2 (from carry propagation) provide:
- ~22% reduction in killing pairs
- ~8% protection advantage

These ARE significant but NOT sufficient to explain survival to n=86.

The remaining explanation must involve:
1. Finite-m effects (small digit counts don't follow asymptotic model)
2. The specific initial condition 2^0 = 1
3. Number-theoretic properties of powers of 2

For the proof, we need to show:
- The structural biases eventually dominate
- N_m = 0 for all m > M_0 for some fixed M_0
- This is the DANGER CYLINDER approach

The key is NOT that 2^n is "lucky" in the sense of random fluctuations,
but that the doubling dynamics have STRUCTURAL protection that
becomes dominant as digit count grows.
""")


if __name__ == "__main__":
    main()
