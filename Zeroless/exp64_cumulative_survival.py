"""
Exp 64: Cumulative Survival Probability

The key insight from Exp 63: P(zeroless | prev zeroless) drops with n.

The orbit survives from n=0 to n=N only if ALL intermediate steps are zeroless.
This is a PRODUCT of survival probabilities, not a single-point probability.

Let's compute the expected "last survivor" under this cumulative model.
"""

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


def main():
    print("=" * 70)
    print("Exp 64: Cumulative Survival Probability")
    print("=" * 70)

    # Part A: Compute P(zeroless | prev zeroless) for each n
    print("\n" + "=" * 70)
    print("PART A: Transition Probabilities")
    print("=" * 70)

    # For powers of 2, track transitions
    transitions = []  # (n, prev_zeroless, curr_zeroless)

    for n in range(1, 300):
        prev_zl = is_zeroless(get_digits(n-1))
        curr_zl = is_zeroless(get_digits(n))
        transitions.append((n, prev_zl, curr_zl))

    # Compute P(zeroless at n | zeroless at n-1) in windows
    print("\nP(zeroless at n | zeroless at n-1) in windows:")
    print("\n  Window  | Transitions | Successes | P(survival)")
    print("-" * 55)

    windows = [(0, 20), (20, 40), (40, 60), (60, 80), (80, 100), (100, 150), (150, 200), (200, 300)]

    for start, end in windows:
        count = 0
        success = 0
        for n, prev_zl, curr_zl in transitions:
            if start <= n < end and prev_zl:
                count += 1
                if curr_zl:
                    success += 1
        if count > 0:
            p = success / count
            print(f"  [{start:3}, {end:3}) | {count:11} | {success:9} | {p:.3f}")
        else:
            print(f"  [{start:3}, {end:3}) | {count:11} | {'N/A':9} | N/A")

    # Part B: Cumulative survival from n=0
    print("\n" + "=" * 70)
    print("PART B: Cumulative Survival Probability")
    print("=" * 70)

    print("\nP(reach n while staying zeroless) = product of all transition probs")

    # Compute actual cumulative survival
    cumulative = 1.0
    zeroless_n = []
    last_zeroless = 0

    print("\n  n  | Is zeroless | # zeroless so far | Last zeroless")
    print("-" * 60)

    for n in range(150):
        zl = is_zeroless(get_digits(n))
        if zl:
            zeroless_n.append(n)
            last_zeroless = n

        if n <= 20 or n >= 80 or zl:
            print(f" {n:3} | {str(zl):11} | {len(zeroless_n):17} | {last_zeroless}")

    # Part C: The "expected last survivor" calculation
    print("\n" + "=" * 70)
    print("PART C: Expected Last Survivor Under Random Model")
    print("=" * 70)

    # Model: at each step n, P(survive) depends on digit count m ≈ 0.301n
    # From APPROACH 50: P(protected) ≈ 0.9479^m

    print("\nModel: P(survive step n) = 0.9479^{0.301n}")
    print("Cumulative: P(survive to N) = prod_{n=1}^{N} 0.9479^{0.301n}")
    print("                            = 0.9479^{0.301 * sum_{n=1}^N n}")
    print("                            = 0.9479^{0.301 * N(N+1)/2}")
    print()

    import math

    base = 0.9479
    coef = 0.301

    print("  N  | Sum(m) | P(cumulative) | Expected # survivors beyond N")
    print("-" * 65)

    for N in [20, 40, 60, 80, 86, 100, 120, 150, 200, 250]:
        sum_m = coef * N * (N + 1) / 2
        p_cum = base ** sum_m
        expected_beyond = p_cum * (300 - N)  # Crude estimate
        print(f" {N:3} | {sum_m:6.1f} | {p_cum:.2e}       | {expected_beyond:.2e}")

    # Part D: When does P(cumulative) drop below various thresholds?
    print("\n" + "=" * 70)
    print("PART D: Threshold Analysis")
    print("=" * 70)

    thresholds = [0.5, 0.1, 0.01, 0.001, 0.0001]

    print("\nN such that P(survive to N) < threshold:")

    for thresh in thresholds:
        # Solve: 0.9479^{0.301 * N(N+1)/2} = thresh
        # 0.301 * N(N+1)/2 * log(0.9479) = log(thresh)
        # N(N+1) = 2 * log(thresh) / (0.301 * log(0.9479))

        log_base = math.log(base)
        log_thresh = math.log(thresh)

        # N^2 + N - 2*log_thresh/(0.301*log_base) = 0
        a = 1
        b = 1
        c = -2 * log_thresh / (coef * log_base)

        N_thresh = (-b + math.sqrt(b**2 - 4*a*c)) / (2*a)
        print(f"  P < {thresh}: N ≈ {N_thresh:.1f}")

    # Part E: The actual vs model comparison
    print("\n" + "=" * 70)
    print("PART E: Actual vs Model Comparison")
    print("=" * 70)

    print("\nActual zeroless powers: n ∈ {", end="")
    print(", ".join(str(n) for n in zeroless_n), end="}\n")
    print(f"Count: {len(zeroless_n)}, Last: {max(zeroless_n)}")

    print("\nModel predictions (using 0.9479^m approximation):")
    print("  P(survive to 86) ≈ 0.9479^{0.301 * 86*87/2}")
    sum_86 = 0.301 * 86 * 87 / 2
    p_86 = 0.9479 ** sum_86
    print(f"                    = 0.9479^{sum_86:.1f}")
    print(f"                    = {p_86:.2e}")
    print()
    print("  This is EXTREMELY small, suggesting the orbit 'should' have died earlier.")
    print("  The fact it survived to 86 indicates the orbit is LUCKIER than random.")

    # Part F: Alternative model - step-by-step survival
    print("\n" + "=" * 70)
    print("PART F: Step-by-Step Survival (More Accurate Model)")
    print("=" * 70)

    print("\nModel: P(survive step n→n+1 | survived to n) = 0.9479^{m_n}")
    print("where m_n = number of digits in 2^n")

    print("\n  n | m_n | P(step) | P(cumulative)")
    print("-" * 45)

    p_cumulative = 1.0
    for n in range(0, 100, 5):
        m_n = len(get_digits(n))
        p_step = base ** m_n
        p_cumulative *= p_step
        print(f" {n:3} | {m_n:3} | {p_step:.4f}  | {p_cumulative:.2e}")


if __name__ == "__main__":
    main()
