#!/usr/bin/env python3
"""
Experiment 19: Conditional Survival Probability for Small Indices

NEW APPROACH: Instead of Fourier analysis (which loses too much to absolute
values), track the conditional survival probability directly.

For a specific orbit index i (representing exponent n = m + i), track:

    P_m(i) = Prob(i survives all m digit checks)

where "Prob" here means the ACTUAL indicator (0 or 1), not a probabilistic
estimate.

The key insight from exp16: for i < i_low(m) ~ 2.32*m, the orbit element
2^n mod 10^m = 2^n (no reduction), and 2^n < 10^{m-1}, so the leading
digit is 0 and the element is killed. So P_m(i) = 0 for i < i_low(m).

For i in [i_low(m), i_high(m)] (the transition zone, ~3-4 indices wide),
D(n) = m, and i survives iff 2^n is zeroless. This is exactly the 86
conjecture itself.

For i > i_high(m), the behavior should be "generic" -- the orbit element
has been reduced mod 10^m, and survival looks random at rate (9/10)^m.

WHAT THIS EXPERIMENT DOES:

Part A: For each candidate n > 86 with D(n) = m (i.e., i in transition zone),
  track survival through digits 1, 2, ..., m. At which digit does it fail?

Part B: For the "generic" zone (i > i_high), compute the empirical
  conditional survival rate: P(digit j+1 nonzero | survived digits 1..j).
  Compare to 9/10.

Part C: The Independence Test. For each i in the transition zone, compute
  the conditional probabilities of each digit being nonzero given survival
  of all previous digits. Are these independent of each other? If digit j
  and digit j+1 have conditional probabilities that aren't close to (9/10)^2,
  there's correlation we could exploit.

Part D: Track the 35 known zeroless powers. For each n, compute:
  - At level D(n), all digits are nonzero (by definition)
  - At level D(n)+1, the leading digit is 0 (because 2^n < 10^{D(n)+1})
  - At which INTERIOR digit does the nearest non-zeroless power fail?
"""

import sys
import os
import json
import time
import math

sys.set_int_max_str_digits(100000)

DATA_DIR = os.path.join(os.path.dirname(__file__), "data")
os.makedirs(DATA_DIR, exist_ok=True)

LOG10_2 = math.log10(2)

# All 35 known zeroless powers
KNOWN_ZEROLESS = [
    1, 2, 3, 4, 5, 6, 7, 8, 9, 13, 14, 15, 16, 18, 19,
    24, 25, 27, 28, 31, 32, 33, 34, 35, 36, 37, 39, 49,
    51, 67, 72, 76, 77, 81, 86
]

M_MAX = 12  # Check more levels since per-element work is cheap


def digit_count(n):
    """D(n) = number of digits of 2^n."""
    return int(n * LOG10_2) + 1


def i_low(m):
    """First orbit index where D(n) >= m, i.e., 2^n has at least m digits."""
    return math.ceil((m - 1) / LOG10_2) - m


def i_high(m):
    """Last orbit index where D(n) = m exactly."""
    return math.ceil(m / LOG10_2) - m - 1


def get_digits(x, m):
    """Extract the m digits of x (least significant first)."""
    digits = []
    for _ in range(m):
        digits.append(x % 10)
        x //= 10
    return digits


def part_A_transition_zone():
    """For each m, examine the transition zone indices."""
    print("=" * 100)
    print("PART A: Transition Zone Analysis")
    print("  For each m, the transition zone [i_low, i_high] contains the indices")
    print("  where D(n) = m. These are the only candidates for zeroless 2^n at level m.")
    print("=" * 100)

    print(f"\n{'m':>3}  {'i_low':>6}  {'i_high':>6}  {'width':>5}  candidates")
    print("-" * 80)

    all_results = []

    for m in range(1, M_MAX + 1):
        il = i_low(m)
        ih = i_high(m)
        width = ih - il + 1

        # For each candidate index, check all digits
        candidates = []
        for i in range(max(0, il), ih + 1):
            n = m + i
            if n < 0:
                continue
            val = pow(2, n)
            d = digit_count(n)
            if d != m:
                continue
            s = str(val)
            is_zeroless = '0' not in s
            # Find first zero digit (from right = least significant)
            first_zero = None
            for pos, ch in enumerate(reversed(s)):
                if ch == '0':
                    first_zero = pos + 1  # 1-indexed digit position
                    break

            candidates.append({
                "n": n, "i": i, "D_n": d,
                "zeroless": is_zeroless,
                "first_zero_digit": first_zero,
                "value_prefix": s[:min(20, len(s))],
            })

        surviving = [c for c in candidates if c["zeroless"]]
        failing = [c for c in candidates if not c["zeroless"]]

        cand_str = ""
        for c in candidates:
            mark = "Z" if c["zeroless"] else f"x@{c['first_zero_digit']}"
            cand_str += f" n={c['n']}({mark})"

        print(f"{m:>3}  {il:>6}  {ih:>6}  {width:>5} {cand_str}")

        all_results.append({
            "m": m, "i_low": il, "i_high": ih, "width": width,
            "candidates": candidates,
            "n_surviving": len(surviving),
            "n_failing": len(failing),
        })

    return all_results


def part_B_conditional_rates(max_m=10):
    """Compute conditional digit-survival rates in the generic zone."""
    print("\n" + "=" * 100)
    print("PART B: Conditional Survival Rates in Generic Zone (i > i_high)")
    print("  P(digit j+1 nonzero | survived digits 1..j)")
    print("=" * 100)

    for m in range(2, min(max_m + 1, M_MAX + 1)):
        T = 4 * 5 ** (m - 1)
        mod = 10 ** m
        min_val = mod // 10
        ih = i_high(m)

        # Only scan generic zone: i > ih (but cap at reasonable number)
        scan_end = min(T, max(500, ih + 500))
        start_i = max(0, ih + 1)

        # Track survival through digit levels
        # survived_to[j] = count of indices surviving first j digits
        survived_to = [0] * (m + 1)
        total_checked = 0

        x = pow(2, m + start_i, mod)  # start orbit at index start_i
        for i in range(start_i, scan_end):
            total_checked += 1
            digits = get_digits(x, m)

            # Check digit by digit (1=ones, 2=tens, ..., m=leading)
            survived = True
            for j in range(m):
                if survived:
                    survived_to[j + 1] += 1
                    if digits[j] == 0:
                        survived = False

            x = (x * 2) % mod

        # Compute conditional rates
        print(f"\nm={m}: checked {total_checked} elements in [{start_i}, {scan_end})")
        print(f"  {'digit':>5}  {'survived':>10}  {'cond_rate':>10}  {'expected':>10}  {'ratio':>8}")
        print("  " + "-" * 55)
        survived_to[0] = total_checked
        for j in range(1, m + 1):
            if survived_to[j - 1] > 0:
                rate = survived_to[j] / survived_to[j - 1]
            else:
                rate = 0
            expected = 0.9  # 9/10
            ratio = rate / expected if expected > 0 else 0
            print(f"  {j:>5}  {survived_to[j]:>10}  {rate:>10.6f}  {expected:>10.6f}  {ratio:>8.4f}")

        print(f"  Final survivors: {survived_to[m]} / {total_checked} "
              f"= {survived_to[m]/total_checked:.6f} "
              f"(expected: {0.9**m:.6f})")


def part_C_independence_test(max_m=8):
    """Test pairwise independence of digit conditions.

    For pairs of digits (j, k), compute:
    P(digit j nonzero AND digit k nonzero) vs P(j nonzero) * P(k nonzero)
    """
    print("\n" + "=" * 100)
    print("PART C: Pairwise Independence of Digit Conditions")
    print("=" * 100)

    for m in range(2, min(max_m + 1, 8)):
        T = 4 * 5 ** (m - 1)
        mod = 10 ** m
        ih = i_high(m)

        scan_end = min(T, max(1000, ih + 1000))
        start_i = max(0, ih + 1)

        # Count single and joint survival
        single = [0] * m  # single[j] = count with digit j+1 nonzero
        joint = [[0]*m for _ in range(m)]  # joint[j][k]
        total = 0

        x = pow(2, m + start_i, mod)
        for i in range(start_i, scan_end):
            total += 1
            digits = get_digits(x, m)
            nz = [1 if d != 0 else 0 for d in digits]
            for j in range(m):
                single[j] += nz[j]
                for k in range(j, m):
                    joint[j][k] += nz[j] * nz[k]
            x = (x * 2) % mod

        # Print correlation matrix
        print(f"\nm={m}: {total} elements scanned")
        print(f"  Marginal rates: {[round(s/total, 4) for s in single]}")
        print(f"\n  Joint / (marginal * marginal) ratios:")
        print(f"  {'':>3}", end="")
        for k in range(m):
            print(f"  d{k+1:>2}", end="")
        print()

        for j in range(m):
            print(f"  d{j+1}", end="")
            for k in range(m):
                if k < j:
                    print(f"  {'':>4}", end="")
                else:
                    pj = single[j] / total
                    pk = single[k] / total
                    pjk = joint[j][k] / total
                    expected = pj * pk
                    ratio = pjk / expected if expected > 0 else 0
                    print(f"  {ratio:>4.3f}", end="")
            print()


def part_D_known_zeroless():
    """Track known zeroless powers through digit levels."""
    print("\n" + "=" * 100)
    print("PART D: Known Zeroless Powers -- Digit-Level Survival Profile")
    print("=" * 100)

    print(f"\n{'n':>4}  {'D(n)':>4}  {'2^n':>30}  digit_profile")
    print("-" * 100)

    for n in KNOWN_ZEROLESS:
        d = digit_count(n)
        val = pow(2, n)
        s = str(val)

        # Digit profile: for each prefix length j=1..D(n), is it zeroless?
        profile = ""
        for j in range(1, d + 1):
            # Last j digits
            suffix = s[-(j):]
            if '0' in suffix:
                profile += "x"
            else:
                profile += "v"

        # Also check n+1 and n-1
        nearby = {}
        for delta in [-2, -1, 1, 2]:
            nn = n + delta
            if nn >= 0:
                vv = pow(2, nn)
                ss = str(vv)
                first_zero = None
                for pos, ch in enumerate(reversed(ss)):
                    if ch == '0':
                        first_zero = pos + 1
                        break
                nearby[delta] = first_zero

        val_str = s if len(s) <= 30 else s[:15] + "..." + s[-12:]
        nearby_str = ", ".join(f"n{'+' if d > 0 else ''}{d}:z@{v}"
                               for d, v in sorted(nearby.items()) if v)

        print(f"{n:>4}  {d:>4}  {val_str:>30}  {profile}  [{nearby_str}]")

    # Summary: at which digit do nearby exponents first get a zero?
    print("\n\nSummary: First zero digit of 2^n for n near known zeroless powers")
    print(f"{'n':>4}  {'D(n)':>4}  n-2  n-1  n+1  n+2")
    print("-" * 40)
    for n in KNOWN_ZEROLESS:
        d = digit_count(n)
        entries = []
        for delta in [-2, -1, 1, 2]:
            nn = n + delta
            if nn >= 0:
                vv = pow(2, nn)
                ss = str(vv)
                fz = None
                for pos, ch in enumerate(reversed(ss)):
                    if ch == '0':
                        fz = pos + 1
                        break
                entries.append(str(fz) if fz else "-")
            else:
                entries.append("-")
        print(f"{n:>4}  {d:>4}  {'  '.join(f'{e:>3}' for e in entries)}")


def main():
    print("=" * 100)
    print("EXPERIMENT 19: CONDITIONAL SURVIVAL PROBABILITY FOR SMALL INDICES")
    print("=" * 100)
    print()

    t_start = time.time()

    results_A = part_A_transition_zone()
    part_B_conditional_rates()
    part_C_independence_test()
    part_D_known_zeroless()

    total = time.time() - t_start
    print(f"\nTotal elapsed: {total:.1f}s")

    # Save
    save_data = {
        "_meta": {"M_MAX": M_MAX, "KNOWN_ZEROLESS": KNOWN_ZEROLESS},
        "transition_zone": results_A,
    }
    path = os.path.join(DATA_DIR, "exp19_results.json")
    with open(path, 'w') as fp:
        json.dump(save_data, fp, indent=2, default=str)
    print(f"Results saved to {path}")


if __name__ == '__main__':
    main()
