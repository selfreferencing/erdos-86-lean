#!/usr/bin/env python3
"""
Experiment 11b: Parity Balance with CORRECTED classification.

The C-series derivation assumed the parity type for the lift from level m
to level m+1 depends on u < 5^m/2, where u is the level-m 5-adic parameter.

But the correct condition is: w = u * 2^{-1} mod 5^m < 5^m/2.

This is because the digit at position m+1 is floor(2*u_{m+1}/5^m), and
u_{m+1} = u_m * 2^{-1} + a*5^m (the factor of 2^{-1} comes from the
level shift: x = 2^m * u_m at level m, x = 2^{m+1} * u_{m+1} at level m+1,
so u_{m+1} = u_m / 2 mod 5^m).

We also test a THIRD classification: the direct approach.
For each level-m survivor, enumerate its 5 lifts, check which digit
parity class they fall in, and classify accordingly.
"""

import sys
import os
import json
import time

sys.set_int_max_str_digits(100000)

DATA_DIR = os.path.join(os.path.dirname(__file__), "data")
os.makedirs(DATA_DIR, exist_ok=True)

M_MAX = 10  # smaller for speed


def is_m_digit_zeroless(x, m):
    for _ in range(m):
        if x % 10 == 0:
            return False
        x //= 10
    return True


def main():
    print("Experiment 11b: Corrected Parity Classification")
    print("=" * 70)

    results = {}

    for m in range(1, M_MAX + 1):
        mod_m = 10 ** m
        mod_m1 = 10 ** (m + 1)
        mod5m = 5 ** m
        mod5m1 = 5 ** (m + 1)
        period_m = 4 * (5 ** (m - 1))
        period_m1 = 4 * (5 ** m)
        threshold = mod5m / 2.0

        inv2_m = pow(2, -1, mod5m)  # 2^{-1} mod 5^m = (5^m+1)/2
        inv2m_m = pow(2, -m, mod5m)  # 2^{-m} mod 5^m

        t0 = time.time()

        # Method 1: Original (WRONG) classification: u < 5^m/2
        # Method 2: Corrected classification: w = u * 2^{-1} mod 5^m < 5^m/2
        # Method 3: Direct: enumerate lifts and check digit parity

        x = pow(2, m, mod_m)
        E1 = O1 = 0  # wrong
        E2 = O2 = 0  # corrected
        E3 = O3 = 0  # direct
        Z_m = 0

        survivors = []

        for i in range(period_m):
            if is_m_digit_zeroless(x, m):
                Z_m += 1
                u = (x * inv2m_m) % mod5m

                # Method 1: u < threshold
                if u < threshold:
                    E1 += 1
                else:
                    O1 += 1

                # Method 2: w = u * inv2 mod 5^m < threshold
                w = (u * inv2_m) % mod5m
                if w < threshold:
                    E2 += 1
                else:
                    O2 += 1

                survivors.append((x, u))

            x = (x * 2) % mod_m

        # Method 3: For each survivor, check digit m+1 parity via direct lift
        # Only do this for small m (expensive otherwise)
        if m <= 8:
            E3 = O3 = 0
            for (x_surv, u_surv) in survivors:
                # The 5 lifts at level m+1
                # x' = 2^{m+1} * v mod 10^{m+1} where v = w + a*5^m
                # w = u * inv(2) mod 5^m
                # But actually, let's just directly compute the 5 lifts
                # as x_surv + d * 10^m for d = 0,...,9 and pick the 5 in the orbit

                # Actually, the 5 orbit lifts are obtained by running the orbit at level m+1
                # and filtering for those that reduce to x_surv at level m.
                # That's expensive. Instead, use the parametrization.

                # v = u_surv * inv(2, 5^{m+1}) mod 5^{m+1} ... no.
                # Let me just check the digit at position m+1 for the first lift.

                # Actually, simplest approach: compute x_surv + d*10^m for all d,
                # check which are in the orbit (divisible by 2^{m+1} and unit mod 5^{m+1}).
                found_parity = None
                for d in range(10):
                    x_lift = x_surv + d * (10 ** m)
                    # Check if x_lift is in the orbit at level m+1:
                    # Must be divisible by 2^{m+1} and x_lift / 2^{m+1} must be coprime to 5
                    if x_lift % (2 ** (m + 1)) == 0:
                        v = x_lift // (2 ** (m + 1))
                        if v % 5 != 0:
                            # This d is a valid lift. Check its parity.
                            if found_parity is None:
                                found_parity = d % 2
                            break

                if found_parity == 0:
                    E3 += 1
                else:
                    O3 += 1

        elapsed = time.time() - t0

        r1 = E1 / Z_m if Z_m > 0 else 0
        r2 = E2 / Z_m if Z_m > 0 else 0
        r3 = E3 / Z_m if Z_m > 0 else 0

        S1 = 1.0 - E1 / (5.0 * Z_m) if Z_m > 0 else 0
        S2 = 1.0 - E2 / (5.0 * Z_m) if Z_m > 0 else 0
        S3 = 1.0 - E3 / (5.0 * Z_m) if Z_m > 0 else 0

        results[m] = {
            'Z_m': Z_m, 'E1': E1, 'O1': O1, 'E2': E2, 'O2': O2,
            'E3': E3, 'O3': O3, 'r1': r1, 'r2': r2, 'r3': r3,
            'S1': S1, 'S2': S2, 'S3': S3,
        }

        print(f"\nm = {m} | Z_m = {Z_m:,d} | elapsed = {elapsed:.2f}s")
        print(f"  Method 1 (u < 5^m/2):        E/Z = {r1:.8f}  S = {S1:.8f}")
        print(f"  Method 2 (u*inv2 < 5^m/2):    E/Z = {r2:.8f}  S = {S2:.8f}")
        if m <= 8:
            print(f"  Method 3 (direct digit check): E/Z = {r3:.8f}  S = {S3:.8f}")

    # Now verify the identity Z_{m+1} = 4*E + 5*O for each method
    print("\n" + "=" * 70)
    print("VERIFY: Z_{m+1} = 4*E_m + 5*O_m")
    print("=" * 70)

    ms = sorted(results.keys())
    print(f"\n{'m':>4} {'Z_{m+1}':>12} {'4E1+5O1':>12} {'4E2+5O2':>12} {'4E3+5O3':>12}")
    print("-" * 56)
    for i in range(len(ms) - 1):
        m = ms[i]
        m1 = ms[i + 1]
        if m1 != m + 1:
            continue
        r = results[m]
        z_next = results[m1]['Z_m']
        pred1 = 4 * r['E1'] + 5 * r['O1']
        pred2 = 4 * r['E2'] + 5 * r['O2']
        pred3 = 4 * r['E3'] + 5 * r['O3'] if r['E3'] > 0 else 0
        match1 = "Y" if pred1 == z_next else "N"
        match2 = "Y" if pred2 == z_next else "N"
        match3 = "Y" if pred3 == z_next else "N" if r['E3'] > 0 else "-"
        print(f"{m:4d} {z_next:12,d} {pred1:12,d}({match1}) {pred2:12,d}({match2}) {pred3:12,d}({match3})")

    # Summary table
    print("\n" + "=" * 70)
    print("SUMMARY: E/Z ratios by method")
    print("=" * 70)
    print(f"\n{'m':>4} {'Method1':>12} {'Method2':>12} {'Method3':>12}")
    for m in ms:
        r = results[m]
        m3 = f"{r['r3']:.8f}" if r['E3'] > 0 else "---"
        print(f"{m:4d} {r['r1']:12.8f} {r['r2']:12.8f} {m3:>12}")


if __name__ == '__main__':
    main()
