#!/usr/bin/env python3
"""
QR gap covering v2: Direct enumeration of small DP congruences.

For each (delta, u, v) with delta ≡ 3 (mod 4), u+v = delta, u,v > 0:
  Congruence: P ≡ -(u+v) (mod 4*lcm(u,v))

Build a covering of the 6 QR gap classes mod 840 incrementally.
"""

from math import gcd
import time


def lcm2(a, b):
    return a * b // gcd(a, b)


def factorize(n):
    factors = {}
    d = 2
    while d * d <= n:
        while n % d == 0:
            factors[d] = factors.get(d, 0) + 1
            n //= d
        d += 1
    if n > 1:
        factors[n] = factors.get(n, 0) + 1
    return factors


def main():
    t0 = time.time()

    # Start: 6 QR gap classes mod 840
    Q = 840
    targets = set()
    for x in range(1, Q, 24):
        if gcd(x, Q) != 1:
            continue
        if x % 7 in (1, 2, 4) and x % 5 in (1, 4):
            targets.add(x)

    print(f"Q = {Q}, QR gap targets: {len(targets)}")
    print(f"Classes: {sorted(targets)}")
    print()

    # Enumerate DP congruences, sorted by delta
    covered = set()
    selected = []
    max_Q = 500_000_000  # 500M

    for delta in range(3, 5001, 4):
        if covered >= targets:
            break

        for u in range(1, (delta + 1) // 2 + 1):
            v = delta - u
            if v <= 0:
                continue
            L = lcm2(u, v)
            modulus = 4 * L
            res = (-delta) % modulus

            # Check compatibility with P ≡ 1 (mod 24)
            g = gcd(modulus, 24)
            if res % g != 1 % g:
                continue

            # Check what this covers
            new_Q = lcm2(Q, modulus)
            if new_Q > max_Q:
                continue

            # If Q changes, lift targets
            if new_Q != Q:
                new_targets = set()
                for x in range(new_Q):
                    if x % 24 != 1:
                        continue
                    if gcd(x, new_Q) != 1:
                        continue
                    if x % 7 in (1, 2, 4) and x % 5 in (1, 4):
                        new_targets.add(x)

                # Lift covered
                new_covered = set()
                for x in new_targets:
                    if x % Q in covered:
                        new_covered.add(x)

                # DP coverage
                dp_new = set()
                for x in new_targets:
                    if x not in new_covered and x % modulus == res:
                        dp_new.add(x)

                if len(dp_new) > 0:
                    Q = new_Q
                    targets = new_targets
                    covered = new_covered | dp_new
                    selected.append((delta, u, v, modulus, res, len(dp_new)))

                    pct = 100.0 * len(covered) / len(targets)
                    print(f"#{len(selected):>3}: delta={delta:>4}, u={u:>4}, v={v:>4}, "
                          f"mod={modulus:>8}, P≡{res}(mod {modulus}), "
                          f"+{len(dp_new):>4} → {len(covered)}/{len(targets)} "
                          f"({pct:.4f}%) Q={Q:,}")

                    if covered >= targets:
                        break
            else:
                # Q doesn't change, just check coverage within existing targets
                dp_new = set()
                for x in targets:
                    if x not in covered and x % modulus == res:
                        dp_new.add(x)

                if len(dp_new) > 0:
                    covered |= dp_new
                    selected.append((delta, u, v, modulus, res, len(dp_new)))

                    pct = 100.0 * len(covered) / len(targets)
                    print(f"#{len(selected):>3}: delta={delta:>4}, u={u:>4}, v={v:>4}, "
                          f"mod={modulus:>8}, P≡{res}(mod {modulus}), "
                          f"+{len(dp_new):>4} → {len(covered)}/{len(targets)} "
                          f"({pct:.4f}%) Q={Q:,}")

                    if covered >= targets:
                        break

        if covered >= targets:
            break

    # Summary
    print(f"\n{'=' * 78}")
    if covered >= targets:
        print(f"*** COMPLETE DP COVERING ***")
    else:
        remaining = targets - covered
        print(f"INCOMPLETE: {len(remaining)}/{len(targets)} uncovered")
        # Show distribution
        for m in [7, 5, 11, 13, 17, 19, 23]:
            if Q % m == 0:
                dist = {}
                for x in remaining:
                    r = x % m
                    dist[r] = dist.get(r, 0) + 1
                if dist:
                    print(f"  Uncovered mod {m}: {sorted(dist.items())}")

    print(f"\nQ = {Q:,}")
    facs = factorize(Q)
    print(f"  = " + " * ".join(f"{p}^{e}" if e > 1 else str(p)
                                 for p, e in sorted(facs.items())))
    print(f"DP constructions used: {len(selected)}")
    print(f"Targets mod Q: {len(targets)}")
    print(f"Covered: {len(covered)}")

    # Print selected constructions
    print(f"\nSelected DP constructions:")
    for i, (delta, u, v, mod, res, gain) in enumerate(selected):
        print(f"  #{i+1}: delta={delta}, u={u}, v={v}, mod={mod}, "
              f"P≡{res}(mod {mod}), gain={gain}")

    elapsed = time.time() - t0
    print(f"\nTotal time: {elapsed:.1f}s")


if __name__ == "__main__":
    main()
