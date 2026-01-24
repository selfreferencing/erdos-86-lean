#!/usr/bin/env python3
"""
For the K13 failures, find which k values DO work.
"""

FAILURES = [10170169, 11183041, 22605361, 24966481, 30573481, 30619801,
            34103161, 35241529, 36851929, 36869281, 37228801, 45575401,
            46936849, 48991849]

def x_k(p, k):
    m = 4*k + 3
    return (p + m) // 4 if (p + m) % 4 == 0 else None

def has_witness(p, k):
    m = 4*k + 3
    x = x_k(p, k)
    if x is None:
        return False
    target = (-x) % m
    if target == 0:
        target = m
    x_sq = x * x
    d = target
    while d <= x:
        if d > 0 and x_sq % d == 0:
            return True
        d += m
    return False

def find_working_k(p, max_k=100):
    """Find all k values that work for prime p."""
    working = []
    for k in range(max_k + 1):
        if has_witness(p, k):
            working.append(k)
    return working

def main():
    print("Finding working k values for K13 failures")
    print("=" * 60)

    all_working = set()

    for p in FAILURES:
        working = find_working_k(p, max_k=200)
        all_working.update(working)
        print(f"\np = {p} (mod 840 = {p % 840}):")
        print(f"  Working k values: {working[:20]}{'...' if len(working) > 20 else ''}")
        print(f"  Count: {len(working)} working k's in [0, 200]")

        # Show smallest working k
        if working:
            k = working[0]
            m = 4*k + 3
            x = x_k(p, k)
            print(f"  Smallest: k={k}, m_k={m}, x_k={x}")

    print("\n" + "=" * 60)
    print("All k values that work for at least one failure:")
    print(sorted(all_working)[:30])
    print(f"Total: {len(all_working)} distinct k values")

    # Find k values that work for ALL failures
    print("\nk values that work for ALL failures:")
    universal = None
    for p in FAILURES:
        working = set(find_working_k(p, max_k=200))
        if universal is None:
            universal = working
        else:
            universal &= working
    print(sorted(universal)[:20] if universal else "None!")

if __name__ == "__main__":
    main()
