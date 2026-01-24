#!/usr/bin/env python3
"""
Testing GPT 5.2's Bridge A: Is the killed-child index uniformly distributed locally?

If yes, this gives the discrepancy bound that breaks the circularity.
"""

import sys
sys.set_int_max_str_digits(100000)

def get_killed_index(r, k):
    """
    For a level-k survivor r, find which child index (0-4) is killed at level k+1.
    Returns None if all 5 children survive (5-child case).
    """
    T_k = 4 * 5**(k-1)
    T_k1 = 4 * 5**k

    killed = None
    for j in range(5):
        child = r + j * T_k
        n = child if child >= k + 1 else child + T_k1
        power = pow(2, n, 10**(k+1))

        # Check if last k+1 digits are zeroless
        zeroless = True
        temp = power
        for _ in range(k + 1):
            if temp % 10 == 0:
                zeroless = False
                break
            temp //= 10

        if not zeroless:
            if killed is not None:
                # More than one killed - shouldn't happen!
                return "ERROR: multiple killed"
            killed = j

    return killed  # None means 5-child case

def test_global_uniformity():
    """Test if killed index is uniform globally among 4-child survivors."""
    print("="*70)
    print("TEST: Global uniformity of killed-child index")
    print("="*70)

    for k in range(2, 9):
        T_k = 4 * 5**(k-1)

        # Find all level-k survivors and their killed indices
        killed_counts = {0: 0, 1: 0, 2: 0, 3: 0, 4: 0}
        five_child_count = 0
        survivors = []

        for r in range(T_k):
            n = r if r >= k else r + T_k
            power = pow(2, n, 10**k)
            zeroless = all((power // 10**i) % 10 != 0 for i in range(k))

            if zeroless:
                survivors.append(r)
                ki = get_killed_index(r, k)
                if ki is None:
                    five_child_count += 1
                elif isinstance(ki, int):
                    killed_counts[ki] += 1

        four_child_count = len(survivors) - five_child_count

        print(f"\nk={k}: {len(survivors)} survivors, {four_child_count} have 4 children")
        print(f"  Killed index distribution: {killed_counts}")
        if four_child_count > 0:
            for j in range(5):
                pct = 100 * killed_counts[j] / four_child_count
                print(f"    κ={j}: {killed_counts[j]:5d} ({pct:5.1f}%), expected 20%")

def test_local_uniformity():
    """
    Test if killed index is uniform LOCALLY within cylinders.
    This is the key test for Bridge A.
    """
    print("\n" + "="*70)
    print("TEST: Local uniformity within cylinders (Bridge A)")
    print("="*70)

    for k in range(3, 7):
        T_k = 4 * 5**(k-1)
        block_size = T_k // 5  # Divide into 5 blocks

        print(f"\nk={k}, period={T_k}, block_size={block_size}")
        print(f"Testing uniformity within each of 5 blocks:")

        for block in range(5):
            block_start = block * block_size
            block_end = (block + 1) * block_size

            killed_counts = {0: 0, 1: 0, 2: 0, 3: 0, 4: 0}
            survivors_in_block = 0

            for r in range(block_start, block_end):
                n = r if r >= k else r + T_k
                power = pow(2, n, 10**k)
                zeroless = all((power // 10**i) % 10 != 0 for i in range(k))

                if zeroless:
                    survivors_in_block += 1
                    ki = get_killed_index(r, k)
                    if isinstance(ki, int):
                        killed_counts[ki] += 1

            if survivors_in_block > 0:
                four_child = sum(killed_counts.values())
                if four_child > 0:
                    dist = [f"{j}:{100*killed_counts[j]/four_child:.0f}%" for j in range(5)]
                    print(f"  Block {block} [{block_start:5d}-{block_end:5d}]: "
                          f"{survivors_in_block:4d} survivors, "
                          f"killed dist: {' '.join(dist)}")

def test_cylinder_uniformity():
    """
    Test uniformity within finer cylinders (residue classes mod 5^t).
    """
    print("\n" + "="*70)
    print("TEST: Cylinder uniformity (residue classes mod 5^t)")
    print("="*70)

    k = 6  # Use a moderately large k
    T_k = 4 * 5**(k-1)

    for t in [1, 2, 3]:
        mod = 5**t
        print(f"\nk={k}, testing mod {mod} cylinders:")

        cylinder_stats = {}
        for cyl in range(mod):
            killed_counts = {0: 0, 1: 0, 2: 0, 3: 0, 4: 0}
            survivors = 0

            for r in range(T_k):
                if r % mod != cyl:
                    continue

                n = r if r >= k else r + T_k
                power = pow(2, n, 10**k)
                zeroless = all((power // 10**i) % 10 != 0 for i in range(k))

                if zeroless:
                    survivors += 1
                    ki = get_killed_index(r, k)
                    if isinstance(ki, int):
                        killed_counts[ki] += 1

            four_child = sum(killed_counts.values())
            if four_child >= 10:  # Only report if enough samples
                # Compute max deviation from uniform
                max_dev = max(abs(killed_counts[j]/four_child - 0.2) for j in range(5))
                cylinder_stats[cyl] = (survivors, four_child, max_dev)

        if cylinder_stats:
            avg_dev = sum(s[2] for s in cylinder_stats.values()) / len(cylinder_stats)
            max_max_dev = max(s[2] for s in cylinder_stats.values())
            print(f"  Cylinders with ≥10 four-child: {len(cylinder_stats)}")
            print(f"  Average max deviation from 20%: {avg_dev:.4f}")
            print(f"  Worst max deviation: {max_max_dev:.4f}")

def test_initial_segment_discrepancy():
    """
    The key test: is |S_k ∩ [0,M]| bounded by density * M + small error?
    """
    print("\n" + "="*70)
    print("TEST: Initial segment discrepancy")
    print("="*70)

    for k in range(5, 15):
        T_k = 4 * 5**(k-1)
        density = 0.9**(k-1)

        # Count survivors in initial segment [0, M] for various M
        M_values = [int(3.32 * k), int(10 * k), T_k // 10, T_k // 5]

        survivors = []
        for r in range(T_k):
            n = r if r >= k else r + T_k
            power = pow(2, n, 10**k)
            zeroless = all((power // 10**i) % 10 != 0 for i in range(k))
            if zeroless:
                survivors.append(r)

        print(f"\nk={k}, density={density:.6f}, total survivors={len(survivors)}")

        for M in M_values:
            if M > T_k:
                continue
            count = sum(1 for r in survivors if r < M)
            expected = density * M
            discrepancy = count - expected
            print(f"  M={M:8d}: count={count:6d}, expected={expected:.1f}, "
                  f"discrepancy={discrepancy:+.1f}")

if __name__ == "__main__":
    test_global_uniformity()
    test_local_uniformity()
    test_cylinder_uniformity()
    test_initial_segment_discrepancy()
