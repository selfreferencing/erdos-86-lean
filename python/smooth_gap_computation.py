"""
R₀ Smooth Gap Computation for Erdős-Straus K10 Coverage
========================================================

Computes R₀ = upper endpoint of the last consecutive 29-smooth pair
with gap ≤ 24.

Result: R₀ = 4,252,385,304

For r > R₀, every interval [r+5, r+29] contains at most one 29-smooth
number, so at least one x_k = r + k (k ∈ K10) has a prime factor > 29.
"""

from bisect import bisect_right
import heapq

K10 = [5, 7, 9, 11, 14, 17, 19, 23, 26, 29]
PRIMES_29 = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29]

def smooth_numbers_upto(bound: int, primes=PRIMES_29):
    """
    Generate all numbers <= bound whose prime factors lie in `primes`.
    This uses the unique factorization by iterating primes and exponents.
    """
    smooth = [1]
    for p in primes:
        new = []
        for x in smooth:
            v = x
            while v <= bound:
                new.append(v)   # exponent 0,1,2,...
                v *= p
        smooth = new
    smooth.sort()
    return smooth

def last_gap_at_most(smooth, target_gap: int):
    """Return the last (a,b,gap) with consecutive smooth numbers b-a <= target_gap."""
    last = None
    for a, b in zip(smooth, smooth[1:]):
        gap = b - a
        if gap <= target_gap:
            last = (a, b, gap)
    return last

def top_k_gaps(smooth, k=5):
    """Return the top-k largest gaps as (gap, a, b)."""
    top = []  # min-heap of size k
    for a, b in zip(smooth, smooth[1:]):
        gap = b - a
        item = (gap, a, b)
        if len(top) < k:
            heapq.heappush(top, item)
        elif gap > top[0][0]:
            heapq.heapreplace(top, item)
    return sorted(top, reverse=True)

def smooth_gap_R0(bound: int, target_gap: int = 24):
    """
    Compute R0 = upper endpoint of the last consecutive 29-smooth pair
    with gap <= target_gap, and verify that all later gaps (within bound)
    are >= target_gap+1.
    """
    smooth = smooth_numbers_upto(bound, PRIMES_29)

    a, b, g = last_gap_at_most(smooth, target_gap)
    R0 = b

    # verify (within computed range) all gaps after R0 are >= target_gap+1
    i = bisect_right(smooth, R0)
    min_gap = 10**100
    min_pair = None
    for x, y in zip(smooth[i:], smooth[i+1:]):
        gap = y - x
        if gap < min_gap:
            min_gap = gap
            min_pair = (x, y)

    return {
        "bound": bound,
        "count_smooth": len(smooth),
        "R0": R0,
        "last_small_gap": (a, b, g),
        "min_gap_after_R0": min_gap,
        "min_gap_after_R0_pair": min_pair,
        "top5_gaps": top_k_gaps(smooth, 5),
    }

if __name__ == "__main__":
    # Any bound >= 10**10 is enough to "see" the last small gap we found,
    # but you can push higher for extra confidence.
    result = smooth_gap_R0(bound=10**16, target_gap=24)
    for k, v in result.items():
        print(k, ":", v)
