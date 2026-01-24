# TASK: Compute Smooth-Gap Bound R₀

## Context

For the Erdős-Straus proof (Strategy A), we need an explicit bound R₀ such that:

> For all r ≥ R₀, among the 10 integers {r + k : k ∈ K10}, at least one has a prime factor > 29.

Where K10 = {5, 7, 9, 11, 14, 17, 19, 23, 26, 29}.

## What This Means

A number is "29-smooth" if all its prime factors are ≤ 29.

The 29-smooth numbers become increasingly sparse. We need to find R₀ such that no interval [r+5, r+29] of length 25 can consist entirely of 29-smooth numbers for r ≥ R₀.

## Your Task

Write Python code that:

1. **Enumerates 29-smooth numbers** up to some bound
2. **Finds the largest gap** between consecutive 29-smooth numbers
3. **Determines R₀** such that all gaps beyond R₀ are > 24

```python
import sympy
from sympy import primefactors

def is_smooth(n, B):
    """Check if n is B-smooth (all prime factors ≤ B)"""
    if n <= 1:
        return True
    return max(primefactors(n)) <= B

def enumerate_smooth(bound, B):
    """Enumerate all B-smooth numbers up to bound"""
    smooth = []
    for n in range(1, bound + 1):
        if is_smooth(n, B):
            smooth.append(n)
    return smooth

def find_max_gap(smooth_list):
    """Find maximum gap between consecutive smooth numbers"""
    max_gap = 0
    max_gap_location = 0
    for i in range(1, len(smooth_list)):
        gap = smooth_list[i] - smooth_list[i-1]
        if gap > max_gap:
            max_gap = gap
            max_gap_location = smooth_list[i-1]
    return max_gap, max_gap_location

def find_R0(B, target_gap):
    """
    Find R₀ such that all gaps in B-smooth numbers beyond R₀ are > target_gap.
    Uses the fact that smooth numbers become sparse.
    """
    # Start with a reasonable bound and increase if needed
    bound = 10**7
    smooth = enumerate_smooth(bound, B)

    # Find last position where gap ≤ target_gap
    last_small_gap = 0
    for i in range(1, len(smooth)):
        gap = smooth[i] - smooth[i-1]
        if gap <= target_gap:
            last_small_gap = smooth[i]

    return last_small_gap

# Main computation
B = 29  # smoothness bound
target_gap = 24  # we need gaps > 24 to ensure some x_k has large prime

print(f"Computing {B}-smooth numbers...")
R0 = find_R0(B, target_gap)
print(f"R₀ = {R0}")
print(f"Beyond r = {R0}, no 25-element interval [r+5, r+29] is entirely {B}-smooth")
```

## Expected Output

The code should output:
1. The value of R₀
2. Verification that beyond R₀, all gaps between 29-smooth numbers exceed 24
3. A few examples of the largest gaps found

## Theoretical Note

It's known that gaps between B-smooth numbers grow. By Størmer's theorem and related results, B-smooth numbers have density O((log X)^π(B) / X^{1-1/log B}), so they become very sparse.

For B = 29, the largest 29-smooth numbers under 10^7 have gaps that eventually exceed 24.

## Deliverable

1. The Python code
2. The computed value of R₀
3. A statement suitable for use in Lean:
   ```
   -- For r ≥ R₀, some k ∈ K10 has x_k = r + k with a prime factor > 29
   lemma smooth_gap_bound : R₀ = <computed value>
   ```
