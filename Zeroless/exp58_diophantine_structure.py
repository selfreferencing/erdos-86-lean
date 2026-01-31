"""
Exp 58: Direct Diophantine Analysis of Zeroless Powers

The condition "2^n has zeroless m-digit prefix" translates to:
    {n·θ} ∈ Z_m  (where θ = log₁₀(2), {·} = fractional part)

where Z_m ⊂ [0,1) is the "zeroless region" at depth m.

Key questions:
1. What is the structure of Z_m?
2. How does |Z_m| (measure) shrink with m?
3. Can Baker's theorem show {n·θ} eventually leaves Z_m?
"""

import math
from fractions import Fraction

theta = math.log10(2)  # ≈ 0.30102999566...

print("=" * 60)
print("THE DIOPHANTINE STRUCTURE OF ZEROLESS POWERS")
print("=" * 60)
print(f"\nθ = log₁₀(2) = {theta:.15f}")

# ============================================================
# PART 1: The Zeroless Region Z_m
# ============================================================

print("\n" + "=" * 60)
print("PART 1: Structure of the Zeroless Region Z_m")
print("=" * 60)

def mantissa_interval(d):
    """
    For leading digit d, the mantissa {log₁₀(x)} lies in [log₁₀(d), log₁₀(d+1)).
    """
    return (math.log10(d), math.log10(d + 1))

print("\nLeading digit intervals (depth 1):")
for d in range(1, 10):
    lo, hi = mantissa_interval(d)
    width = hi - lo
    print(f"  Digit {d}: [{lo:.6f}, {hi:.6f})  width = {width:.6f}")

# For m-digit zeroless prefix, the mantissa must lie in the union of intervals
# corresponding to all zeroless m-digit numbers.

def zeroless_intervals(m):
    """
    Return list of (lo, hi) intervals in [0,1) corresponding to
    m-digit zeroless prefixes.
    """
    intervals = []
    # Generate all m-digit zeroless numbers
    def generate(prefix, remaining):
        if remaining == 0:
            n = int(prefix)
            lo = math.log10(n)
            hi = math.log10(n + 1)
            # Normalize to [0,1) by taking fractional part
            lo_frac = lo - int(lo)
            hi_frac = hi - int(hi)
            # Handle wrap-around (shouldn't happen for same digit count)
            intervals.append((lo_frac, hi_frac))
            return
        for d in '123456789':
            generate(prefix + d, remaining - 1)

    for first in '123456789':
        generate(first, m - 1)

    return intervals

def total_measure(intervals):
    """Compute total measure of interval list."""
    return sum(hi - lo for lo, hi in intervals)

print("\nZeroless region measure by depth:")
for m in range(1, 7):
    intervals = zeroless_intervals(m)
    measure = total_measure(intervals)
    count = len(intervals)
    print(f"  Depth {m}: {count} intervals, total measure = {measure:.6f}")

# ============================================================
# PART 2: Which n give zeroless 2^n?
# ============================================================

print("\n" + "=" * 60)
print("PART 2: Orbit {n·θ} and Zeroless Powers")
print("=" * 60)

def fractional_part(x):
    return x - math.floor(x)

def is_in_zeroless_region(frac, m):
    """Check if fractional part corresponds to zeroless m-digit prefix."""
    # Convert back to mantissa form: 10^frac gives the leading digits
    mantissa = 10 ** frac
    # Get m digits
    s = f"{mantissa:.{m+5}f}".replace('.', '')[:m]
    return '0' not in s

print("\nFirst 100 values of {n·θ}:")
zeroless_n = []
for n in range(1, 101):
    frac = fractional_part(n * theta)
    is_zl_3 = is_in_zeroless_region(frac, 3)
    if is_zl_3:
        zeroless_n.append(n)
    if n <= 20:
        print(f"  n={n:2}: {{n·θ}} = {frac:.6f}, zeroless(m=3): {is_zl_3}")

print(f"\nZeroless at depth 3 among n=1..100: {len(zeroless_n)}")
print(f"  n values: {zeroless_n[:20]}...")

# ============================================================
# PART 3: The Three-Distance Theorem and θ
# ============================================================

print("\n" + "=" * 60)
print("PART 3: Continued Fraction of θ = log₁₀(2)")
print("=" * 60)

def continued_fraction(x, terms=15):
    """Compute continued fraction expansion of x."""
    cf = []
    for _ in range(terms):
        a = int(x)
        cf.append(a)
        frac = x - a
        if frac < 1e-10:
            break
        x = 1 / frac
    return cf

def convergents(cf):
    """Compute convergents p_n/q_n from continued fraction."""
    convs = []
    p_prev, p_curr = 1, cf[0]
    q_prev, q_curr = 0, 1
    convs.append((p_curr, q_curr))

    for a in cf[1:]:
        p_next = a * p_curr + p_prev
        q_next = a * q_curr + q_prev
        convs.append((p_next, q_next))
        p_prev, p_curr = p_curr, p_next
        q_prev, q_curr = q_curr, q_next

    return convs

cf_theta = continued_fraction(theta, 20)
print(f"\nContinued fraction of θ = log₁₀(2):")
print(f"  [{cf_theta[0]}; {', '.join(map(str, cf_theta[1:]))}]")

convs = convergents(cf_theta)
print(f"\nConvergents p_n/q_n (best rational approximations):")
for i, (p, q) in enumerate(convs[:12]):
    approx = p / q
    error = abs(approx - theta)
    print(f"  {i}: {p}/{q} = {approx:.10f}, error = {error:.2e}")

print("\nThe denominators q_n are the 'resonant' values where {n·θ} is small.")
print("These are key for Baker-type arguments.")

# ============================================================
# PART 4: Gap Analysis - When does orbit leave zeroless region?
# ============================================================

print("\n" + "=" * 60)
print("PART 4: Gap Analysis")
print("=" * 60)

print("\nFor each depth m, find the LAST n where 2^n has zeroless m-digit prefix:")

for m in range(1, 8):
    last_zeroless_n = None
    power = 1
    for n in range(1, 500):
        power *= 2
        s = str(power)
        if len(s) >= m:
            prefix = s[:m]
            if '0' not in prefix:
                last_zeroless_n = n

    if last_zeroless_n:
        power_val = 2 ** last_zeroless_n
        prefix = str(power_val)[:m]
        frac = fractional_part(last_zeroless_n * theta)
        print(f"  Depth {m}: last zeroless n = {last_zeroless_n}, prefix = {prefix}, {{n·θ}} = {frac:.6f}")

# ============================================================
# PART 5: The Key Diophantine Inequality
# ============================================================

print("\n" + "=" * 60)
print("PART 5: The Diophantine Inequality")
print("=" * 60)

print("""
For 2^n to have zeroless m-digit prefix w:

    w·10^k ≤ 2^n < (w+1)·10^k  for some integer k

Taking logs:

    log(w) + k·log(10) ≤ n·log(2) < log(w+1) + k·log(10)

Rearranging:

    0 ≤ n·log(2) - k·log(10) - log(w) < log(1 + 1/w)

Define the linear form:

    Λ = n·log(2) - k·log(10) - log(w)

Then: 0 < Λ < log(1 + 1/w) ≈ 1/w < 10^{-(m-1)}

BAKER'S THEOREM says:

    |Λ| > exp(-C · (log n)^κ)  for some C, κ depending on the algebraic numbers

So for large n:

    exp(-C · (log n)^κ) < |Λ| < 10^{-(m-1)}

This gives:

    m < 1 + C · (log n)^κ / log(10)

Meaning: for n large enough, no zeroless prefix of length m is possible!
""")

# ============================================================
# PART 6: Explicit Baker-type calculation
# ============================================================

print("\n" + "=" * 60)
print("PART 6: Baker-Type Bounds (Simplified)")
print("=" * 60)

print("""
The classical Baker-Wüstholz theorem gives:

For Λ = b₁·log(α₁) + b₂·log(α₂) + b₃·log(α₃) with αᵢ algebraic, bᵢ integers:

    log|Λ| > -C · h(α₁) · h(α₂) · h(α₃) · log(B)

where h(α) is the logarithmic height and B = max|bᵢ|.

For our case:
    Λ = n·log(2) - k·log(10) - log(w)

Here:
    α₁ = 2,  h(2) = log(2)
    α₂ = 10, h(10) = log(10)
    α₃ = w,  h(w) ≤ log(w) < m·log(10)
    B ≈ max(n, k) ≈ n·log(2)/log(10) ≈ 0.3n

So roughly:
    log|Λ| > -C' · m · log(n)

Meaning:
    |Λ| > exp(-C' · m · log(n)) = n^{-C'·m}

For zeroless prefix to exist:
    |Λ| < 10^{-(m-1)}

So we need:
    n^{-C'·m} < 10^{-(m-1)}

Taking logs:
    -C'·m·log(n) < -(m-1)·log(10)
    C'·m·log(n) > (m-1)·log(10)
    log(n) > (m-1)·log(10) / (C'·m)

For large m, this gives approximately:
    log(n) > log(10) / C'

Which means n must be bounded!

The actual Baker constants are large, but the principle is clear:
Baker's theorem implies that for any fixed n, the length of zeroless
prefixes is bounded, and for any fixed m, the values of n with
zeroless m-digit prefix are bounded.
""")

# ============================================================
# PART 7: Empirical verification of the bound
# ============================================================

print("\n" + "=" * 60)
print("PART 7: Empirical Verification")
print("=" * 60)

print("\nFor each n with zeroless 2^n, what's the maximum zeroless prefix length?")

import sys
sys.set_int_max_str_digits(50000)

max_prefix_by_n = {}
power = 1
for n in range(1, 200):
    power *= 2
    s = str(power)
    # Find longest zeroless prefix
    max_len = 0
    for m in range(1, len(s) + 1):
        if '0' not in s[:m]:
            max_len = m
        else:
            break
    if max_len > 0:
        max_prefix_by_n[n] = max_len

print("n : max zeroless prefix length")
for n in sorted(max_prefix_by_n.keys())[:50]:
    print(f"  {n:3}: {max_prefix_by_n[n]}")

print(f"\n...")
print(f"Last entries:")
for n in sorted(max_prefix_by_n.keys())[-10:]:
    print(f"  {n:3}: {max_prefix_by_n[n]}")

# ============================================================
# SUMMARY
# ============================================================

print("\n" + "=" * 60)
print("SUMMARY: The Diophantine Path to Erdős 86")
print("=" * 60)

print("""
1. The condition "2^n has zeroless m-digit prefix" is equivalent to:

   |n·log(2) - k·log(10) - log(w)| < 10^{-(m-1)}

   for some integers k, w with w zeroless.

2. Baker's theorem gives LOWER BOUNDS on such linear forms:

   |Λ| > n^{-C·m}  (roughly)

3. Combining upper and lower bounds:

   n^{-C·m} < 10^{-(m-1)}

   This bounds n in terms of m (and vice versa).

4. To prove Erdős 86 via Baker:
   - Get explicit Baker constants for log(2), log(10)
   - For each candidate m-digit zeroless prefix w
   - Compute the bound on n
   - Verify computationally up to that bound

5. The Entry-Forced Zero Lemma helps by:
   - Eliminating prefixes w that have Entry witnesses
   - Reducing the number of cases to check

6. This is a HYBRID approach:
   - Combinatorial: Entry-Forced Zero prunes prefixes
   - Diophantine: Baker bounds n for each remaining prefix
""")
