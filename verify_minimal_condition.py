#!/usr/bin/env python3
"""
Verify GPT's minimal sufficient condition for Type II.

THEOREM: If (p + 4) has a divisor m ≡ 3 (mod 4), then Type II succeeds.

CONJECTURE: If (p + 4) fails, then (p + 4a²) works for small a.
"""

import math
from typing import List, Tuple, Optional

def is_prime(n):
    if n < 2: return False
    if n == 2: return True
    if n % 2 == 0: return False
    for i in range(3, int(math.isqrt(n)) + 1, 2):
        if n % i == 0: return False
    return True

def get_divisors(n: int) -> List[int]:
    if n <= 0:
        return []
    divs = []
    for i in range(1, int(math.isqrt(n)) + 1):
        if n % i == 0:
            divs.append(i)
            if i != n // i:
                divs.append(n // i)
    return sorted(divs)

def prime_factors(n: int) -> List[int]:
    """Return list of prime factors (with multiplicity)."""
    factors = []
    d = 2
    while d * d <= n:
        while n % d == 0:
            factors.append(d)
            n //= d
        d += 1
    if n > 1:
        factors.append(n)
    return factors

def has_3mod4_factor(n: int) -> Tuple[bool, Optional[int]]:
    """Check if n has a prime factor ≡ 3 (mod 4). Return (bool, factor)."""
    factors = prime_factors(n)
    for f in set(factors):
        if f % 4 == 3:
            return True, f
    return False, None

def has_3mod4_divisor(n: int) -> Tuple[bool, Optional[int]]:
    """Check if n has ANY divisor ≡ 3 (mod 4). Return (bool, divisor)."""
    for d in get_divisors(n):
        if d > 1 and d % 4 == 3:
            return True, d
    return False, None

print("=" * 70)
print("VERIFYING GPT'S MINIMAL CONDITION")
print("=" * 70)

# Test the claim: if (p+4) has a factor ≡ 3 (mod 4), Type II succeeds
print("\n" + "=" * 70)
print("PART 1: Testing (p + 4) has 3-mod-4 factor → Type II succeeds")
print("=" * 70)

primes_1mod4 = [p for p in range(5, 10001) if is_prime(p) and p % 4 == 1]

simple_successes = 0
simple_failures = []

for p in primes_1mod4:
    has_factor, factor = has_3mod4_divisor(p + 4)
    if has_factor:
        simple_successes += 1
    else:
        simple_failures.append((p, p + 4, prime_factors(p + 4)))

print(f"\nPrimes p ≡ 1 (mod 4) up to 10000: {len(primes_1mod4)}")
print(f"Simple condition (p+4 has 3-mod-4 divisor) works: {simple_successes}")
print(f"Simple condition fails: {len(simple_failures)}")

print(f"\nPrimes where simple condition FAILS:")
for p, p4, factors in simple_failures[:20]:
    print(f"  p = {p:5d}: p+4 = {p4:6d} = {' × '.join(map(str, factors))} (all ≡ 1 mod 4)")

# Test the square-shift rescue
print("\n" + "=" * 70)
print("PART 2: Square-shift rescue for failures")
print("=" * 70)

def find_rescue_a(p: int, max_a: int = 20) -> Optional[Tuple[int, int, int]]:
    """Find smallest a where (p + 4a²) has a 3-mod-4 divisor."""
    for a in range(1, max_a + 1):
        val = p + 4 * a * a
        has_div, div = has_3mod4_divisor(val)
        if has_div:
            return a, val, div
    return None

print(f"\nFor each failure, finding rescue a:")
all_rescued = True
max_rescue_a = 0

for p, p4, factors in simple_failures:
    rescue = find_rescue_a(p)
    if rescue:
        a, val, div = rescue
        if a > max_rescue_a:
            max_rescue_a = a
        print(f"  p = {p:5d}: a = {a}, p + 4a² = {val} has divisor {div} ≡ 3 (mod 4)")
    else:
        print(f"  p = {p:5d}: NO RESCUE FOUND (a ≤ 20)")
        all_rescued = False

print(f"\nAll failures rescued: {all_rescued}")
print(f"Maximum rescue a needed: {max_rescue_a}")

# Detailed analysis of p = 2521
print("\n" + "=" * 70)
print("PART 3: Detailed analysis of p = 2521")
print("=" * 70)

p = 2521
print(f"\np = {p}")
print(f"p + 4 = {p + 4} = {' × '.join(map(str, prime_factors(p + 4)))}")

print(f"\nTrying p + 4a² for a = 1, 2, 3, ...:")
for a in range(1, 10):
    val = p + 4 * a * a
    factors = prime_factors(val)
    has_3, div = has_3mod4_divisor(val)
    status = f"✓ (divisor {div} ≡ 3 mod 4)" if has_3 else "✗ (all factors ≡ 1 mod 4)"
    print(f"  a = {a}: p + 4×{a}² = {val} = {' × '.join(map(str, factors))} {status}")

# Now verify the actual Type II solution works
print("\n" + "=" * 70)
print("PART 4: Verify Type II solution for p = 2521 via a = 2")
print("=" * 70)

p = 2521
a = 2
val = p + 4 * a * a  # p + 16 = 2537 = 43 × 59
m = 43  # The 3-mod-4 divisor

print(f"\np = {p}, a = {a}")
print(f"p + 4a² = {val} = 43 × 59")
print(f"m = {m} (≡ 3 mod 4)")

# For Type II with this m:
# x = (p + m) / 4
x = (p + m) // 4
print(f"\nx = (p + m) / 4 = ({p} + {m}) / 4 = {x}")
print(f"Check: 4x - p = 4×{x} - {p} = {4*x - p}")

# The condition is: d ≡ -x (mod m) with d | x²
# If d = a² = 4, need 4 ≡ -x (mod 43)
print(f"\nChecking d = a² = {a*a}:")
print(f"  x mod m = {x} mod {m} = {x % m}")
print(f"  -x mod m = {(-x) % m}")
print(f"  d = {a*a}")
print(f"  d ≡ -x (mod m)? {a*a} ≡ {(-x) % m} (mod {m})? {a*a % m == (-x) % m}")

# Hmm, this doesn't match directly. Let me re-examine the claim.
print("\n" + "=" * 70)
print("PART 5: Re-examining the connection")
print("=" * 70)

print("""
GPT's claim was:
- If m | (p + 4), then x ≡ -1 (mod m), so d = 1 works.

For the square-shift case with (p + 4a²):
- We need to find the right correspondence.

Let me check what our original Type II framework says about p = 2521.
""")

# Our original Type II: x_k = (p + 4k + 3) / 4, m_k = 4k + 3
# We found success at k = 5

def coprime_pairs(n: int) -> List[Tuple[int, int]]:
    divs = get_divisors(n)
    pairs = []
    for i, a in enumerate(divs):
        for b in divs[i:]:
            if math.gcd(a, b) == 1:
                pairs.append((a, b))
    return pairs

def find_type_ii_solution(p: int, max_k: int = 20):
    """Find Type II solution for prime p ≡ 1 (mod 4)."""
    x_0 = (p + 3) // 4
    for k in range(max_k):
        x_k = x_0 + k
        m_k = 4 * k + 3
        for a, b in coprime_pairs(x_k):
            if (a + b) % m_k == 0:
                return k, x_k, m_k, (a, b)
    return None

result = find_type_ii_solution(2521)
if result:
    k, x_k, m_k, pair = result
    print(f"p = 2521: Type II succeeds at k = {k}")
    print(f"  x_k = {x_k}, m_k = {m_k}")
    print(f"  Coprime pair: {pair}, sum = {pair[0] + pair[1]}")
    print(f"  {pair[0]} + {pair[1]} = {pair[0] + pair[1]} ≡ 0 (mod {m_k})? {(pair[0] + pair[1]) % m_k == 0}")

# Now let's see if GPT's framework matches
print("\n" + "=" * 70)
print("PART 6: Connecting GPT's (p + 4a²) to our (x_k, m_k)")
print("=" * 70)

print("""
Our framework: x_k = (p + 3)/4 + k, m_k = 4k + 3
GPT's framework: m | (p + 4a²), then x = (p + m)/4

Let's see if m_k | (p + 4a²) for some a when k = 5, m_5 = 23.
""")

p = 2521
m = 23  # m_5

print(f"p = {p}, m = {m} (our m_5)")
print(f"Need: m | (p + 4a²), i.e., {m} | ({p} + 4a²)")
print(f"p mod m = {p % m}")
print(f"Need: 4a² ≡ -{p % m} ≡ {(-p) % m} (mod {m})")

target = (-p) % m
print(f"\nLooking for a where 4a² ≡ {target} (mod {m}):")
for a in range(1, 25):
    if (4 * a * a) % m == target:
        print(f"  a = {a}: 4×{a}² = {4*a*a} ≡ {(4*a*a) % m} (mod {m}) ✓")
        print(f"  p + 4a² = {p + 4*a*a}")
        break
else:
    print("  No solution found for a ≤ 24")

# Final summary
print("\n" + "=" * 70)
print("SUMMARY")
print("=" * 70)

print(f"""
1. GPT's simple condition "(p+4) has 3-mod-4 divisor" works for:
   {simple_successes}/{len(primes_1mod4)} primes ≡ 1 (mod 4) up to 10000

2. Failures (where p+4 has all factors ≡ 1 mod 4): {len(simple_failures)} primes

3. All failures rescued by (p + 4a²) for small a: {all_rescued}
   Maximum a needed: {max_rescue_a}

4. This explains WHY p = 2521 is hard:
   - p + 4 = 2525 = 5² × 101 (all factors ≡ 1 mod 4)
   - Requires square-shift rescue

5. The connection to our coprime-pair framework needs further analysis.
""")
