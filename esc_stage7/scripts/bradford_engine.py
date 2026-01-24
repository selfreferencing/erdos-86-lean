#!/usr/bin/env python3
"""Bradford one-dimensional search engine for Erdős–Straus (prime case).

We implement the sufficient/necessary modular characterizations from:
  Kyle Bradford, "Elementary patterns from the Erdős–Straus conjecture",
  INTEGERS 25 (2025) A54.
PDF: https://math.colgate.edu/~integers/z54/z54.pdf

For a prime p, search x in [ceil(p/4), ceil(p/2)]. Define m = 4x - p (>0).

Type I (p ∤ y): find d | x^2 such that
  d ≡ -p x (mod m)
Then
  y = (p x + d)/m
  z = p( x + p*(x^2/d) )/m

Type II (p | y): find d | x^2 such that
  d ≤ x   and   d ≡ -x (mod m)
Then
  y = p(x + d)/m
  z = p( x + x^2/d )/m

For prime p and x < p, gcd(x, m) = gcd(x, 4x - p) = gcd(x, p) = 1,
so all divisors of x^2 are invertible mod m.

This module is designed for dataset generation and pattern analysis:
- deterministic search order: increasing k, then increasing d
- returns structured dicts suitable for JSONL
"""

from __future__ import annotations

import json
import math
from dataclasses import dataclass
from typing import Dict, Iterable, List, Optional, Sequence, Tuple


def ceil_div(a: int, b: int) -> int:
    return -(-a // b)


def verify_identity(n: int, x: int, y: int, z: int) -> bool:
    """Check 4/n = 1/x + 1/y + 1/z via cross-multiplication."""
    # All must be positive
    if n <= 0 or x <= 0 or y <= 0 or z <= 0:
        return False
    lhs = 4 * x * y * z
    rhs = n * (x * y + x * z + y * z)
    return lhs == rhs


def sieve_primes_upto(n: int) -> List[int]:
    """Simple sieve returning list of primes <= n."""
    if n < 2:
        return []
    sieve = bytearray(b"\x01") * (n + 1)
    sieve[0:2] = b"\x00\x00"
    for p in range(2, int(n ** 0.5) + 1):
        if sieve[p]:
            step = p
            start = p * p
            sieve[start : n + 1 : step] = b"\x00" * ((n - start) // step + 1)
    return [i for i in range(2, n + 1) if sieve[i]]


def factorize(n: int, primes: Sequence[int]) -> List[Tuple[int, int]]:
    """Prime factorization of n using trial division by given primes."""
    assert n > 0
    out: List[Tuple[int, int]] = []
    rem = n
    for p in primes:
        if p * p > rem:
            break
        if rem % p == 0:
            e = 0
            while rem % p == 0:
                rem //= p
                e += 1
            out.append((p, e))
    if rem > 1:
        out.append((rem, 1))
    return out


def factorize_using_base(d: int, base_factors: Sequence[Tuple[int, int]]) -> List[Tuple[int, int]]:
    """Factorize d knowing all primes dividing it are among base_factors primes."""
    rem = d
    out: List[Tuple[int, int]] = []
    for p, _e in base_factors:
        if rem % p == 0:
            e = 0
            while rem % p == 0:
                rem //= p
                e += 1
            out.append((p, e))
    if rem != 1:
        # This should never happen if d|x^2 and base_factors is factorization of x.
        out.append((rem, 1))
    return out


def divisors_from_factors(factors: Sequence[Tuple[int, int]]) -> List[int]:
    """Enumerate all positive divisors from prime-exponent factorization."""
    divs = [1]
    for p, e in factors:
        current = []
        p_pow = 1
        for _ in range(e + 1):
            for d in divs:
                current.append(d * p_pow)
            p_pow *= p
        divs = current
    return divs


def divisors_x2_le_x(x: int, x_factors: Sequence[Tuple[int, int]]) -> List[int]:
    """All divisors d of x^2 with d <= x, sorted increasing."""
    x2_factors = [(p, 2 * e) for p, e in x_factors]
    divs = divisors_from_factors(x2_factors)
    divs = [d for d in divs if d <= x]
    divs.sort()
    return divs


def is_square(n: int) -> bool:
    if n < 0:
        return False
    r = int(math.isqrt(n))
    return r * r == n


@dataclass
class BradfordResult:
    p: int
    residue_840: int
    x: int
    y: int
    z: int
    k: int
    m: int
    d: int
    sol_type: str  # "I" or "II"
    x_factors: List[Tuple[int, int]]
    d_factors: List[Tuple[int, int]]
    minimal_x: bool = True

    def to_json(self) -> str:
        obj = {
            "p": self.p,
            "residue_840": self.residue_840,
            "x": self.x,
            "y": self.y,
            "z": self.z,
            "k": self.k,
            "m": self.m,
            "d": self.d,
            "type": self.sol_type,
            "x_factors": self.x_factors,
            "d_factors": self.d_factors,
            "minimal_x": self.minimal_x,
        }
        return json.dumps(obj, separators=(",", ":"))


def _try_type_ii(p: int, x: int, m: int, x_factors: Sequence[Tuple[int, int]]) -> Optional[Tuple[int, int, int]]:
    """Return (d,y,z) if Type II condition is met for this x."""
    if m <= 0:
        return None
    target = (-x) % m
    # Enumerate divisors d|x^2 with d <= x
    for d in divisors_x2_le_x(x, x_factors):
        if d % m != target:
            continue
        # Reconstruct
        # y = p(x+d)/m
        num_y = p * (x + d)
        if num_y % m != 0:
            continue
        y = num_y // m
        t = (x * x) // d
        num_z = p * (x + t)
        if num_z % m != 0:
            continue
        z = num_z // m
        if verify_identity(p, x, y, z):
            return d, y, z
    return None


def _try_type_i(p: int, x: int, m: int, x_factors: Sequence[Tuple[int, int]]) -> Optional[Tuple[int, int, int]]:
    """Return (d,y,z) if Type I condition is met for this x."""
    if m <= 0:
        return None
    target = (-p * x) % m
    # Enumerate all divisors of x^2 (no d<=x constraint)
    x2_factors = [(q, 2 * e) for q, e in x_factors]
    divs = divisors_from_factors(x2_factors)
    divs.sort()
    for d in divs:
        if d % m != target:
            continue
        num_y = p * x + d
        if num_y % m != 0:
            continue
        y = num_y // m
        t = (x * x) // d
        num_z = p * (x + p * t)
        if num_z % m != 0:
            continue
        z = num_z // m
        if verify_identity(p, x, y, z):
            return d, y, z
    return None


def bradford_search(p: int, primes_for_fact: Sequence[int], k_max: int = 200) -> BradfordResult:
    """Search for the minimal-x Bradford certificate for a prime p.

    Returns a BradfordResult. Raises ValueError if not found up to k_max.
    """
    if p < 2:
        raise ValueError("p must be >=2")
    if p == 2:
        # trivial certificate
        x, y, z = 1, 2, 2
        return BradfordResult(
            p=p,
            residue_840=p % 840,
            x=x,
            y=y,
            z=z,
            k=0,
            m=4 * x - p,
            d=1,
            sol_type="II",
            x_factors=factorize(x, primes_for_fact),
            d_factors=[(1, 1)],
            minimal_x=True,
        )

    x0 = (p + 3) // 4  # ceil(p/4) for odd p
    x_end = (p + 1) // 2  # ceil(p/2) for odd p

    for k in range(0, k_max + 1):
        x = x0 + k
        if x > x_end:
            break
        m = 4 * x - p
        if m <= 0:
            continue
        x_factors = factorize(x, primes_for_fact)

        # Type II first (dominant)
        got = _try_type_ii(p, x, m, x_factors)
        if got is not None:
            d, y, z = got
            d_factors = factorize_using_base(d, x_factors)
            return BradfordResult(
                p=p,
                residue_840=p % 840,
                x=x,
                y=y,
                z=z,
                k=k,
                m=m,
                d=d,
                sol_type="II",
                x_factors=list(x_factors),
                d_factors=d_factors,
                minimal_x=True,
            )

        # Then Type I
        got = _try_type_i(p, x, m, x_factors)
        if got is not None:
            d, y, z = got
            d_factors = factorize_using_base(d, x_factors)
            return BradfordResult(
                p=p,
                residue_840=p % 840,
                x=x,
                y=y,
                z=z,
                k=k,
                m=m,
                d=d,
                sol_type="I",
                x_factors=list(x_factors),
                d_factors=d_factors,
                minimal_x=True,
            )

    raise ValueError(f"No Bradford solution found for p={p} with k<= {k_max}")


def bradford_fixed_k(p: int, k: int, primes_for_fact: Sequence[int]) -> Optional[BradfordResult]:
    """Try to solve prime p with a fixed k (i.e., fixed x = ceil(p/4)+k).

    Returns a BradfordResult if works, else None.

    Note: this uses the same deterministic d-search order (increasing d) as bradford_search.
    """
    x0 = (p + 3) // 4
    x = x0 + k
    if x > (p + 1) // 2:
        return None
    m = 4 * x - p
    if m <= 0:
        return None
    x_factors = factorize(x, primes_for_fact)

    got = _try_type_ii(p, x, m, x_factors)
    if got is not None:
        d, y, z = got
        return BradfordResult(
            p=p,
            residue_840=p % 840,
            x=x,
            y=y,
            z=z,
            k=k,
            m=m,
            d=d,
            sol_type="II",
            x_factors=list(x_factors),
            d_factors=factorize_using_base(d, x_factors),
            minimal_x=False,
        )

    got = _try_type_i(p, x, m, x_factors)
    if got is not None:
        d, y, z = got
        return BradfordResult(
            p=p,
            residue_840=p % 840,
            x=x,
            y=y,
            z=z,
            k=k,
            m=m,
            d=d,
            sol_type="I",
            x_factors=list(x_factors),
            d_factors=factorize_using_base(d, x_factors),
            minimal_x=False,
        )

    return None
