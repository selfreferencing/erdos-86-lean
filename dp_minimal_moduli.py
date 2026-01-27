#!/usr/bin/env python3
"""
Find minimal divisor-pair moduli for each QR obstruction class.

For each "problem prime" p in {5, 7, 11, 13, 17} and each quadratic residue r mod p,
find the DP pair (u, v) minimizing 4*lcm(u,v) such that:
  - u + v ≡ 7 (mod 8)  [compatibility with P ≡ 1 mod 8]
  - p | lcm(u, v)       [congruence determines P mod p]
  - -(u+v) ≡ r (mod p)  [covers the target QR class]
  - Compatible with P ≡ 1 (mod 24)

Then compute Q = lcm(D6_Q, all DP moduli) and check if it's manageable.
"""

from math import gcd
from collections import defaultdict

def lcm2(a, b):
    return a * b // gcd(a, b)

def is_qr(a, p):
    """Check if a is a quadratic residue mod p using Euler's criterion."""
    if a % p == 0:
        return True  # 0 is sometimes included
    return pow(a, (p - 1) // 2, p) == 1

def get_qr_set(p):
    """Get set of non-zero quadratic residues mod p."""
    return {a for a in range(1, p) if is_qr(a, p)}

def get_qnr_set(p):
    """Get set of quadratic non-residues mod p."""
    return {a for a in range(1, p) if not is_qr(a, p)}

def find_minimal_dp(target_prime, target_residue, max_delta=5000):
    """
    Find DP pair (u, v) minimizing 4*lcm(u,v) that covers
    P ≡ target_residue (mod target_prime).
    
    Constraints:
      - delta = u + v ≡ 7 (mod 8)
      - target_prime | lcm(u, v)
      - -(u+v) ≡ target_residue (mod target_prime)
      - P ≡ 1 (mod 24) compatibility: check (-delta) mod gcd(4*lcm, 24) == 1 mod same
    """
    p = target_prime
    r = target_residue
    
    best = None
    best_modulus = float('inf')
    
    # delta ≡ 7 (mod 8) and delta ≡ -r (mod p)
    # CRT: find delta mod lcm(8, p) = 8p (since p is odd prime > 2)
    for d0 in range(7, 8 * p + 1, 8):  # d0 ≡ 7 (mod 8)
        if (-d0) % p != r % p:
            continue
        # d0 is the base; delta = d0, d0 + 8p, d0 + 16p, ...
        for delta in range(d0, max_delta + 1, 8 * p):
            # Try all (u, v) pairs with u + v = delta
            # u even, v odd (since delta is odd)
            for u in range(2, delta, 2):  # u even
                v = delta - u
                if v <= 0:
                    break
                
                L = lcm2(u, v)
                
                # Check target_prime | lcm
                if L % p != 0:
                    continue
                
                modulus = 4 * L
                
                # Quick filter: if modulus >= best, skip
                if modulus >= best_modulus:
                    continue
                
                # Full compatibility check with P ≡ 1 (mod 24)
                res = (-delta) % modulus
                g24 = gcd(modulus, 24)
                if res % g24 != 1 % g24:
                    continue
                
                # Additional check: residue mod 24 compatibility
                # The effective congruence is P ≡ res (mod modulus) AND P ≡ 1 (mod 24)
                # This has solutions iff res ≡ 1 (mod gcd(modulus, 24))
                # Already checked above
                
                # Verify target coverage
                if res % p != r % p:
                    continue
                    
                best = (u, v, delta, modulus, res)
                best_modulus = modulus
            
            # If we found something with small modulus, no need for larger delta
            if best_modulus <= 8 * p * 4:
                break
    
    return best

def find_all_dp_for_class(target_prime, target_residue, max_delta=2000, max_results=10):
    """Find multiple DP pairs for a given class, sorted by modulus."""
    p = target_prime
    r = target_residue
    
    results = []
    seen_moduli = set()
    
    for d0 in range(7, 8 * p + 1, 8):
        if (-d0) % p != r % p:
            continue
        for delta in range(d0, max_delta + 1, 8 * p):
            for u in range(2, delta, 2):
                v = delta - u
                if v <= 0:
                    break
                L = lcm2(u, v)
                if L % p != 0:
                    continue
                modulus = 4 * L
                if modulus in seen_moduli:
                    continue
                res = (-delta) % modulus
                g24 = gcd(modulus, 24)
                if res % g24 != 1 % g24:
                    continue
                if res % p != r % p:
                    continue
                results.append((modulus, u, v, delta, res))
                seen_moduli.add(modulus)
                if len(results) >= max_results * 5:
                    break
            if len(results) >= max_results * 5:
                break
    
    results.sort()
    return results[:max_results]


def main():
    print("=" * 80)
    print("MINIMAL DP MODULI FOR QR OBSTRUCTION CLASSES")
    print("=" * 80)
    
    problem_primes = [5, 7, 11, 13, 17]
    
    all_dp_moduli = []
    
    for p in problem_primes:
        qr_set = get_qr_set(p)
        qnr_set = get_qnr_set(p)
        print(f"\nPrime {p}:")
        print(f"  QRs: {sorted(qr_set)}")
        print(f"  QNRs: {sorted(qnr_set)}")
        
        for r in sorted(qr_set):
            best = find_minimal_dp(p, r, max_delta=5000)
            if best:
                u, v, delta, modulus, res = best
                all_dp_moduli.append(modulus)
                print(f"  r={r} (QR): best DP = (u={u}, v={v}, delta={delta}), "
                      f"modulus={modulus}, res={res}")
                
                # Also show a few alternatives
                alts = find_all_dp_for_class(p, r, max_delta=2000, max_results=5)
                for mod, uu, vv, dd, rr in alts[:3]:
                    if mod != modulus:
                        print(f"          alt: (u={uu}, v={vv}, delta={dd}), modulus={mod}")
            else:
                print(f"  r={r} (QR): NO DP FOUND!")
    
    # Compute combined Q
    print(f"\n{'=' * 80}")
    print("COMBINED MODULUS COMPUTATION")
    print("=" * 80)
    
    Q1 = 30_630_600  # D6 modulus
    print(f"D6 modulus Q1 = {Q1:,}")
    print(f"DP moduli: {sorted(set(all_dp_moduli))}")
    
    Q = Q1
    for mod in all_dp_moduli:
        Q = lcm2(Q, mod)
        
    print(f"\nCombined Q = lcm(Q1, all DP moduli) = {Q:,}")
    print(f"Q / Q1 = {Q // Q1:,}")
    
    # Factor Q
    n = Q
    factors = {}
    d = 2
    while d * d <= n:
        while n % d == 0:
            factors[d] = factors.get(d, 0) + 1
            n //= d
        d += 1
    if n > 1:
        factors[n] = factors.get(n, 0) + 1
    
    print(f"Q = " + " * ".join(f"{p}^{e}" if e > 1 else str(p)
                                 for p, e in sorted(factors.items())))
    
    # Check feasibility
    if Q < 10**9:
        print(f"\n*** Q < 10^9: FEASIBLE for native_decide! ***")
    elif Q < 10**12:
        print(f"\n*** Q < 10^12: CHALLENGING but possible with optimization ***")
    else:
        print(f"\n*** Q = {Q:.2e}: TOO LARGE for direct native_decide ***")
        print(f"    Need CRT decomposition or other approach")
    
    # Try to find DP moduli that are SMOOTH (only small prime factors)
    # to minimize Q
    print(f"\n{'=' * 80}")
    print("OPTIMIZED SEARCH: DP moduli with minimal new prime factors")
    print("=" * 80)
    
    Q1_primes = set(factors.keys()) if Q == Q1 else None
    # Recompute Q1 factors
    n1 = Q1
    q1_factors = set()
    d = 2
    while d * d <= n1:
        while n1 % d == 0:
            q1_factors.add(d)
            n1 //= d
        d += 1
    if n1 > 1:
        q1_factors.add(n1)
    print(f"Q1 prime factors: {sorted(q1_factors)}")
    
    for p in problem_primes:
        qr_set = get_qr_set(p)
        print(f"\nPrime {p} QR classes:")
        for r in sorted(qr_set):
            alts = find_all_dp_for_class(p, r, max_delta=5000, max_results=20)
            # Find the one whose modulus introduces fewest new prime factors
            best_new = None
            best_new_count = float('inf')
            best_smooth = None
            best_smooth_mod = float('inf')
            
            for mod, uu, vv, dd, rr in alts:
                # Factor modulus
                nn = mod
                mod_factors = set()
                dd2 = 2
                while dd2 * dd2 <= nn:
                    while nn % dd2 == 0:
                        mod_factors.add(dd2)
                        nn //= dd2
                    dd2 += 1
                if nn > 1:
                    mod_factors.add(nn)
                
                new_primes = mod_factors - q1_factors
                if len(new_primes) < best_new_count:
                    best_new_count = len(new_primes)
                    best_new = (mod, uu, vv, dd, rr, new_primes)
                
                if not new_primes and mod < best_smooth_mod:
                    best_smooth_mod = mod
                    best_smooth = (mod, uu, vv, dd, rr)
            
            if best_smooth:
                mod, uu, vv, dd, rr = best_smooth
                print(f"  r={r}: SMOOTH modulus={mod} (u={uu}, v={vv}, delta={dd}) "
                      f"[no new primes!]")
            elif best_new:
                mod, uu, vv, dd, rr, new_p = best_new
                print(f"  r={r}: best modulus={mod} (u={uu}, v={vv}, delta={dd}) "
                      f"[new primes: {sorted(new_p)}]")
    
    # Compute Q with smooth DP moduli only
    print(f"\n{'=' * 80}")
    print("Q WITH SMOOTH DP MODULI ONLY")
    print("=" * 80)
    
    Q_smooth = Q1
    smooth_count = 0
    non_smooth_classes = []
    
    for p in problem_primes:
        qr_set = get_qr_set(p)
        for r in sorted(qr_set):
            alts = find_all_dp_for_class(p, r, max_delta=5000, max_results=20)
            found_smooth = False
            for mod, uu, vv, dd, rr in alts:
                nn = mod
                mod_factors = set()
                dd2 = 2
                while dd2 * dd2 <= nn:
                    while nn % dd2 == 0:
                        mod_factors.add(dd2)
                        nn //= dd2
                    dd2 += 1
                if nn > 1:
                    mod_factors.add(nn)
                
                if mod_factors <= q1_factors:
                    Q_smooth = lcm2(Q_smooth, mod)
                    smooth_count += 1
                    found_smooth = True
                    break
            
            if not found_smooth:
                non_smooth_classes.append((p, r))
    
    print(f"Smooth DP found for {smooth_count} classes")
    print(f"Non-smooth classes: {non_smooth_classes}")
    print(f"Q_smooth = {Q_smooth:,}")
    
    if Q_smooth < 10**9:
        print(f"*** Q_smooth < 10^9: FEASIBLE! ***")
    else:
        print(f"*** Q_smooth = {Q_smooth:.2e}: need further optimization ***")


if __name__ == "__main__":
    main()
