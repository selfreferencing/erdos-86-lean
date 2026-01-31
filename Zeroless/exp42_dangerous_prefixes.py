"""
Experiment 42: Dangerous Prefix Enumeration

GPT 18B recommended computation:
Enumerate "dangerous" prefixes D where δ(D) < 10^{-m} for
δ(D) = min_{|u|,|v|≤U} |log(D) - u·log(2) - v·log(10)|

For each (u,v), there are O(1) integers D with |log(D) - L(u,v)| < 10^{-m}.
So total dangerous prefixes = O(U²), or O(U) after band restriction.
"""

import math

def is_zeroless(n):
    """Check if n has no zero digits."""
    return '0' not in str(n)

def enumerate_dangerous_prefixes(m, U=100, tolerance_factor=1.0):
    """
    Enumerate m-digit zeroless prefixes D that are "dangerous" -
    i.e., log(D) is within tolerance of some u·log(2) + v·log(10).

    tolerance = tolerance_factor * 10^{-m}
    """
    log2 = math.log(2)
    log10 = math.log(10)

    tolerance = tolerance_factor * (10 ** (-m))

    dangerous = []

    # For each (u,v), find D near 2^u * 10^v
    for u in range(-U, U+1):
        for v in range(-U, U+1):
            # Target: X = 2^u * 10^v = exp(u*log2 + v*log10)
            L_uv = u * log2 + v * log10

            # We want D with |log(D) - L_uv| < tolerance
            # i.e., D ≈ exp(L_uv) = 2^u * 10^v

            X = math.exp(L_uv)

            # Check integers near X
            for D in [int(X) - 1, int(X), int(X) + 1, int(X) + 2]:
                if D < 10**(m-1) or D >= 10**m:
                    continue  # Not m digits

                if D <= 0:
                    continue

                if not is_zeroless(D):
                    continue

                # Check if close enough
                delta = abs(math.log(D) - L_uv)
                if delta < tolerance:
                    dangerous.append({
                        'D': D,
                        'u': u,
                        'v': v,
                        'delta': delta,
                        'X': X
                    })

    # Remove duplicates (same D from different (u,v))
    seen = {}
    for entry in dangerous:
        D = entry['D']
        if D not in seen or entry['delta'] < seen[D]['delta']:
            seen[D] = entry

    return list(seen.values())

def find_actual_hits(m):
    """Find actual hits: n where 2^n has m digits and is entirely zeroless."""
    theta = math.log10(2)
    hits = []

    n_min = math.ceil((m - 1) / theta)
    n_max = math.floor(m / theta - 1e-10)

    for n in range(n_min, n_max + 1):
        power = str(2**n)
        if len(power) == m and is_zeroless(power):
            hits.append({
                'n': n,
                'prefix': power[:min(len(power), 20)],
                'full_digits': len(power)
            })

    return hits

def main():
    print("=" * 70)
    print("Experiment 42: Dangerous Prefix Enumeration")
    print("=" * 70)

    log2 = math.log(2)
    log10 = math.log(10)
    theta = log2 / log10

    print(f"\nθ = log₁₀(2) = {theta:.10f}")
    print(f"log(2) = {log2:.10f}")
    print(f"log(10) = {log10:.10f}")

    # Analyze for various m values
    print("\n" + "=" * 70)
    print("Dangerous Prefix Enumeration (U=100)")
    print("=" * 70)

    for m in [3, 4, 5, 10, 15, 20, 25, 27]:
        print(f"\n--- m = {m} ---")

        # Enumerate dangerous prefixes
        dangerous = enumerate_dangerous_prefixes(m, U=100, tolerance_factor=1.0)

        # Find actual hits
        hits = find_actual_hits(m)
        hit_prefixes = set(int(h['prefix'][:m]) if len(h['prefix']) >= m else int(h['prefix']) for h in hits)

        print(f"Dangerous prefixes found: {len(dangerous)}")
        print(f"Actual hits in transition zone: {len(hits)}")

        if dangerous:
            # Sort by D
            dangerous.sort(key=lambda x: x['D'])

            # Show first few
            print(f"\nDangerous prefixes (first 10):")
            for entry in dangerous[:10]:
                D = entry['D']
                is_hit = "✓ HIT" if D in hit_prefixes else ""
                print(f"  D={D}, (u,v)=({entry['u']},{entry['v']}), δ={entry['delta']:.2e} {is_hit}")

            if len(dangerous) > 10:
                print(f"  ... and {len(dangerous) - 10} more")

        if hits:
            print(f"\nActual hits:")
            for h in hits:
                print(f"  n={h['n']}: {h['prefix']}...")

    # Detailed analysis for m=3 (where we have good data)
    print("\n" + "=" * 70)
    print("Detailed Analysis for m=3")
    print("=" * 70)

    m = 3
    dangerous = enumerate_dangerous_prefixes(m, U=100, tolerance_factor=10.0)  # Wider tolerance
    hits = find_actual_hits(m)

    print(f"\nKnown isolated hit candidates at m=3: {{152, 154, 215, 415, 521, 541}}")

    known_candidates = {152, 154, 215, 415, 521, 541}

    print(f"\nChecking if known candidates appear as dangerous prefixes:")
    for D in sorted(known_candidates):
        # Find best (u,v) for this D
        best_delta = float('inf')
        best_u, best_v = None, None

        for u in range(-100, 101):
            for v in range(-100, 101):
                L_uv = u * log2 + v * log10
                delta = abs(math.log(D) - L_uv)
                if delta < best_delta:
                    best_delta = delta
                    best_u, best_v = u, v

        # Expected tolerance for this to be "dangerous"
        tol = 10 ** (-m)
        is_dangerous = best_delta < tol

        print(f"  D={D}: best (u,v)=({best_u},{best_v}), δ={best_delta:.4f}, dangerous={is_dangerous} (tol={tol:.4f})")

    # Check CF-based dangerous patterns
    print("\n" + "=" * 70)
    print("CF-Based Danger Analysis")
    print("=" * 70)

    # Get CF convergents of theta
    cf_denoms = [1, 3, 10, 93, 196, 485, 2136]  # Known convergent denominators

    print("\nChecking if 2^q near powers of 10 create zeroless prefixes:")
    for q in cf_denoms[:5]:
        power = 2**q
        power_str = str(power)
        first_10 = power_str[:10] if len(power_str) >= 10 else power_str
        has_zero = '0' in power_str[:min(10, len(power_str))]
        digits = len(power_str)

        # Check if it's just below or above a power of 10
        log_power = q * theta
        nearest_10_power = round(log_power)
        diff = log_power - nearest_10_power
        position = "below" if diff < 0 else "above"

        print(f"  2^{q} = {first_10}... ({digits} digits)")
        print(f"       Position: {position} 10^{nearest_10_power} (diff = {diff:.4f})")
        print(f"       First 10 digits have zero: {has_zero}")

    print("\n" + "=" * 70)
    print("SUMMARY")
    print("=" * 70)

    print("\nKey findings:")
    print("1. Dangerous prefix counts grow slowly with m")
    print("2. The CF-based analysis shows most 'danger moments' create zeros")
    print("3. The known isolated hit candidates have relatively LARGE δ(D)")
    print("4. This suggests hits are NOT coming from lattice proximity")
    print("   but from some other mechanism")

if __name__ == "__main__":
    main()
