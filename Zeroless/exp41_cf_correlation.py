"""
Experiment 41: CF Convergent Correlation Analysis

GPT 19B's recommended computation:
"Test whether isolated hits correlate with exceptionally good rational
approximations to θ = log₁₀(2) (continued fraction convergents)."

For each hit n (where 2^n has zeroless m-digit prefix in transition zone),
measure how close n is to a CF convergent denominator q_k.
"""

from decimal import Decimal, getcontext
from fractions import Fraction
import math

# High precision for theta
getcontext().prec = 100

def compute_cf_convergents(theta, num_terms=50):
    """Compute continued fraction convergents of theta."""
    # Get CF expansion
    cf = []
    x = theta
    for _ in range(num_terms):
        a = int(x)
        cf.append(a)
        frac = x - a
        if frac < 1e-15:
            break
        x = 1 / frac

    # Compute convergents p_k/q_k
    convergents = []
    p_prev, p_curr = 0, 1
    q_prev, q_curr = 1, 0

    for a in cf:
        p_new = a * p_curr + p_prev
        q_new = a * q_curr + q_prev
        convergents.append((p_new, q_new))
        p_prev, p_curr = p_curr, p_new
        q_prev, q_curr = q_curr, q_new

    return cf, convergents

def is_zeroless(s):
    """Check if string has no '0' digit."""
    return '0' not in s

def get_transition_zone(m):
    """Get the range of n where 2^n has exactly m digits."""
    # 2^n has m digits when 10^(m-1) <= 2^n < 10^m
    # i.e., (m-1)/log10(2) <= n < m/log10(2)
    theta = math.log10(2)
    n_min = math.ceil((m - 1) / theta)
    n_max = math.floor(m / theta - 1e-10)  # exclusive upper bound
    return range(n_min, n_max + 1)

def find_hits_in_transition_zone(m):
    """Find all n in transition zone where 2^n is entirely zeroless."""
    hits = []
    for n in get_transition_zone(m):
        power = str(2**n)
        if len(power) == m and is_zeroless(power):
            hits.append(n)
    return hits

def distance_to_nearest_convergent(n, convergent_denoms):
    """Find minimum distance from n to any convergent denominator."""
    min_dist = float('inf')
    closest_q = None
    for q in convergent_denoms:
        dist = abs(n - q)
        if dist < min_dist:
            min_dist = dist
            closest_q = q
    return min_dist, closest_q

def main():
    print("=" * 70)
    print("Experiment 41: CF Convergent Correlation Analysis")
    print("=" * 70)

    # Compute theta and its CF expansion
    theta = math.log10(2)
    print(f"\nθ = log₁₀(2) = {theta:.15f}")

    cf, convergents = compute_cf_convergents(theta, 30)
    print(f"\nContinued fraction: [{cf[0]}; {', '.join(map(str, cf[1:15]))}...]")

    # Extract denominators
    convergent_denoms = [q for p, q in convergents]
    print(f"\nConvergent denominators q_k:")
    for i, (p, q) in enumerate(convergents[:15]):
        approx_error = abs(q * theta - p)
        print(f"  q_{i} = {q:8d}  (|q·θ - p| = {approx_error:.2e})")

    print("\n" + "=" * 70)
    print("Analysis of Hits in Transition Zones")
    print("=" * 70)

    all_hits = []

    for m in range(2, 28):  # Up to m=27 (last observed hits at m=26)
        hits = find_hits_in_transition_zone(m)
        zone = get_transition_zone(m)

        if hits:
            for n in hits:
                dist, closest_q = distance_to_nearest_convergent(n, convergent_denoms)
                all_hits.append({
                    'm': m,
                    'n': n,
                    'dist_to_q': dist,
                    'closest_q': closest_q,
                    'power': str(2**n)
                })

    # Print hit analysis
    print(f"\n{'m':>3} | {'n':>5} | {'closest q_k':>10} | {'dist':>6} | {'2^n (truncated)':<30}")
    print("-" * 70)

    for hit in all_hits:
        power_str = hit['power'][:25] + "..." if len(hit['power']) > 25 else hit['power']
        print(f"{hit['m']:>3} | {hit['n']:>5} | {hit['closest_q']:>10} | {hit['dist_to_q']:>6} | {power_str}")

    print("\n" + "=" * 70)
    print("Statistical Summary")
    print("=" * 70)

    # Compute statistics
    distances = [h['dist_to_q'] for h in all_hits]
    hit_ns = [h['n'] for h in all_hits]

    print(f"\nTotal hits found: {len(all_hits)}")
    print(f"Hit exponents n: {hit_ns}")
    print(f"\nDistances to nearest CF convergent:")
    print(f"  Min: {min(distances)}")
    print(f"  Max: {max(distances)}")
    print(f"  Mean: {sum(distances)/len(distances):.1f}")

    # Check which hits ARE convergent denominators
    hits_at_convergents = [h for h in all_hits if h['dist_to_q'] == 0]
    print(f"\nHits that ARE convergent denominators: {len(hits_at_convergents)}")
    for h in hits_at_convergents:
        print(f"  n = {h['n']} (m = {h['m']})")

    # Check hits within 5 of a convergent
    close_hits = [h for h in all_hits if h['dist_to_q'] <= 5]
    print(f"\nHits within distance 5 of a convergent: {len(close_hits)}/{len(all_hits)}")

    # Compare to random baseline
    print("\n" + "=" * 70)
    print("Comparison to Random Baseline")
    print("=" * 70)

    # For random n in similar range, what's the expected distance to nearest q_k?
    import random
    random.seed(42)

    n_max = max(hit_ns)
    relevant_qs = [q for q in convergent_denoms if q <= n_max * 1.5]

    random_distances = []
    for _ in range(1000):
        rand_n = random.randint(1, n_max)
        dist, _ = distance_to_nearest_convergent(rand_n, relevant_qs)
        random_distances.append(dist)

    print(f"\nRandom baseline (1000 samples in [1, {n_max}]):")
    print(f"  Mean distance to nearest q_k: {sum(random_distances)/len(random_distances):.1f}")
    print(f"  Hits within 5 of convergent: {sum(1 for d in random_distances if d <= 5)}/1000")

    print(f"\nActual hits:")
    print(f"  Mean distance to nearest q_k: {sum(distances)/len(distances):.1f}")
    print(f"  Hits within 5 of convergent: {len(close_hits)}/{len(all_hits)}")

    # Check for correlation with |nθ - round(nθ)|
    print("\n" + "=" * 70)
    print("Diophantine Quality Analysis")
    print("=" * 70)

    print(f"\n{'n':>5} | {'|nθ - nearest int|':>20} | {'Is this unusually small?'}")
    print("-" * 60)

    for h in all_hits[-10:]:  # Last 10 hits (larger n)
        n = h['n']
        frac_part = (n * theta) % 1
        dist_to_int = min(frac_part, 1 - frac_part)
        # Compare to 1/(2q) where q is the relevant convergent scale
        relevant_q = max(q for q in convergent_denoms if q <= n)
        threshold = 1 / (2 * relevant_q) if relevant_q > 0 else 0.5
        unusually_small = "YES" if dist_to_int < threshold else "no"
        print(f"{n:>5} | {dist_to_int:>20.6f} | {unusually_small} (threshold ~ {threshold:.6f})")

    print("\n" + "=" * 70)
    print("CONCLUSION")
    print("=" * 70)

    hit_mean = sum(distances)/len(distances)
    random_mean = sum(random_distances)/len(random_distances)

    if hit_mean < random_mean * 0.5:
        print("\n*** CORRELATION DETECTED ***")
        print("Hits cluster significantly closer to CF convergents than random.")
        print("This supports the 'too-good approximation' connection.")
    elif hit_mean > random_mean * 1.5:
        print("\n*** ANTI-CORRELATION DETECTED ***")
        print("Hits are FARTHER from CF convergents than random.")
        print("CF approximation quality is NOT the lever.")
    else:
        print("\n*** NO SIGNIFICANT CORRELATION ***")
        print("Hits show similar distribution to random baseline.")
        print("CF convergent proximity does not appear to be the key factor.")

if __name__ == "__main__":
    main()
