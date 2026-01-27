#!/usr/bin/env python3
"""
Search for a finite modular covering set for the ED2 existence proof.

Dyachenko Lemma D.6: For (r, s, alpha) with M = 4*alpha*s*r - 1 dividing
(4*alpha*s^2 + P), we get an ED2 solution with:
  d' = r, b' = s, c' = m*r - s, A = alpha*s*(m*r - s)
  where m = (4*alpha*s^2 + P) / M.

The divisibility condition is: P ≡ -4*alpha*s^2 (mod M).

Theorem D.14: If a finite set of (r, s, alpha) triples covers ALL residue
classes P ≡ 1 (mod 24) modulo Q = lcm(all M_i), then every prime P ≡ 1 (mod 24)
has an ED2 solution (for large enough P; small P checked separately).

This script searches for such a covering.
"""

from math import gcd


def lcm2(a, b):
    return a * b // gcd(a, b)


def is_prime(n):
    if n < 2:
        return False
    if n < 4:
        return True
    if n % 2 == 0 or n % 3 == 0:
        return False
    i = 5
    while i * i <= n:
        if n % i == 0 or n % (i + 2) == 0:
            return False
        i += 6
    return True


def ed2_check(P, r, s, alpha):
    """Try Lemma D.6 construction. Returns (offset, b, c) or None."""
    M = 4 * alpha * s * r - 1
    val = 4 * alpha * s * s + P
    if val % M != 0:
        return None

    m = val // M
    c_prime = m * r - s
    if c_prime <= 0:
        return None

    A = alpha * s * c_prime
    L = (P + 3) // 4
    U = (3 * P - 3) // 4
    if A < L or A > U:
        return None

    offset = 4 * A - P
    g = alpha * r  # g = alpha * d'
    b = g * s
    c = g * c_prime

    # Verify
    if (P + offset) * (b + c) != 4 * offset * b * c:
        return None
    if offset % 4 != 3 or b <= 0 or c <= 0:
        return None

    return (offset, b, c, A)


def min_P_for_window(r, s, alpha):
    """Minimum P so that A lands in the window [L(P), U(P)]."""
    # A >= L: P >= 4*alpha*s*(3r - s) - 3
    bound1 = 4 * alpha * s * (3 * r - s) - 3
    # A <= U: P*(8*alpha*s*r - 3) >= 4*alpha*s^2 + 12*alpha*s*r - 3
    num = 4 * alpha * s * s + 12 * alpha * s * r - 3
    den = 8 * alpha * s * r - 3
    if den > 0:
        bound2 = -(-num // den)  # ceiling division
    else:
        bound2 = 0
    return max(bound1, bound2, 5)


# ── Phase 1: Enumerate all triples and their congruence classes ──────────

def enumerate_triples(max_r=20, max_s=20, max_alpha=5):
    """Generate (r, s, alpha, M, residue) tuples."""
    results = []
    seen = set()
    for alpha in range(1, max_alpha + 1):
        for s in range(1, max_s + 1):
            for r in range(1, max_r + 1):
                M = 4 * alpha * s * r - 1
                residue = (-4 * alpha * s * s) % M
                key = (M, residue)
                if key not in seen:
                    seen.add(key)
                    results.append((r, s, alpha, M, residue))
    results.sort(key=lambda t: t[3])
    return results


# ── Phase 2: Greedy covering search ─────────────────────────────────────

def greedy_cover(triples, max_Q=200000):
    """Find a small set of triples covering all P ≡ 1 (mod 24) mod Q."""
    Q = 24
    target = frozenset(x for x in range(Q) if x % 24 == 1)
    covered = set()
    selected = []

    print(f"Target: {len(target)} classes mod {Q}")

    for iteration in range(300):
        best = None
        best_gain = 0

        for t in triples:
            if t in selected:
                continue
            r, s, alpha, M, residue = t
            new_Q = lcm2(Q, M)
            if new_Q > max_Q:
                continue

            # Lift current state to new_Q
            new_target_size = new_Q // 24
            lift_covered = set()
            triple_new = set()
            for x in range(new_Q):
                if x % 24 != 1:
                    continue
                if x % Q in covered:
                    lift_covered.add(x)
                if x % M == residue:
                    triple_new.add(x)

            gain = len((lift_covered | triple_new)) - len(lift_covered)
            if gain > best_gain:
                best_gain = gain
                best = t
                best_new_Q = new_Q
                best_lift = lift_covered
                best_triple = triple_new

        if best is None or best_gain == 0:
            break

        selected.append(best)
        Q = best_new_Q
        target = frozenset(x for x in range(Q) if x % 24 == 1)
        covered = (best_lift | best_triple)

        r, s, alpha, M, residue = best
        pct = 100 * len(covered) / len(target)
        print(f"  #{iteration+1}: (r={r}, s={s}, α={alpha}) M={M}, "
              f"P≡{residue}(mod {M}), "
              f"covered {len(covered)}/{len(target)} ({pct:.1f}%) mod {Q}")

        if covered == set(target):
            print(f"\n*** COMPLETE COVERING with {len(selected)} triples, Q={Q} ***")
            return selected, Q, True

    uncov = len(target) - len(covered)
    print(f"\nIncomplete: {uncov} classes uncovered mod {Q}")
    return selected, Q, False


# ── Phase 3: Verify against actual primes ────────────────────────────────

def verify_primes(selected, max_P=100000):
    """Check every prime P ≡ 1 (mod 24) up to max_P."""
    print(f"\nVerifying primes P ≡ 1 (mod 24) up to {max_P}...")
    failures = []
    checked = 0

    for P in range(25, max_P + 1, 24):
        if not is_prime(P):
            continue
        checked += 1

        found = False
        for t in selected:
            r, s, alpha, M, residue = t
            result = ed2_check(P, r, s, alpha)
            if result is not None:
                found = True
                break

        if not found:
            # Try ALL triples, not just selected
            failures.append(P)

    print(f"Checked {checked} primes")
    if failures:
        print(f"FAILURES ({len(failures)}): {failures[:50]}")
    else:
        print(f"ALL {checked} PRIMES COVERED!")
    return failures


# ── Phase 4: For failures, find what works ───────────────────────────────

def diagnose_failures(failures, max_r=50, max_s=50, max_alpha=10):
    """For each failed prime, find SOME triple that works."""
    print(f"\nDiagnosing {len(failures)} failures...")
    still_failed = []

    for P in failures:
        found = False
        for alpha in range(1, max_alpha + 1):
            if found:
                break
            for s in range(1, max_s + 1):
                if found:
                    break
                for r in range(1, max_r + 1):
                    result = ed2_check(P, r, s, alpha)
                    if result is not None:
                        offset, b, c, A = result
                        M = 4 * alpha * s * r - 1
                        print(f"  P={P}: (r={r}, s={s}, α={alpha}) M={M}, "
                              f"offset={offset}, b={b}, c={c}, A={A}")
                        found = True
                        break
        if not found:
            still_failed.append(P)
            print(f"  P={P}: NO SOLUTION FOUND (searched r,s≤{max_s}, α≤{max_alpha})")

    return still_failed


# ── Phase 5: Summary for Lean formalization ──────────────────────────────

def print_lean_summary(selected, Q):
    """Print the covering in a format useful for Lean formalization."""
    print(f"\n{'='*60}")
    print(f"COVERING SET FOR LEAN FORMALIZATION")
    print(f"{'='*60}")
    print(f"Q = {Q}")
    print(f"Number of triples: {len(selected)}")
    print()

    for i, t in enumerate(selected):
        r, s, alpha, M, residue = t
        min_P = min_P_for_window(r, s, alpha)
        lam = alpha * s * r / (4 * alpha * s * r - 1)
        print(f"Triple {i+1}:")
        print(f"  (r={r}, s={s}, α={alpha})")
        print(f"  M = 4·{alpha}·{s}·{r} - 1 = {M}")
        print(f"  Covers: P ≡ {residue} (mod {M})")
        print(f"  λ = {alpha*s*r}/{M} = {lam:.6f}")
        print(f"  Window valid for P ≥ {min_P}")
        print()


# ── Main ─────────────────────────────────────────────────────────────────

if __name__ == "__main__":
    print("=" * 60)
    print("ED2 COVERING SET SEARCH")
    print("Goal: cover all P ≡ 1 (mod 24) for the ESC proof")
    print("=" * 60)

    # Step 1: Enumerate triples
    print("\nStep 1: Enumerating triples...")
    triples = enumerate_triples(max_r=20, max_s=20, max_alpha=5)
    print(f"  Found {len(triples)} unique (M, residue) pairs")

    # Show coverage per modulus
    by_mod = {}
    for t in triples:
        M = t[3]
        by_mod.setdefault(M, []).append(t[4])
    print("\n  Modulus -> residues covered:")
    for M in sorted(by_mod.keys())[:15]:
        res = sorted(by_mod[M])
        print(f"    M={M}: {len(res)}/{M} residues = {res[:10]}{'...' if len(res)>10 else ''}")

    # Step 2: Greedy covering
    print("\nStep 2: Searching for covering set...")
    selected, Q, complete = greedy_cover(triples, max_Q=500000)

    # Step 3: Verify
    print("\nStep 3: Verification...")
    failures = verify_primes(selected, max_P=100000)

    # Step 4: Diagnose failures
    if failures:
        still_bad = diagnose_failures(failures)
        if still_bad:
            print(f"\n*** STILL FAILED: {still_bad} ***")
        else:
            print(f"\nAll failures resolved with expanded parameters.")
            print("These triples should be added to the covering set.")

    # Step 5: Print summary
    if complete:
        print_lean_summary(selected, Q)
    else:
        print(f"\nCovering incomplete. {len(failures)} prime failures found.")
        print("May need larger search parameters or different approach.")
