#!/usr/bin/env python3
"""Generate Lean 4 witness code for the sorry region.

For each prime p in the sorry region (p%24=1, p%7 in {1,2,4}, p%5 in {1,4},
p%11 not in {7,8,10}, p%19 not in {14,15,18},
p%23 not in {7,10,11,15,17,19,20,21,22}),
find (offset, b, c) satisfying:
  offset % 4 = 3
  b > 0, c > 0
  (p + offset)(b + c) = 4 * offset * b * c

Output: Lean 4 code using interval_cases or explicit by_cases chain.
"""

from math import gcd


def is_prime(n):
    if n < 2: return False
    if n < 4: return True
    if n % 2 == 0 or n % 3 == 0: return False
    i = 5
    while i * i <= n:
        if n % i == 0 or n % (i + 2) == 0: return False
        i += 6
    return True


def in_sorry_region(p):
    """Check if p is in the sorry region."""
    if p % 24 != 1: return False
    if p % 7 not in (1, 2, 4): return False
    if p % 5 not in (1, 4): return False
    if p % 11 in (7, 8, 10): return False
    if p % 19 in (14, 15, 18): return False
    if p % 23 in (7, 10, 11, 15, 17, 19, 20, 21, 22): return False
    return True


def divisors(n):
    if n <= 0: return []
    result = []
    i = 1
    while i * i <= n:
        if n % i == 0:
            result.append(i)
            if i != n // i:
                result.append(n // i)
        i += 1
    return sorted(result)


def get_d6_residues(M):
    k = (M + 1) // 4
    if 4 * k - 1 != M: return {}
    result = {}  # residue -> (alpha, r, s)
    for a in divisors(k):
        rem = k // a
        for s in divisors(rem):
            r = rem // s
            res = (-4 * a * s * s) % M
            if res not in result:
                result[res] = (a, r, s)
    return result


def find_witness_d6(p, max_M=10000):
    """Try D6 construction for various M values."""
    for M in range(3, max_M + 1):
        if M % 4 != 3: continue
        residues = get_d6_residues(M)
        if not residues: continue
        target = p % M
        if target in residues:
            alpha, r, s = residues[target]
            # Compute offset, b, c
            num_a = 4 * alpha * s * s
            if (p + num_a) % M != 0: continue
            offset = (p + num_a) // M
            b_val = alpha * r * s
            # c formula: alpha * r * (r * offset - s)
            # Actually, let me derive c from the Type II equation
            # (p + offset)(b + c) = 4 * offset * b * c
            # c(4*offset*b - p - offset) = (p + offset) * b
            denom = 4 * offset * b_val - p - offset
            if denom <= 0: continue
            num = (p + offset) * b_val
            if num % denom != 0: continue
            c_val = num // denom
            if c_val <= 0: continue
            # Verify
            if (p + offset) * (b_val + c_val) == 4 * offset * b_val * c_val:
                if offset % 4 == 3:
                    return (offset, b_val, c_val, 'd6', M, alpha, r, s)
    return None


def find_witness_dp(p, max_delta=100000, max_b=2000):
    """Try divisor-pair construction."""
    for delta in range(3, max_delta + 1, 4):  # delta ≡ 3 mod 4
        if (p + delta) % 4 != 0: continue
        A = (p + delta) // 4
        # Try small b values
        for b in range(1, min(delta + 1, max_b)):
            # c from: (p + delta)(b + c) = 4*delta*b*c
            # c(4*delta*b - p - delta) = (p+delta)*b
            denom = 4 * delta * b - p - delta
            if denom <= 0: continue
            num = (p + delta) * b
            if num % denom != 0: continue
            c = num // denom
            if c > 0:
                return (delta, b, c, 'dp', 0, 0, 0, 0)
    return None


def find_witness(p):
    """Find a Type II witness for prime p."""
    # First try D6 (faster for most primes)
    w = find_witness_d6(p)
    if w: return w
    # Then try DP
    w = find_witness_dp(p)
    if w: return w
    return None


def gen_lean_witness_block(p, offset, b, c, indent=34):
    """Generate Lean proof block for a single witness (p, offset, b, c)."""
    I = " " * indent
    lines = []
    lines.append(f"{I}-- p = {p}")
    lines.append(f"{I}exact ⟨{offset}, {b}, {c}, by omega, by norm_num, by norm_num, by push_cast; ring⟩")
    return lines


def main():
    import sys

    B = int(sys.argv[1]) if len(sys.argv) > 1 else 10000

    print(f"Generating witnesses for sorry-region primes up to {B}...")

    primes = []
    for p in range(25, B + 1, 24):
        if not is_prime(p): continue
        if not in_sorry_region(p): continue
        primes.append(p)

    print(f"Found {len(primes)} sorry-region primes up to {B}")

    # Find witnesses
    witnesses = {}
    failures = []
    for p in primes:
        w = find_witness(p)
        if w:
            offset, b, c = w[0], w[1], w[2]
            witnesses[p] = (offset, b, c)
        else:
            failures.append(p)

    print(f"Witnesses found: {len(witnesses)}/{len(primes)}")
    if failures:
        print(f"FAILURES: {failures[:20]}")
        return

    # Generate Lean code
    lean_lines = []
    lean_lines.append("-- Auto-generated witness table for sorry-region primes")
    lean_lines.append(f"-- Primes up to {B}: {len(primes)}")
    lean_lines.append("")

    # Generate a lookup-style proof
    # For small B, use omega on each case
    lean_lines.append("-- Each witness (offset, b, c) satisfies:")
    lean_lines.append("-- offset % 4 = 3 ∧ b > 0 ∧ c > 0 ∧")
    lean_lines.append("-- (↑p + ↑offset : ℤ) * (↑b + ↑c) = 4 * ↑offset * ↑b * ↑c")
    lean_lines.append("")

    for p, (offset, b, c) in sorted(witnesses.items()):
        # Verify
        assert offset % 4 == 3, f"offset%4 = {offset%4} for p={p}"
        assert b > 0 and c > 0
        assert (p + offset) * (b + c) == 4 * offset * b * c, f"Type II fails for p={p}"
        lean_lines.append(f"-- p={p}: offset={offset}, b={b}, c={c}")

    # Write output
    outfile = f"/Users/kvallie2/Desktop/esc_stage8/witness_table_{B}.txt"
    with open(outfile, "w") as f:
        f.write("\n".join(lean_lines))
    print(f"\nWrote {len(lean_lines)} lines to {outfile}")

    # Also write a CSV for easy processing
    csvfile = f"/Users/kvallie2/Desktop/esc_stage8/witnesses_{B}.csv"
    with open(csvfile, "w") as f:
        f.write("p,offset,b,c\n")
        for p, (offset, b, c) in sorted(witnesses.items()):
            f.write(f"{p},{offset},{b},{c}\n")
    print(f"Wrote CSV to {csvfile}")

    # Stats
    print(f"\nStatistics:")
    offsets = [w[0] for w in witnesses.values()]
    bs = [w[1] for w in witnesses.values()]
    cs = [w[2] for w in witnesses.values()]
    print(f"  Max offset: {max(offsets)}")
    print(f"  Max b: {max(bs)}")
    print(f"  Max c: {max(cs)}")
    print(f"  Median offset: {sorted(offsets)[len(offsets)//2]}")


if __name__ == "__main__":
    main()
