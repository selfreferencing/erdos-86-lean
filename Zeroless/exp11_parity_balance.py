#!/usr/bin/env python3
"""
Experiment 11: Exact Parity Balance of the Survivor Set

Compute E_m (even-type) and O_m (odd-type) among orbit survivors at each
digit level m. For survivor x = 2^n mod 10^m (divisible by 2^m):
  u = x // 2^m  (5-adic parameter, 0 <= u < 5^m)
  Even-type if u is even  (lifts produce digits {0,2,4,6,8} => 4 survive)
  Odd-type  if u is odd   (lifts produce digits {1,3,5,7,9} => 5 survive)

Derivation: the 5 lifts to level m+1 have parameter v with 2v = u (mod 5^m).
If u even: v_0 = u/2 < 5^m/2, so digits are {0,2,4,6,8}.
If u odd:  v_0 = (u+5^m)/2 >= 5^m/2, so digits are {1,3,5,7,9}.

Formula: Z_{m+1} = 4*E_m + 5*O_m
         S_{m+1} = 1 - E_m/(5*Z_m)
"""

import sys, os, json, time, math
import numpy as np

sys.set_int_max_str_digits(100000)
DATA_DIR = os.path.join(os.path.dirname(__file__), "data")
os.makedirs(DATA_DIR, exist_ok=True)

M_MAX = 12  # T_10=7.8M, T_11=39M, T_12=195M.


def part_A():
    """Compute E_m, O_m, Z_m via full orbit enumeration."""
    print("=" * 90)
    print("PART A: Exact Parity Balance E_m, O_m, Z_m")
    print("=" * 90)

    results = {}
    for m in range(1, M_MAX + 1):
        mod = 10 ** m
        T = 4 * 5 ** (m - 1)
        five_m = 5 ** m
        min_val = mod // 10  # 10^(m-1)

        t0 = time.time()
        x = pow(2, m, mod)
        Z = E = O = 0

        for i in range(T):
            # String-based digit check (C-level, fast)
            if x >= min_val and '0' not in str(x):
                Z += 1
                u = x >> m   # x // 2^m (exact since 2^m | x)
                if u % 2 == 0:  # u even => even-type
                    E += 1
                else:
                    O += 1
            x = (x * 2) % mod

            if m >= 9 and i > 0 and i % (T // 5) == 0:
                el = time.time() - t0
                print(f"  [m={m}: {100*i//T}%, {el:.1f}s]",
                      file=sys.stderr, flush=True)

        elapsed = time.time() - t0
        ratio = E / Z if Z else 0
        bias = abs(ratio - 0.5)
        S_next = 1 - E / (5 * Z) if Z else 0

        results[m] = dict(
            E_m=E, O_m=O, Z_m=Z, period=T,
            ratio_E_Z=ratio, bias=bias, S_formula=S_next,
            elapsed=elapsed)

        print(f"\nm={m:2d} | T={T:>12,} | {elapsed:.2f}s")
        print(f"  Z={Z:>10,}  E={E:>10,}  O={O:>10,}")
        print(f"  E/Z={ratio:.10f}  |E/Z-½|={bias:.2e}  "
              f"S({m+1})={S_next:.10f}")

    return results


def part_B(results):
    """Convergence analysis of E/Z toward 1/2."""
    print("\n" + "=" * 90)
    print("PART B: Parity Ratio Convergence")
    print("=" * 90)

    ms = sorted(results.keys())
    print(f"\n{'m':>3} {'E/Z':>12} {'|bias|':>12} {'log2|bias|':>12}")
    print("-" * 45)
    for m in ms:
        r = results[m]
        lb = math.log2(r['bias']) if r['bias'] > 0 else float('-inf')
        print(f"{m:3d} {r['ratio_E_Z']:12.8f} {r['bias']:12.2e} {lb:12.2f}")

    # Geometric fit
    valid = [(m, results[m]['bias']) for m in ms
             if results[m]['bias'] > 0 and m >= 2]
    theta = C_fit = theta_late = C_late = None
    if len(valid) >= 3:
        xv = np.array([v[0] for v in valid])
        yv = np.array([math.log(v[1]) for v in valid])
        b, a = np.polyfit(xv, yv, 1)
        theta = math.exp(b)
        C_fit = math.exp(a)
        print(f"\nFull fit: |E/Z - ½| ~ {C_fit:.4f} * {theta:.6f}^m")
        print(f"  theta = {theta:.6f} "
              f"{'(CONVERGES)' if theta < 1 else '(>=1)'}")

        late = [(m, b2) for m, b2 in valid if m >= 4]
        if len(late) >= 3:
            xl = np.array([v[0] for v in late])
            yl = np.array([math.log(v[1]) for v in late])
            bl, al = np.polyfit(xl, yl, 1)
            theta_late = math.exp(bl)
            C_late = math.exp(al)
            print(f"Late fit (m>=4): theta = {theta_late:.6f}")

    # Successive ratios
    print(f"\nSuccessive bias ratios:")
    for i in range(1, len(ms)):
        m, mp = ms[i], ms[i-1]
        if results[mp]['bias'] > 0:
            r = results[m]['bias'] / results[mp]['bias']
            print(f"  bias({m})/bias({mp}) = {r:.6f}")

    return theta, C_fit, theta_late, C_late


def part_C(results):
    """Verify parity-fiber formula and Z_{m+1} = 4E_m + 5O_m."""
    print("\n" + "=" * 90)
    print("PART C: Verify Parity-Fiber Formula")
    print("=" * 90)

    ms = sorted(results.keys())

    # Verify identity
    print(f"\n{'m':>3} {'4E+5O':>12} {'Z(m+1)':>12} {'match':>6}")
    print("-" * 40)
    all_ok = True
    for i in range(len(ms) - 1):
        m = ms[i]
        if ms[i+1] != m + 1:
            continue
        pred = 4 * results[m]['E_m'] + 5 * results[m]['O_m']
        actual = results[m+1]['Z_m']
        ok = pred == actual
        all_ok = all_ok and ok
        print(f"{m:3d} {pred:12,} {actual:12,} "
              f"{'YES' if ok else 'NO'}")
    print(f"  {'ALL VERIFIED' if all_ok else 'FAILURES'}")

    # Verify S formula
    print(f"\n{'m':>3} {'S(formula)':>14} {'S(direct)':>14} {'diff':>12}")
    print("-" * 50)
    for i in range(len(ms) - 1):
        m = ms[i]
        if ms[i+1] != m + 1:
            continue
        Sf = 1 - results[m]['E_m'] / (5 * results[m]['Z_m'])
        Sd = results[m+1]['Z_m'] / (5 * results[m]['Z_m'])
        print(f"{m:3d} {Sf:14.10f} {Sd:14.10f} {abs(Sf-Sd):12.2e}")


def part_D(results):
    """Parity imbalance E-O analysis."""
    print("\n" + "=" * 90)
    print("PART D: Parity Imbalance Analysis")
    print("=" * 90)

    ms = sorted(results.keys())
    print(f"\n{'m':>3} {'E-O':>12} {'|E-O|/Z':>14} "
          f"{'|E-O| growth':>14}")
    print("-" * 55)
    prev = None
    for m in ms:
        r = results[m]
        d = r['E_m'] - r['O_m']
        frac = abs(d) / r['Z_m'] if r['Z_m'] else 0
        g = abs(d) / prev if prev and prev > 0 else 0
        gs = f"{g:.4f}" if prev else "---"
        print(f"{m:3d} {d:>+12,} {frac:14.2e} {gs:>14}")
        prev = abs(d) if abs(d) > 0 else None

    seq = [results[m]['E_m'] - results[m]['O_m'] for m in ms]
    print(f"\n  E-O sequence: {seq}")


def part_F(results):
    """Parity-type transition stats for small m."""
    print("\n" + "=" * 90)
    print("PART F: Parity-Type Transition Statistics")
    print("=" * 90)

    for m in range(2, min(M_MAX, 8) + 1):
        mod_m = 10 ** m
        mod_prev = 10 ** (m - 1)
        five_m = 5 ** m
        five_prev = 5 ** (m - 1)
        T = 4 * 5 ** (m - 1)
        min_val = mod_m // 10

        x = pow(2, m, mod_m)
        trans = {'EE': 0, 'EO': 0, 'OE': 0, 'OO': 0}
        pcounts = {'E': 0, 'O': 0}

        for i in range(T):
            if x >= min_val and '0' not in str(x):
                parent = x % mod_prev
                # Parent fiber type: u_parent = parent // 2^{m-1}
                u_p = parent >> (m - 1)
                p_type = 'E' if u_p % 2 == 0 else 'O'

                # Child fiber type at level m
                u_c = x >> m
                c_type = 'E' if u_c % 2 == 0 else 'O'

                trans[p_type + c_type] += 1
                pcounts[p_type] += 1

            x = (x * 2) % mod_m

        print(f"\nm={m}: E_parents={pcounts['E']}, O_parents={pcounts['O']}")
        for pt in ['E', 'O']:
            if pcounts[pt] > 0:
                for ct in ['E', 'O']:
                    k = pt + ct
                    p = trans[k] / pcounts[pt]
                    print(f"  {pt}->{ct}: {trans[k]:>8,} ({p:.4f})")
                total = trans[pt+'E'] + trans[pt+'O']
                print(f"  {pt} children/parent: "
                      f"{total/pcounts[pt]:.4f}")


def main():
    print(f"Experiment 11: Parity Balance (m=1..{M_MAX})\n")
    t_start = time.time()

    results = part_A()
    theta, C_fit, theta_late, C_late = part_B(results)
    part_C(results)
    part_D(results)
    part_F(results)

    # SUMMARY
    print("\n" + "=" * 90)
    print("SUMMARY")
    print("=" * 90)

    ms = sorted(results.keys())
    print(f"\n{'m':>3} {'Z':>10} {'E':>10} {'O':>10} "
          f"{'E/Z':>10} {'|E/Z-½|':>10} {'S(m+1)':>10}")
    print("-" * 75)
    for m in ms:
        r = results[m]
        print(f"{m:3d} {r['Z_m']:10,} {r['E_m']:10,} {r['O_m']:10,} "
              f"{r['ratio_E_Z']:10.6f} {r['bias']:10.2e} "
              f"{r['S_formula']:10.6f}")

    L = results[ms[-1]]
    print(f"\nAt m={ms[-1]}: E/Z={L['ratio_E_Z']:.10f}, "
          f"|E/Z-½|={L['bias']:.2e}")

    th = theta_late if theta_late else theta
    if th:
        print(f"Decay rate theta ~ {th:.4f}")
    weak = all(results[m]['ratio_E_Z'] > 0.05 for m in ms if m >= 2)
    strong = all(results[m]['bias'] < 0.01 for m in ms if m >= 4)
    print(f"Weak lemma (E/Z>0.05, m>=2): {'YES' if weak else 'NO'}")
    print(f"Near-balance (|E/Z-½|<0.01, m>=4): "
          f"{'YES' if strong else 'NO'}")

    if th and th < 1 and strong:
        print(f"\nCRITICAL: Parity balance converges to 1/2, "
              f"theta ~ {th:.4f}")
        print("Density-zero closes with a proof that theta < 1.")

    elapsed = time.time() - t_start
    print(f"\nTotal time: {elapsed:.1f}s")

    # Save
    save = {str(m): {k: v for k, v in results[m].items()
                     if k != 'elapsed'}
            for m in ms}
    save['_meta'] = {'M_MAX': M_MAX,
                     'theta_full': theta, 'theta_late': theta_late}
    path = os.path.join(DATA_DIR, "exp11_results.json")
    with open(path, 'w') as f:
        json.dump(save, f, indent=2, default=str)
    print(f"Saved to {path}")


if __name__ == '__main__':
    main()
