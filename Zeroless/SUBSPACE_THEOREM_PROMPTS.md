# S-unit / Subspace Theorem Prompts for Finiteness of Zeroless Powers of 2

## Context for all prompts

**The 86 Conjecture**: 2^86 is the largest power of 2 with no digit 0 in base 10.

**What we know** (from extensive computational and theoretical analysis):

1. Computationally verified for n = 87..302 (Lean 4 formalization with `native_decide`).
2. The "4.5^k barrier" blocks all digit-by-digit proof strategies: the net growth factor per digit level is 5 * (9/10) = 4.5 > 1, so survivor counts grow exponentially.
3. The zeroless constraint is invisible to residues mod 2^k alone (density 1.0 for all k, tested to k=25) and mod 5^k alone (density 1.0 for all k, tested to k=8). The constraint lives ONLY in the joint mod-10^k structure, where density = (9/10)^(k-1).
4. The additive Fourier spectrum of the zeroless set mod 10^k has a permanent obstruction: max coefficient = 1/9 (mod 5^k) and 1/4 (mod 10^k, normalized), neither decaying with k.
5. For n >= k, the residue 2^n mod 10^k satisfies 2^k | (2^n mod 10^k), i.e., the last k digits of 2^n form a number divisible by 2^k. This is a strong structural constraint from CRT: 2^n mod 10^k = CRT(0 mod 2^k, 2^n mod 5^k).

**What we need**: ANY proof that the set E = {n in N : 2^n is zeroless in base 10} is finite. We do NOT need the exact cutoff 86. Even proving |E| < 10^100 or that E is contained in {0,...,N_0} for some explicit N_0 would be a breakthrough.

---

## PROMPT S1: The Compression Lemma

### Goal
Determine whether zerolessness of 2^n can force a "compression" of the digit expansion into a bounded number of S-unit terms, enabling application of the Subspace Theorem.

### Setup
A k-digit zeroless power of 2 satisfies:
```
2^n = d_0 + d_1 * 10 + d_2 * 10^2 + ... + d_{k-1} * 10^{k-1}
```
where each d_i in {1,...,9}. This is a sum of k terms, each an S-unit for S = {2, 5} with bounded coefficients. The Subspace Theorem (Evertse-Schlickewei-Schmidt) gives finiteness when the NUMBER of terms is fixed, but here k grows with n (k ~ n * log_10(2) ~ 0.301 * n).

### Question
Is there a way to "compress" this sum into a bounded number of terms? Specifically:

1. **Block grouping**: Group consecutive digits into blocks of length B. Each block contributes a term of the form (sum of digits * powers of 10 within the block) * 10^{Bi}. The coefficient of each block is an integer in [B-digit zeroless numbers]. For B fixed, you get ceil(k/B) terms, still growing. But if the COEFFICIENTS are S-units themselves (which they're not generally), the Subspace Theorem applies.

2. **Carry structure**: When 2^n is computed digit by digit, carries propagate. Does the carry structure impose enough rigidity that the expansion can be rewritten with fewer independent terms?

3. **Factorization approach**: Can we write 2^n = A * 10^m + B where A and B are zeroless and m is chosen to split at a zero-free position? If 2^n is zeroless, this decomposition is trivial (take m=0). But if we could show that ANY decomposition 2^n = A * 10^m + B with A, B in some structured set forces a bounded number of S-unit terms...

4. **Corvaja-Zannier style**: Corvaja-Zannier prove that for integers N with "few nonzero digits" in two multiplicatively independent bases, N must satisfy certain constraints. Our condition is the OPPOSITE (all digits nonzero), but can their machinery be adapted? Specifically, can "all digits nonzero in base 10" plus "only one nonzero digit in base 2" (since 2^n = 1 followed by zeros in base 2) create a Subspace Theorem contradiction?

### Deliverable
Either:
(a) A sketch of a compression lemma that reduces the variable-length sum to O(1) S-unit terms, enabling Subspace Theorem application, OR
(b) A clear explanation of why no such compression exists, identifying the precise obstruction.

### References
- Evertse, Schlickewei, Schmidt: "The number of solutions of decomposable form equations"
- Corvaja, Zannier: "On the number of integral points on algebraic curves" and related work on S-units with digit constraints
- Bennett, Bugeaud, Mignotte: "Perfect powers with few binary digits and few ternary digits"
- Dimitrov, Howe: "Powers of 2 as sums of two powers of 3" (bounded-term ternary result)
- Senge, Straus: "PV numbers and sets of multiplicity"
- Stewart: "On the representation of an integer in two different bases"

---

## PROMPT S2: The Two-Bases Obstruction

### Goal
Determine whether the Senge-Straus / Stewart "two bases" technology can be adapted from "few nonzero digits" to "no zero digits."

### Setup
Senge-Straus (1971) proved: for multiplicatively independent bases b_1, b_2, the number of integers with at most r nonzero digits in BOTH bases is finite (for any fixed r). Stewart (1980) made this effective.

Our situation: 2^n has exactly 1 nonzero digit in base 2 (trivially), and we want to show it has at least one ZERO digit in base 10 for all large n. Base 2 and base 10 are not multiplicatively independent (10 = 2 * 5), but 2 and 5 are.

### Questions

1. **Direct adaptation**: Senge-Straus bounds the count of integers with "few nonzero digits" in two independent bases. We want "all nonzero digits" in base 10 plus "one nonzero digit" in base 2. Can "all nonzero" be converted to "few nonzero" via complementation? E.g., if N has k digits all nonzero, then 10^k - 1 - N + ... hmm, this doesn't simplify.

2. **Digit sum variant**: A zeroless k-digit number N satisfies s_10(N) >= k (digit sum >= k, since each digit >= 1) and s_10(N) <= 9k. The digit sum of 2^n in base 10 is known to satisfy s_10(2^n) ~ 4.5 * k (by equidistribution heuristic). Does the constraint s_10(2^n) >= k (which is weaker than zeroless) combine with s_2(2^n) = 1 to give a Senge-Straus type result?

3. **The v_p obstruction**: For a zeroless number N = d_0 + d_1*10 + ..., the p-adic valuation v_5(N) depends on d_0 only (v_5(N) = v_5(d_0), which is 1 if d_0 = 5 and 0 otherwise). But v_5(2^n) = 0 for all n. So d_0 != 5 is forced. Similarly, v_2(2^n) = n, but v_2(N) = v_2(d_0) <= 3. So for n > 3, 2^n cannot equal a number whose 2-adic valuation is <= 3. WAIT: this seems to immediately prove the conjecture for n > 3. But 2^86 IS zeroless, so there must be an error. What's wrong with this argument? (This is a crucial sanity check.)

4. **Resolution of the v_2 issue**: The error must be that v_2(d_0 + d_1*10 + ...) is NOT simply v_2(d_0) when there are carries. Clarify exactly how carries affect the 2-adic valuation of a multi-digit sum, and determine whether ANY useful valuation constraint survives.

### Deliverable
(a) An assessment of whether Senge-Straus / Stewart can yield finiteness of zeroless 2^n, and if so, what the key lemma would be.
(b) A resolution of the v_2 / v_5 valuation question (item 3 above): either it gives a proof, or explain precisely why carries invalidate it.

### References
- Senge, Straus: "PV numbers and sets of multiplicity" (1971)
- Stewart: "On the representation of an integer in two different bases" (1980)
- Lagarias: "Ternary expansions of powers of 2"

---

## PROMPT S3: Effective Bounds via Baker's Method

### Goal
Determine whether Baker-type linear forms in logarithms can produce an explicit upper bound N_0 such that all zeroless 2^n have n <= N_0.

### Setup
A standard approach in exponential Diophantine problems:
1. Show the problem implies a "small" linear form in logarithms.
2. Apply Baker-Wustholz / Matveev lower bounds.
3. Get an explicit (though possibly huge) upper bound.
4. Reduce the bound computationally (LLL, etc.).

For our problem: if 2^n is a k-digit zeroless number, then:
- k ~ n * log_10(2), so k ~ 0.301 * n
- The leading digits of 2^n are determined by {n * log_10(2)} (the fractional part)
- If 2^n starts with digits d_{k-1} d_{k-2} ..., then d_{k-1} * 10^{k-1} <= 2^n < (d_{k-1}+1) * 10^{k-1}
- Taking logs: log_10(d_{k-1}) <= {n * log_10(2)} < log_10(d_{k-1} + 1)
- For d_{k-1} in {1,...,9} (zeroless), this constrains {n * log_10(2)} to lie in the union of intervals [log_10(d), log_10(d+1)) for d = 1,...,9, which is [0, 1) minus the empty set (since we're just saying the leading digit is nonzero, which is always true for 2^n).

So the LEADING digit alone gives no constraint (it's never 0). The constraint comes from INTERIOR digits.

### Questions

1. **Interior digit constraint**: If digit j (from the right, 0-indexed) of 2^n equals 0, this means:
   floor(2^n / 10^j) mod 10 = 0
   which means 10 | floor(2^n / 10^j), i.e., 2^n mod 10^{j+1} is in the range [0, 10^j) union [2*10^j, 3*10^j) union ... union [9*10^j, 10^{j+1}).
   Can this be turned into a linear form in logarithms?

2. **Truncation approach**: Consider the "truncated" number T_m = 2^n mod 10^m (the last m digits). If 2^n is zeroless, then T_m is a zeroless m-digit number (possibly with leading zeros... no, each digit is nonzero so no leading zeros except T_m might be < 10^{m-1}... actually T_m could be anything with all nonzero digits when written with m digits). The key: T_m = 2^n - floor(2^n / 10^m) * 10^m. So:
   |2^n - floor(2^n / 10^m) * 10^m| = T_m < 10^m
   This gives: |n * log(2) - m * log(10) - log(floor(2^n/10^m))| is small. But floor(2^n/10^m) is a specific integer that depends on n.

3. **Can Baker's method yield ANY bound?** Even if N_0 is 10^{10^{10}}, that would be a theoretical breakthrough. The question is whether the structure of zeroless constraint can be encoded as a small linear form AT ALL.

4. **The p-adic Baker alternative**: Instead of archimedean Baker bounds, use p-adic (5-adic) linear forms. Since 2^n mod 5^k is periodic with period 4*5^{k-1}, the constraint "last k digits of 2^n are all nonzero" translates to 2^n mod 10^k avoiding certain residue classes. If we could show that these residue classes force |2^n - A|_5 to be small for some structured A, then 5-adic Baker bounds apply.

### Deliverable
An assessment of whether Baker's method can produce any explicit bound for zeroless 2^n, identifying the key reduction step (or explaining why no reduction exists).

### References
- Baker, Wustholz: "Logarithmic forms and Diophantine geometry"
- Matveev: "An explicit lower bound for a homogeneous rational linear form in logarithms of algebraic numbers"
- de Weger: "Algorithms for Diophantine equations" (LLL reduction of Baker bounds)
- Bennett, Bugeaud, Mignotte: "Perfect powers with few binary digits and few ternary digits"
