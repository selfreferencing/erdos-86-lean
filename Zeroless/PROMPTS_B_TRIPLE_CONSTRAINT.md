# Prompt Set B: The Triple Constraint Approach

## Context for All Prompts

These prompts target a potentially tractable SUB-PROBLEM of the 86 Conjecture, motivated by computational findings.

**The 86 Conjecture**: 2^86 is the largest power of 2 with no digit 0 in base 10.

**Key experimental finding (Experiment 3)**:
- The last n where 2^n, 2^{n+1}, 2^{n+2} are ALL zeroless: **n = 35**
- The last n where 2^n AND 2^{n+1} are both zeroless: **n = 76**
- The last n where 2^n alone is zeroless: **n = 86**

So triples die 51 exponents before singles. The compounding effect of requiring three consecutive powers to be zeroless is dramatically restrictive.

**The carry-drop mechanism**: When doubling a zeroless number x to get 2x, a zero in 2x is most likely produced when the carry chain transitions from 1 to 0. Specifically:
- carry_in = 0 with digit d = 5: output is 2*5 + 0 = 10, giving digit 0 (the ONLY zeroless input that produces a zero output)
- carry_in = 1: output is 2d + 1 (always odd, NEVER zero). So carry = 1 provides complete protection.
- Zero production rate: 0.200 for most carry patterns, but **0.360** for patterns with a 1-to-0 carry transition

**The correlation data**: Consecutive n-values have positively correlated zerolessness, and the correlation GROWS with scale:
- P(pair survivor) / P(single)^2: k=1: 1.00, k=4: 1.16, k=8: 1.43
- P(triple survivor) / P(single)^3: k=1: 1.00, k=4: 1.80, k=8: 2.65

Despite this growing correlation, the max paired suffix depth is 81 (vs single: 115) and max triple suffix depth is 42.

---

## Prompt B1: The Carry Rigidity Argument

### Goal
Prove that for all sufficiently large k, no three consecutive numbers n, n+1, n+2 can all have 2^n, 2^{n+1}, 2^{n+2} with k nonzero trailing digits. This would be a NEW result (weaker than the full conjecture but still non-trivial).

### Setup

If 2^n has k nonzero trailing digits, then 2^n mod 10^k is in the "survivor set" S_k. We want to show: for large k, there is no n such that 2^n, 2^{n+1}, and 2^{n+2} are all in S_k (mod 10^k).

The relationships:
- 2^{n+1} = 2 * 2^n
- 2^{n+2} = 4 * 2^n = 2 * 2^{n+1}

So if x = 2^n mod 10^k, then 2^{n+1} mod 10^k = (2x) mod 10^k and 2^{n+2} mod 10^k = (4x) mod 10^k.

The question becomes: for large k, does there exist x in Z/10^k Z such that x, 2x, and 4x ALL have no digit 0 (when written as k-digit numbers)?

### The carry chain constraints

When computing 2x from x (both k-digit zeroless numbers):
- At each digit position j, the output digit is (2 * d_j + c_j) mod 10, where c_j is the carry from position j-1.
- c_0 = 0 (no initial carry).
- c_j = floor((2 * d_{j-1} + c_{j-1}) / 10).

For x to be zeroless: d_j in {1,...,9} for all j.
For 2x to be zeroless: (2 * d_j + c_j) mod 10 != 0 for all j.
For 4x to be zeroless: the output of doubling 2x must also have no zero.

**The vulnerability**: At any position j where c_j = 0 and d_j = 5, the output digit is 0. So for 2x to be zeroless, we need: whenever c_j = 0, d_j != 5.

For 4x = 2*(2x): let y = 2x. Then 4x = 2y, and for 4x to be zeroless, whenever the carry in the second doubling is 0 at position j, the digit of y at position j must not be 5.

### Questions

1. **The carry-0 positions**: In the first doubling (x -> 2x), the carry chain starts at c_0 = 0. The carry at position j depends on all digits d_0, ..., d_{j-1}. For the carry to be 0 at position j, we need the cumulative effect of the first j digits to produce carry 0. Given that each digit d_i is in {1,...,9}, and carry propagation is memoryless (P(c=1) = 5/9 independent of input carry), the expected number of carry-0 positions in k digits is about 4k/9. At each such position, we need d_j != 5, which fails with probability 1/9. The expected number of failures in k digits is thus ~4k/81. For large k, this is large, suggesting a zero must appear. Can this be made rigorous?

2. **The double constraint**: For BOTH 2x and 4x to be zeroless, the constraints from two independent-ish carry chains must both be satisfied. The second carry chain (for doubling y = 2x) has its own carry-0 positions, which are correlated with but distinct from the first chain's. Can we bound the probability that both chains avoid producing a zero?

3. **The key combinatorial lemma needed**: Show that the number of k-digit zeroless numbers x such that 2x and 4x are also zeroless grows slower than 9^k (the total number of k-digit zeroless numbers). Specifically, show it grows as c * alpha^k with alpha < 9. Our data shows:
   - k=1: 8 (of 9), k=2: 64 (of 81), k=3: 514 (of 729), k=4: 4131 (of 6561)
   - Ratios: 8/9=0.889, 64/81=0.790, 514/729=0.705, 4131/6561=0.630
   - These ratios decay, suggesting alpha/9 < 1.

   Can you prove alpha < 9 using the carry chain analysis?

4. **The transfer matrix approach**: Define states as (carry_in_first_doubling, carry_in_second_doubling) = (c1, c2), each in {0, 1}. For each pair of input digits (d for first doubling, output_d_1 for second), the state transitions are determined. The 4x4 transfer matrix restricted to "both outputs nonzero" should have spectral radius < 9 (the full matrix has spectral radius 9). Can you compute this matrix explicitly and verify?

5. **Extension to the full conjecture**: If we can prove the triple constraint result, can it be leveraged toward the full conjecture? Note: for each digit count k, there are ~3.32 values of n giving k-digit powers. If we could show that no 3 consecutive orbit elements are all in S_k, and there are ~3.32 elements per level, we'd need a pigeonhole argument to get from "no 3 consecutive" to "at least one is out."

---

## Prompt B2: The Transfer Matrix for Double Doubling

### Goal
Explicitly construct and analyze the transfer matrix for the system:
"Given k-digit zeroless x, both 2x and 4x are also k-digit zeroless."

### Setup

**State space**: The carry state for the double-doubling system is (c1, c2) where:
- c1 = carry from x -> 2x at the current position
- c2 = carry from 2x -> 4x at the current position

Each is in {0, 1}, giving a 4-state system: (0,0), (0,1), (1,0), (1,1).

**Transitions**: For input digit d in {1,...,9} (zeroless x) and current state (c1, c2):

Step 1: Compute 2x digit
- output_1 = (2d + c1) mod 10
- new_c1 = (2d + c1) >= 10 ? 1 : 0
- Constraint: output_1 != 0

Step 2: Compute 4x digit
- output_2 = (2 * output_1 + c2) mod 10
- new_c2 = (2 * output_1 + c2) >= 10 ? 1 : 0
- Constraint: output_2 != 0

The transition is valid only if BOTH output_1 != 0 AND output_2 != 0.

### Questions

1. **Construct the 4x4 matrix M** where M[(c1',c2')][(c1,c2)] = number of digits d in {1,...,9} for which the transition (c1,c2) -> (c1',c2') is valid (both outputs nonzero). What is the spectral radius rho(M)?

2. **Compare to the unconstrained case**: The full matrix (no zero constraint) would count all d in {1,...,9} for each transition, giving total count 9 per column. The constrained matrix should have spectral radius < 9. By how much?

3. **The growth rate**: The number of k-digit zeroless x with 2x and 4x also zeroless grows as ~C * rho(M)^k. If rho(M) < 9, then the fraction of "triple survivors" among all zeroless numbers is (rho(M)/9)^k, which decays exponentially.

4. **Comparison with the single constraint**: For single doubling (x -> 2x both zeroless), the 2x2 conditioned transfer matrix has spectral radius 8.531 (we computed this). The ratio 8.531/9 = 0.948. For double doubling, the ratio should be smaller. How much smaller?

5. **Does this prove anything?** If rho(M) < 9, then the set of x with x, 2x, 4x all zeroless has density 0 among k-digit numbers. Combined with the fact that 2^n mod 10^k lands uniformly-ish on residues, this would suggest that triples die out. But to make it rigorous, we'd need to combine the transfer matrix bound with an equidistribution statement about 2^n mod 10^k.

6. **The crucial question**: Can the transfer matrix analysis alone (without equidistribution) prove the triple constraint? The answer is yes IF the number of triples C * rho(M)^k grows SLOWER than the period T_k = 4 * 5^{k-1}. Since 5 > rho(M)/9 * 5 = ... we need rho(M) < 9 * 5/5 = 9. Wait, let me reconsider. The number of valid triples at level k is rho(M)^k (approximately). The period is 4*5^{k-1}. We need rho(M)^k < 4*5^{k-1}, i.e., (rho(M)/5)^k < 4/5. This requires rho(M) < 5. Is rho(M) < 5?

---

## Prompt B3: Probability of Long Zeroless Runs Under Doubling

### Goal
Give a rigorous probability bound: if x is a uniformly random k-digit zeroless number, what is the probability that 2x is also zeroless? What about 2x AND 4x?

### Setup

Let Z_k = {x in [10^{k-1}, 10^k - 1] : all digits of x are in {1,...,9}}.
- |Z_k| = 9^k (since each of k digits has 9 choices independently... wait, actually k-digit numbers have leading digit in {1,...,9} and remaining digits in {0,...,9}. But for ZEROLESS numbers, ALL digits are in {1,...,9}. So |Z_k| = 9^k.)

For x uniform in Z_k:
- P(2x is zeroless) = ?
- P(2x and 4x are both zeroless) = ?

Our computation gave:
- k=1: P(2x zl) = 0.889, P(both) = 0.889
- k=3: P(2x zl) = 0.796, P(both) = 0.705
- k=5: P(2x zl) = 0.715, P(both) = 0.562
- k=7: P(2x zl) = 0.642, P(both) = 0.448

### Questions

1. **Exact formula for P(2x zeroless | x zeroless)**:
   The carry chain for doubling x is a Markov chain on {0, 1} with transition probabilities determined by the digit distribution (uniform on {1,...,9}). The initial state is c_0 = 0. At each step, digit d is drawn uniformly from {1,...,9}, and:
   - Output digit: (2d + c) mod 10
   - New carry: floor((2d + c) / 10)

   We showed the carry chain is memoryless: P(new_carry = 1) = 5/9 regardless of current carry. But the OUTPUT depends on carry:
   - c=0: output = 0 when d=5 (probability 1/9)
   - c=1: output is always odd, never 0 (probability 0)

   So P(output != 0 at position j) = P(c_j = 0) * (8/9) + P(c_j = 1) * 1.
   Since the carry chain is memoryless, P(c_j = 1) = 5/9 for j >= 1 (and c_0 = 0).
   So for j = 0: P(output != 0) = 1 * (8/9) + 0 * 1 = 8/9.
   For j >= 1: P(output != 0) = (4/9) * (8/9) + (5/9) * 1 = 32/81 + 45/81 = 77/81.

   If positions were independent (they ARE, since carry is memoryless!):
   P(2x zeroless) = (8/9) * (77/81)^{k-1}.

   Is this exact? (77/81 = 0.95062..., and (77/81)^{k-1} should match the observed P(2x zl).)
   Verify: k=1: 8/9 = 0.889 ✓. k=2: (8/9)*(77/81) = 0.846. Observed: 0.840. Close but not exact.

   Why the discrepancy? Is it because the carry ISN'T exactly memoryless when conditioned on zeroless output? (We found Dobrushin = 0.056 for the conditioned chain.)

2. **Rigorous upper bound**: Even if the exact formula isn't clean, can you prove P(2x and 4x both zeroless | x zeroless) <= C * alpha^k with alpha < 1? The data shows the ratio decays roughly as 0.93^k. An upper bound of this form would prove that the number of triple survivors is at most C * (9 * alpha)^k, which for alpha < 1 grows as (9*alpha)^k < 9^k.

3. **The transfer matrix gives the exact answer**: The number of x in Z_k with 2x, 4x both in Z_{k'} (where k' is the digit count of 4x) is exactly rho(M)^k * polynomial-correction. Computing rho(M) from Prompt B2 gives the exact growth rate. Is rho(M)/9 demonstrably < 1?

4. **Connection to the actual conjecture**: Suppose we prove that the fraction of k-digit zeroless x with 2x and 4x zeroless decays as alpha^k. The conjecture needs: for large n, 2^n is not zeroless. The connection: if 2^n is zeroless with k digits, then x = 2^n mod 10^k is zeroless, and 2x = 2^{n+1} mod 10^k. For the triple to die, we need this fraction to be small enough that "random" x has essentially zero chance of being a triple. But 2^n mod 10^k is NOT random -- it's a specific deterministic value. How do we bridge from the probabilistic statement to the deterministic one?

5. **The finite computation angle**: If the triple constraint transfers matrix has rho(M) < 5, then the total number of triples at level k is < 5^k, while the period is ~5^k. So the fraction of the orbit landing on triples is < 1/1 = bounded. But we need it to be < 1/(number of n per level) ~ 1/3.32. Can a more careful computation give rho(M) < 5/3.32^{1/k} ~< 5 for large k?

---

## Prompt B4: The Pair Constraint as a Stepping Stone

### Goal
Prove the WEAKEST possible non-trivial result: for all sufficiently large k, there is no n such that BOTH 2^n and 2^{n+1} have k nonzero trailing digits.

This is weaker than the triple constraint (which requires three consecutive) and much weaker than the full conjecture, but it would be a genuine new result.

### Why pairs might be easier

- Last observed pair: n=76 (still within the "small" range)
- Max paired suffix depth: 81 (vs single: 115)
- The pair constraint requires only ONE doubling to destroy zerolessness
- The transfer matrix is only 2x2 (carry state for one doubling)

### The 2x2 conditioned transfer matrix (from Experiment 1)

We computed:
```
M_cond = [[4, 4],
          [4, 5]]
```
Spectral radius: 8.531. Ratio to unconditioned (9): 0.948.

This means: the number of k-digit zeroless x such that 2x is also k-digit zeroless grows as ~C * 8.531^k. The total number of zeroless k-digit numbers is 9^k. So the fraction of pairs decays as (8.531/9)^k = 0.948^k.

### Questions

1. **Is 8.531 < 5?** No! 8.531 > 5. So the total number of pairs (~8.531^k) exceeds the period (~4*5^{k-1}) for large k. This means we CANNOT prove the pair constraint from the transfer matrix alone, because there are more pairs than period elements.

2. **What if we use the period constraint?** The 4*5^{k-1} orbit elements of 2^n mod 10^k include some that form pairs (n and n+1 both zeroless). The number of such paired elements is at most ~8.531^{k}/2 (dividing by 2 since each pair counts twice). Wait, that's not right either. The number of n-values in one period such that both 2^n and 2^{n+1} mod 10^k are zeroless is what we measured in Experiment 3 Test 6:

   k=1: 4 (of period 4)
   k=2: 17 (of period 20)
   k=3: 72 (of period 100)
   k=4: 307 (of period 500)
   k=5: 1309 (of period 2500)
   k=8: 101612 (of period 312500)

   The ratio 101612/312500 = 0.325. The density decays, but slowly (each level multiplies by ~4.26, not 4.5). The pair branching factor is 101612/23821 = 4.266 (from k=7 to k=8). This is LESS than 4.5 but still > 1.

3. **The pair branching factor**: If pairs branch at rate ~4.27 per level (not 4.5), the pair density per period element decays as (4.27/5)^k = 0.854^k. For the pair constraint to be provable, we need the ~3.32 orbit elements per digit level to miss ALL pairs. The expected number of pairs hit is 3.32 * 0.854^k * (period/period) = 3.32 * 0.854^k, which decays exponentially. So heuristically, pairs die for large k. But can this be made rigorous?

4. **The pair branching factor might be exactly computable**: At each level, each paired survivor (n with both n and n+1 surviving) lifts to some number of paired survivors at the next level. Can you compute this exactly? The pair lift count per parent determines the pair branching factor precisely.

5. **Alternative approach**: Instead of transfer matrices, could we directly count the number of residues r mod 10^k such that both r and 2r (mod 10^k) have all nonzero digits? This is a purely combinatorial question about multiplication by 2 in Z/10^k Z, with no orbit or equidistribution needed.

**Deliverable**: Either a proof that the pair branching factor is < 5 (which would make the pair constraint heuristically true), or an analysis of why even the pair constraint is hard.
