# Automaton / Coupled-State Prompts for Finiteness of Zeroless Powers of 2

## Context for all prompts

**The 86 Conjecture**: 2^86 is the largest power of 2 with no digit 0 in base 10.

**What we know** (from extensive computational and theoretical analysis):

1. Computationally verified: no zeroless 2^n for n = 87..10000. Also verified in Lean 4 for n = 87..302 via `native_decide`.
2. The "4.5^k barrier" blocks all digit-by-digit proof strategies: the net growth factor per digit level is 5 * (9/10) = 4.5 > 1, so survivor counts grow as ~4 * 4.5^(k-1). Confirmed from 5 independent angles.
3. The zeroless constraint is invisible to residues mod 2^k alone (density 1.0, tested to k=25) and mod 5^k alone (density 1.0, tested to k=8). The constraint lives ONLY in the joint mod-10^k structure, where density = (9/10)^(k-1). CRT factoring is impossible.
4. The additive Fourier spectrum of the zeroless set mod 10^k has a permanent obstruction: max coefficient = 1/9 (mod 5^k), not decaying with k.
5. Multiplicative Fourier on (Z/5^k Z)* is dead: every unit mod 5^k is zeroless-compatible.
6. For n >= k, the residue 2^n mod 10^k = CRT(0 mod 2^k, 2^n mod 5^k). The 2^n mod 5^k orbit is periodic with period 4 * 5^(k-1).
7. Suffix depth (number of consecutive nonzero digits from the right) can exceed 91: n=1958 has depth 93, n=7931 has depth 115. So a proof cannot just bound suffix depth.
8. S-unit / Subspace Theorem approaches are dead: zeroless is a positive-entropy condition (9^k possibilities among k-digit numbers) that cannot be compressed to O(1) S-unit terms. Baker/Matveev linear forms also fail because truncation quotients have uncontrolled height ~2^n.

**What we need**: ANY proof that the set E = {n in N : 2^n is zeroless in base 10} is finite. We do NOT need the exact cutoff 86.

**Why the automaton/coupled approach is the remaining hope**: Every approach that treats "last k digits" or "first k digits" in isolation fails. The zeroless condition is a JOINT constraint across ALL ~0.301n digits simultaneously. The only approaches not yet killed are those that couple the non-archimedean structure (mod 10^k, which controls trailing digits) with the archimedean structure ({n * log_10(2)}, which controls leading digits).

---

## PROMPT A1: The Doubling Automaton and the 4.5^k Barrier

### Goal
Determine whether modeling the "doubling with carry" operation as a finite automaton can overcome the 4.5^k barrier, and if not, identify precisely what additional structure would be needed.

### Setup
When we compute 2^(n+1) from 2^n by doubling, the operation on the decimal expansion is:
```
2 * d_i + carry_in = new_d_i + 10 * carry_out
```
where carry_in, carry_out in {0, 1} and d_i, new_d_i in {0,...,9}.

This defines a finite automaton:
- States: (carry, digit) pairs, or more generally, carry values at each position
- Alphabet: digits {0,...,9} (or {1,...,9} for zeroless)
- Transitions: the doubling rule above

The zeroless condition restricts the output alphabet to {1,...,9} at every position.

### Questions

1. **State space analysis**: Define the automaton precisely. At each digit position, the state is the incoming carry (0 or 1). The transition is: given digit d and carry c, output digit (2d + c) mod 10, carry out = floor((2d + c) / 10). For zeroless maintenance, we need (2d + c) mod 10 != 0. Which (d, c) pairs produce a zero output digit? These are exactly:
   - d = 0, c = 0: output 0 (but d = 0 is already forbidden in zeroless input)
   - d = 5, c = 0: output 0 (digit 5 with no carry produces 10, output digit 0)
   - d = 0, c = 1: output 1 (safe, but d = 0 forbidden)
   - d = 5, c = 1: output 1 (safe, carry 1)
   So among zeroless inputs (d in {1,...,9}), the ONLY dangerous case is d = 5 with c = 0. How does this constraint propagate through multiple doublings?

2. **The carry propagation graph**: For a k-digit zeroless number, the carries c_0, c_1, ..., c_{k-1} form a binary string determined by the digit string. Define the "carry graph" whose nodes are (position, carry) and edges are valid (digit, output_digit) transitions. How many zeroless k-digit numbers have a valid carry sequence under doubling (i.e., 2N is also zeroless)? Is this number smaller than 9^k? By how much?

3. **Iterated doubling**: 2^n = 2 * 2 * ... * 2 (n times) applied to 1. The first few are trivially zeroless (1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024...). After 2^10 = 1024, a zero appears. But 2^n regains zerolessness at various points up to n = 86. The automaton perspective: the "state" after n doublings is the full k-digit string plus carries, which is exponentially large. Can the automaton be compressed?

4. **Why 4.5^k reappears**: The number of k-digit zeroless numbers is 8 * 9^(k-1) (first digit 1-9, rest 1-9 except leading digit must be >= 1 for exactly k digits). Wait: actually it's 9^k if we fix k digits (each can be 1-9), but among all k-digit numbers (first digit 1-9, rest 0-9) there are 9 * 10^(k-1). So the density is 9^k / (9 * 10^(k-1)) = (9/10)^(k-1). The 4.5^k barrier arises because the doubling operation maps each zeroless number to ~5 possible zeroless successors (on average, because doubling a k-digit number can produce a k or (k+1)-digit result, and the carry structure creates ~5 valid extensions per digit). Explain exactly why the branching factor is 4.5 and not, say, 4 or 5.

5. **Can the automaton see what digit-by-digit counting cannot?** The 4.5^k barrier counts residue classes mod 10^k that are both zeroless-compatible and hit by the 2^n orbit. But 2^n mod 10^k has period 4 * 5^(k-1), which is much smaller than 4.5^k for large k. Specifically:
   - Zeroless-compatible residues mod 10^k: ~ 4 * 4.5^(k-1)
   - Size of 2^n orbit mod 10^k: 4 * 5^(k-1)
   - Ratio (orbit size / zeroless residues): 5^(k-1) / 4.5^(k-1) = (10/9)^(k-1) -> infinity

   So the orbit is MUCH LARGER than the zeroless set for large k. The density of zeroless residues within the orbit is (9/10)^(k-1). This means a RANDOM element of the orbit has probability (9/10)^(k-1) of being zeroless. For k = 91, this is (9/10)^90 ~ 7.5 * 10^{-5}. With an orbit of size 4 * 5^90 ~ 3.2 * 10^63, the expected number of zeroless orbit elements is ~2.4 * 10^59. This is still huge! So even the mod-10^91 constraint doesn't eliminate all candidates.

   But this counts LAST k digits only. The FULL zeroless condition also constrains the leading digits and all middle digits. Can the automaton incorporate leading-digit information?

### Deliverable
(a) A precise automaton model for "doubling preserves zeroless" with analysis of its state space growth, OR
(b) An explanation of why the automaton model is isomorphic to digit-by-digit counting and therefore subject to the same 4.5^k barrier, together with identification of what additional information (beyond mod-10^k residues) would need to be incorporated.

### References
- Cobham: "On the base-dependence of sets of numbers recognizable by finite automata"
- Allouche, Shallit: "Automatic Sequences: Theory, Applications, Generalizations"
- Adamczewski, Bell: "An analogue of Cobham's theorem for fractals"

---

## PROMPT A2: Coupling Archimedean and Non-Archimedean Constraints

### Goal
Determine whether coupling the mod-10^k residue (non-archimedean, controls trailing digits) with the fractional part {n * log_10(2)} (archimedean, controls leading digits) can prove that no large 2^n is zeroless.

### Setup
For a k-digit number 2^n:
- **Trailing digits**: determined by 2^n mod 10^k = CRT(0 mod 2^k, 2^n mod 5^k). The residue 2^n mod 5^k is periodic in n with period T_k = 4 * 5^(k-1). So the trailing digits repeat with this period.
- **Leading digits**: determined by the fractional part α_n = {n * log_10(2)}, where log_10(2) = 0.30103... is irrational. Specifically, 2^n = 10^{α_n} * 10^{floor(n*log_10(2))}, so the leading digits are determined by 10^{α_n}. By Weyl's theorem, α_n is equidistributed mod 1.
- **Digit count**: k = floor(n * log_10(2)) + 1, so k is also determined by n.

The zeroless condition requires ALL k digits to be nonzero. Trailing digits are controlled by mod-10^k, leading digits by α_n, and middle digits by the interaction.

### Questions

1. **The coupled state space**: Define the state of n as the pair (r_k(n), α_n) where r_k(n) = 2^n mod 10^k and α_n = {n * log_10(2)}. For each n, this pair determines 2^n completely (given k). The non-archimedean component is periodic (period T_k), and the archimedean component is equidistributed.

   KEY QUESTION: Are these two components independent? Since T_k = 4 * 5^(k-1) and the archimedean part has irrational frequency log_10(2), by Weyl's theorem the fractional parts {n * log_10(2)} for n in an arithmetic progression mod T_k are equidistributed. So yes, in the limit, the two components are asymptotically independent. Does this independence help or hurt?

2. **The density calculation**: If the two components were exactly independent, the probability that 2^n is zeroless would factor as:
   ```
   P(zeroless) ≈ P(trailing k digits zeroless) * P(leading digits zeroless | trailing ok)
   ```
   The first factor is (9/10)^(k-1) from the mod-10^k density. The second factor involves the leading digits, which are determined by 10^{α_n}. The leading digit is always nonzero (it's floor(10^{α_n}) in {1,...,9}). The second digit is the second digit of floor(10^{α_n} * 10^{k-1}). For the second digit to be zero, we'd need 10^{α_n} to be in certain intervals.

   Work out the probability that the FIRST zero digit (from the leading end) appears at position j, as a function of α_n. Is there a natural density for "the first L leading digits are all nonzero"?

3. **Can independence kill zeroless?** Here is the key argument sketch:
   - For 2^n to be zeroless with k digits, we need ALL k digits nonzero.
   - The trailing k/2 digits being zeroless has probability ~(9/10)^{k/2}.
   - The leading k/2 digits being zeroless has some probability p_{lead}(k/2).
   - If these events are "approximately independent" (which equidistribution of α_n suggests), then the joint probability is ~(9/10)^{k/2} * p_{lead}(k/2).
   - But actually, each digit being nonzero is NOT independent of the others (carries create correlations in trailing digits, and the decimal expansion of 10^{α_n} creates correlations in leading digits).
   - The question: do correlations help or hurt? Is there a way to prove that the joint event has probability decaying faster than 1/T_k = 1/(4 * 5^{k-1}), which would mean the expected number of zeroless 2^n with k digits goes to 0?

4. **The Borel-Cantelli approach**: For each k, let N_k = #{n : 2^n has exactly k digits and is zeroless}. The conjecture is that N_k = 0 for all k >= 27 (since the last zeroless power with k = 26 digits is 2^86). Can we estimate N_k using equidistribution?

   Heuristically:
   - Number of n with k digits: the interval of n is approximately [k/log_10(2) - 1, k/log_10(2)], so about 1/log_10(2) ~ 3.32 values of n per digit length k.
   - Probability each such n is zeroless: this is the hard part. If all k digits were independent Benford-like, the probability would be something like (1 - P(digit = 0))^k. But digit 0 probability varies by position.

   Give a rigorous or heuristic estimate of N_k and determine whether sum_k N_k converges (which would imply finiteness of E by Borel-Cantelli, if we could make the estimate rigorous).

5. **The middle digits problem**: Even if trailing and leading digits can be controlled, the MIDDLE digits (positions ~k/3 to ~2k/3) are influenced by both the mod-10^k residue and the fractional part, but neither alone determines them precisely. This is the "no man's land" where neither the archimedean nor non-archimedean analysis has direct traction. Is there a third ingredient needed for middle digits? Or does the joint (mod-10^k, α_n) state actually determine all digits (which it does, since it determines 2^n)?

### Deliverable
(a) A rigorous or heuristic estimate of the expected number of zeroless 2^n with k digits, showing whether Borel-Cantelli-type reasoning gives finiteness, OR
(b) An identification of why the coupling argument fails (e.g., correlations are too strong, or the density doesn't decay fast enough), with a precise statement of what additional ingredient would be needed.

### References
- Weyl: "Uber die Gleichverteilung von Zahlen mod. Eins"
- Diaconis: "The distribution of leading digits and uniform distribution mod 1"
- Kontoyiannis, Miller: on digit distributions of powers
- Fan, Liao, Ma: "Level sets of the Takagi function and Hausdorff dimension" (related digit-constraint questions)

---

## PROMPT A3: Finite-State Compression via the 5-adic Orbit

### Goal
Determine whether the periodic structure of 2^n mod 5^k can be exploited to build a finite proof that no n > 86 gives a zeroless 2^n, by bootstrapping from finite computation.

### Setup
Key structural fact: 2^n mod 5^k is periodic in n with period T_k = 4 * 5^(k-1). So the residue 2^n mod 10^k (which determines the last k digits) is also periodic with the same period (since 2^n mod 2^k = 0 for n >= k, the CRT reconstruction is trivially periodic).

This means: for fixed k, the "zeroless suffix" question is entirely determined by n mod T_k. There are exactly T_k = 4 * 5^(k-1) possible residues, and we can (in principle) check each one.

Our computational data:
- For n = 87..10000, no zeroless 2^n found.
- Suffix depth (max consecutive nonzero trailing digits) reaches 115 at n = 7931.
- The alive count mod 10^k is exactly 4 * 4.5^(k-1) (confirmed from 5 angles).

### Questions

1. **Period vs. alive count**: For level k:
   - Period: T_k = 4 * 5^(k-1)
   - Alive (zeroless-compatible residues hit by 2^n): A_k = 4 * 4.5^(k-1)
   - Ratio: A_k / T_k = (4.5/5)^(k-1) = (9/10)^(k-1)

   So 2^n hits A_k distinct zeroless residues mod 10^k, out of T_k total orbit elements. The fraction (9/10)^(k-1) is exactly the density of zeroless numbers among all numbers. This is NOT a coincidence: it says the 2^n orbit samples the zeroless set at exactly the expected density. There is no anomalous avoidance or attraction.

   But this is only for the LAST k digits. Can we show that requiring ALL digits to be nonzero (including leading digits, determined by the fractional part) eliminates the remaining A_k candidates?

2. **The hierarchical elimination question**: At level k, we have A_k alive residues. At level k+1, each alive residue mod 10^k lifts to at most 9 alive residues mod 10^{k+1} (extending by a nonzero digit on the left). But wait, "extending on the left" in the mod-10^k tower means adding a digit at position k, which is the (k+1)-th digit from the right. The constraint is that this new digit is nonzero.

   The 4.5^k barrier says: on average, each alive residue mod 10^k lifts to 4.5 alive residues mod 10^{k+1}. This is because 5 of the 10 possible extensions (mod 5) are valid (the 2^n orbit hits 5 residues mod 5^{k+1} for each residue mod 5^k, since the orbit mod 5^{k+1} has period 5 times longer), and 9/10 of those have nonzero digit at position k+1. So: 5 * (9/10) = 4.5.

   Can this hierarchy be analyzed as a branching process? In a Galton-Watson process with mean offspring 4.5, the population explodes. But 2^n is not a random branching process: it has specific arithmetic structure. Does the SPECIFIC structure of the 5-adic orbit create correlations that might cause the branching process to die out, despite having mean > 1?

3. **Coupling with the digit length constraint**: A k-digit power of 2 satisfies 10^{k-1} <= 2^n < 10^k, so n is in the range [(k-1)/log_10(2), k/log_10(2)), which contains about 3.32 values of n. For those specific n values, 2^n mod 10^k is determined.

   At level k, the alive set has A_k ~ 4 * 4.5^{k-1} residues, but only ~3.32 values of n actually produce k-digit numbers. So the question is: do any of those 3.32 values of n land on one of the A_k alive residues?

   For large k, A_k / T_k = (9/10)^{k-1} -> 0, so the probability that a random orbit element is alive goes to 0. With ~3.32 trials, the expected number of hits is ~3.32 * (9/10)^{k-1}. For k = 91, this is ~3.32 * 7.5 * 10^{-5} ~ 2.5 * 10^{-4}. Summing over k >= 91: sum_{k>=91} 3.32 * (9/10)^{k-1} = 3.32 * (9/10)^{90} / (1 - 9/10) = 3.32 * (9/10)^{90} * 10 ~ 0.0025.

   So the EXPECTED total number of zeroless 2^n with k >= 91 digits is about 0.0025, which is already < 1. This is the standard heuristic for why the conjecture should be true.

   Can this heuristic be made rigorous? What would it take to convert the equidistribution-based expected count into a genuine proof?

4. **The quasi-random sampling argument**: The values of n that produce k-digit numbers are n in {ceil((k-1)/log_10(2)), ..., floor(k/log_10(2) - epsilon)}. The residues 2^n mod 10^k for these n values are determined by n mod T_k. Since log_10(2) is irrational, the values of n mod T_k as k varies should behave "quasi-randomly" (by the three-distance theorem or discrepancy bounds for {n * log_10(2)}).

   Can discrepancy bounds (Erdos-Turan, Koksma-Hlawka) be used to show that the ~3.32 values of n do NOT preferentially land on the A_k alive residues? Specifically, if the discrepancy of the sequence n mod T_k (for the relevant n values) is delta_k, then the count of zeroless hits satisfies:
   ```
   |actual hits - expected hits| <= delta_k * T_k
   ```
   For this to give "0 hits", we'd need delta_k * T_k < expected hits ~ 3.32 * (9/10)^{k-1}, i.e., delta_k < (9/10)^{k-1} / T_k = (9/10)^{k-1} / (4 * 5^{k-1}) = (9/50)^{k-1} / 4.

   This requires EXTREMELY good equidistribution (discrepancy decaying exponentially in k). Standard Erdos-Turan bounds give discrepancy ~ 1/sqrt(T_k) at best, which is nowhere near sufficient. Is there a way to get exponential discrepancy bounds for this specific sequence?

5. **The "eventual periodicity" bootstrap**: Here is a more computational approach. For each k, the set of "dangerous n values" (those where 2^n mod 10^k is zeroless) is periodic with period T_k. If we could:
   (a) For each k from 1 to K, compute the dangerous set D_k = {n mod T_k : 2^n mod 10^k is k-digit-zeroless}
   (b) Show that the intersection D_1 ∩ D_2 ∩ ... ∩ D_K (lifted appropriately via CRT) is empty for n > 86

   Then we'd have a proof. But T_k grows as 4 * 5^{k-1}, and for k = 91 this is ~3.2 * 10^{63}. We can't enumerate that. Is there a way to represent D_k implicitly (e.g., as a union of arithmetic progressions) and compute the intersection symbolically?

### Deliverable
(a) An assessment of whether the heuristic expected-count argument (item 3) can be made rigorous, identifying the key gap between heuristic and proof, OR
(b) A concrete finite-computation strategy that would constitute a proof, with an analysis of its computational feasibility, OR
(c) A proof that no finite-computation strategy of this type can work, explaining why the problem is inherently infinite.

### References
- Kuipers, Niederreiter: "Uniform Distribution of Sequences"
- Erdos, Turan: "On a problem in the theory of uniform distribution" (discrepancy bounds)
- Everest, van der Poorten, Shparlinski, Ward: "Recurrence Sequences" (periodic structure of exponential sequences)
- Lagarias: "Ternary expansions of powers of 2" (analogous digit problem)
- Bourgain: "Prescribing the binary digits of primes" (state-of-art digit constraint methods)
