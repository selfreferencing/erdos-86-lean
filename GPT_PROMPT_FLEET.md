# GPT Prompt Fleet: Subdivided ESC Problem

If the main prompt doesn't yield a complete proof, use these focused sub-prompts to attack specific pieces.

---

## PROMPT 1: Coprime Pair Sum Distribution

**Question**: Let n be a positive integer with τ(n) divisors. Let S(n) = {a + b : a, b | n, gcd(a, b) = 1, a ≤ b} be the set of coprime divisor pair sums.

For a modulus m, how are the elements of S(n) distributed mod m?

Specifically:
1. What bounds exist on |{s ∈ S(n) : s ≡ r (mod m)}| for a given residue r?
2. Under what conditions on n and m is 0 guaranteed to appear in S(n) mod m?
3. Are there character sum estimates for Σ_{(a,b) coprime divisors} χ(a + b)?

**Context**: I need to show that for "most" integers n, the set S(n) mod m is well-distributed enough that it hits 0 with high probability.

---

## PROMPT 2: Structure of Consecutive Integers

**Question**: Among K consecutive integers n, n+1, ..., n+K-1:

1. How many have at least 4 divisors? (Lower bound)
2. How many have coprime divisor pairs (a, b) with a, b > 1? (i.e., non-trivial pairs)
3. What's the density of integers where gcd(d, n/d) = 1 for some d with 1 < d < n?

**Context**: I need to show consecutive integers have "enough" coprime structure to guarantee hitting various residue conditions.

---

## PROMPT 3: Impossibility of Simultaneous Avoidance

**Question**: Consider the system of conditions:
- C_0: "n has no coprime divisor pair summing to 0 mod 3"
- C_1: "n+1 has no coprime divisor pair summing to 0 mod 7"
- C_2: "n+2 has no coprime divisor pair summing to 0 mod 11"
- ...
- C_K: "n+K has no coprime divisor pair summing to 0 mod (4K+3)"

Can all conditions C_0, C_1, ..., C_K hold simultaneously for some n?

**Approach**:
- Analyze C_j as a condition on n mod some modulus
- Show these conditions are incompatible (like a covering system argument)
- Or show the "density" of n satisfying all C_j tends to 0

---

## PROMPT 4: The k=0 Case Analysis

**Question**: For which integers x does x have coprime divisors (a, b) with a + b ≡ 0 (mod 3)?

Characterize completely:
1. Which x ALWAYS have such a pair?
2. Which x NEVER have such a pair?
3. What's the density of each class?

**Note**: Since m_0 = 3, this is the simplest case. Understanding it completely might reveal the pattern for general m_k.

**Examples**:
- x = 6: pairs (1,6), (2,3). Sums: 7, 5. Neither ≡ 0 (mod 3). FAILS.
- x = 12: pairs include (3,4). Sum = 7 ≢ 0. pairs include (1,12). Sum = 13 ≡ 1. FAILS.
- x = 15: pairs (1,15), (3,5). Sums: 16, 8. 16 ≡ 1, 8 ≡ 2. FAILS.
- x = 9: pairs (1,9). Sum = 10 ≡ 1. FAILS.
- x = 10: pairs (1,10), (2,5). Sums: 11, 7. 11 ≡ 2, 7 ≡ 1. FAILS.

Wait, which x DO work for k=0?

---

## PROMPT 5: Even Number Structure

**Question**: Let x = 2^a · m where m is odd and m > 1. Then (2^a, m) is a coprime divisor pair with sum 2^a + m.

For which moduli M is 2^a + m ≡ 0 (mod M) solvable given constraints on x?

Specifically: Given x = 2^a · m, for which M in {3, 7, 11, 15, 19, 23} is 2^a + m ≡ 0 (mod M)?

**Goal**: Show that among any 6 consecutive integers, at least one even number x = 2^a · m has 2^a + m ≡ 0 (mod 4k+3) for its corresponding k.

---

## PROMPT 6: Literature Search

**Question**: What is known about the following topics in analytic number theory?

1. Distribution of divisor pair sums modulo m
2. Covering systems involving divisor conditions
3. The "sum-of-divisors" function restricted to coprime pairs
4. Applications of character sums to divisor problems
5. The Erdős-Straus conjecture proof attempts via divisor methods

Please identify key papers, especially anything by:
- Elsholtz (worked on ESC)
- Schinzel (covering systems)
- Saias (ESC computational work)
- Anyone working on "coprime divisor" problems

---

## PROMPT 7: Minimal Counterexample Analysis

**Question**: Suppose the theorem is FALSE. Then there exists a prime p ≡ 1 (mod 4) such that for ALL k ≥ 0, x_k = (p + 4k + 3)/4 has NO coprime divisor pair summing to 0 mod (4k + 3).

What properties would such a p have?

1. What constraints does this place on (p + 3)/4?
2. What constraints on (p + 7)/4, (p + 11)/4, ...?
3. Can we derive a contradiction from these constraints?

**Approach**: Assume counterexample exists, derive properties, show no such p can exist.

---

## PROMPT 8: Computational Boundary Analysis

**Question**: We've verified the theorem for all p < 10^7. To extend this:

1. What's the asymptotic density of primes p where first-success k = 0?
2. Is there a pattern to which p require k > 0?
3. Can we prove: for p > P_0, the theorem holds with k ≤ K_0?

**Data**:
- p = 2521 requires k = 5 (the worst case found)
- 2521 = 7 × 360 + 1 (has special structure)
- x_0 = 631 = prime, x_1 = 632 = 8×79, ..., x_5 = 636 = 4×159

Why does 2521 need k = 5? Can we characterize all "hard" primes?

---

# Usage Instructions

1. **Try the main prompt first** (GPT_PROOF_PROMPT.md)

2. **If no complete proof**, use prompts 1-3 to understand the structure better

3. **If promising direction emerges**, use prompts 4-5 to develop specific cases

4. **If stuck**, use prompt 6 for literature and prompt 7 for contradiction approach

5. **Synthesize** results from multiple prompts into a unified attack

---

# Meta-Prompt Option

If the fleet doesn't work, here's a meta-prompt:

**Meta-Prompt**: "I have a mathematical theorem I'm trying to prove. I've tried direct approaches and they haven't worked. I'm now going to describe the problem and my failed attempts. Please analyze WHY my approaches failed and suggest a fundamentally different strategy.

[Insert problem description]

Failed approaches:
1. Probabilistic argument (heuristic, not rigorous)
2. Bounded k argument (false: k can exceed 5)
3. Character sum estimates (couldn't make tight enough)

What's the RIGHT way to attack this?"
