# GPT Prompt 21: Construct the Finite-State Automaton and Compute Spectral Gap

## Context

We're proving the 86 Conjecture. You've established (Prompts 19-20) that:

1. **5-orbit cancellation is exact**: For ℓ ≢ 0 (mod 5), the sum over a full 5-orbit vanishes
2. **The gap**: S_k picks one representative per orbit, so orbit cancellation doesn't directly apply
3. **The missing input**: Either uniform Fourier decay OR a spectral gap for a transfer operator

You identified the key to-do list:
1. **Finite-state encoding**: Prove survival is determined by bounded-size state
2. **Spectral gap**: Bound nontrivial Fourier modes by < 4.5 (ideally ≤ √5)
3. **Uniformity**: Same bound for cylinders

You offered: "I can try to actually build the smallest plausible state space for the 'forced tail' recursion."

**This prompt asks you to do exactly that.**

## The Setup

### The Survivor Recursion
- T_k = 4·5^{k-1}
- S_k ⊂ {0, 1, ..., T_k - 1} are level-k survivors
- |S_k| = 4 × 4.5^{k-1} exactly
- Each r ∈ S_k has 5 potential children at level k+1: r, r+T_k, r+2T_k, r+3T_k, r+4T_k
- Exactly 4 or 5 of these survive (the "4-or-5 children theorem")

### The Digit Test
The k-th digit (0-indexed from right) is zero iff:
```
u_{k+1}(n) < 5^k/2   where u_{k+1}(n) = 2^{n-k-1} mod 5^{k+1}
```

### The 5-adic State Decomposition
Write u_{k+1}(r) = a(r) + 5^k·t(r) where:
- a(r) = u_{k+1}(r) mod 5^k ∈ {0,...,5^k-1}, with 5 ∤ a(r) for survivors
- t(r) = ⌊u_{k+1}(r) / 5^k⌋ ∈ {0,1,2,3,4} (top digit)

### What Determines Survival?
For r ∈ S_k to have child r+jT_k survive at level k+1:
- Need the (k+1)-th digit to be nonzero
- This depends on u_{k+2}(r+jT_k) = 2^{r+jT_k-k-2} mod 5^{k+2}

## The Request

### Question 1: Build the State Space

What is the **minimal state** that determines:
1. Whether r survives at level k (given r mod T_k)
2. Which of r's 5 children survive at level k+1

Candidates for what the state might contain:
- u_{k+1}(r) mod 5^{k+1}? (This is the full 5-adic state)
- Just a(r) mod 5^k?
- Just a(r) mod 5? (This would be ideal - constant size!)
- Some carry information?

**Key question**: Does the state space have **bounded size** (independent of k), or does it grow with k?

### Question 2: Write Down the Transition Matrices

Once you have the state space X, define:
- The transition from level k to k+1 as a (possibly stochastic) matrix
- For each ℓ ≢ 0 (mod 5), define the **twisted** transition matrix M_ℓ that incorporates the phase e(ℓ·Δu / 5^{k+1})

Explicitly:
```
(M_ℓ)_{s,s'} = Σ_{transitions s→s'} e(ℓ · phase_increment / 5^{k+1})
```

### Question 3: Compute or Bound the Spectral Gap

For the twisted matrices M_ℓ (ℓ ≢ 0 mod 5):
1. What is the spectral radius ρ(M_ℓ)?
2. Is ρ(M_ℓ) < 4.5? (This gives exponential decay)
3. Is ρ(M_ℓ) ≤ √5 ≈ 2.236? (This gives optimal √-cancellation)

If the state space is small enough (say, dimension ≤ 20), you could compute this exactly.

### Question 4: Verify Uniformity Over Initial States

For Rel-0C (the cylinder version), we need the same spectral bound to hold regardless of which state we start in.

- Does the spectral gap depend on the initial state?
- Or is it uniform (as required for cylinder equidistribution)?

### Question 5: If State Space Grows with k

If the minimal state space grows with k (bad case):
1. How fast does it grow?
2. Can you still get a uniform spectral gap despite growing dimension?
3. Is there a "coarse-graining" that captures enough to get SOME exponential decay (even if not optimal √5)?

## What We Know That Might Help

### The Multiplier Structure
m_k = 2^{T_k} mod 5^{k+1} satisfies:
- m_k ≡ 1 + s_k·5^k (mod 5^{k+1}) with s_k ≢ 0 (mod 5)
- m_k has order exactly 5

### Children in 5-adic Terms
For child index j ∈ {0,1,2,3,4}:
```
u_{k+1}(r+jT_k) ≡ u_{k+1}(r) · m_k^j (mod 5^{k+1})
```

If u = a + 5^k·t, then:
```
u · m_k^j ≡ a + 5^k·(t + j·a·s_k mod 5) (mod 5^{k+1})
```

So the bottom part a is **preserved**, only the top digit t changes!

### The 4-or-5 Criterion
- Exactly one child dies iff a(r) < 5^k/2
- The killed index j* satisfies: t(r) + j*·a(r)·s_k ≡ 0 (mod 5)

### Key Observation
Since a is preserved and only t changes, the "state" needed might be:
- a mod 5 (determines which j* equation holds)
- t mod 5 (the current top digit)
- Plus whatever determines whether a < 5^k/2

But a < 5^k/2 depends on the FULL value of a, not just a mod 5...

## The Critical Question

**Is survival at level k+1 determined by a BOUNDED amount of information from level k?**

If yes: We get a finite-dimensional transfer operator, and spectral gap is computable.

If no: The state space grows, and we need a different approach (perhaps induction on spectral properties).

## Desired Output

1. **Explicit state space X** - what it contains, its size (or growth rate)
2. **Transition structure** - how states evolve from level k to k+1
3. **Twisted matrices M_ℓ** - explicit form (or description) for ℓ ≢ 0 (mod 5)
4. **Spectral bound** - either:
   - Exact computation if dim(X) is small
   - A rigorous bound if dim(X) is moderate
   - An argument for why a uniform gap exists even if dim(X) grows
5. **Assessment of uniformity** - does the gap hold for all initial states?

## The Big Picture

If you can show:
- State space has bounded dimension d (independent of k)
- Twisted matrices M_ℓ have spectral radius ≤ ρ < 4.5 uniformly
- This holds for all initial states

Then:
- Character sum bound (CS) follows with C depending on d and ρ
- Killed-index uniformity follows
- Rel-0C follows
- Combined with Digit Squeeze and computation to k=27, the **86 Conjecture is proved**

This automaton construction is the final step.
