# Prompt 51: Survey of Effective Results in ES

## Context

We've established:
- GRH → ES (effective, conditional)
- Pollack → ES (unconditional, ineffective)
- Constant-chase fails (p₀ > 10^{1000})

Before pursuing new directions, we should survey what effective results ALREADY exist for ES.

## Questions

### Q1: What is verified computationally?

- What is the largest n for which ES is verified?
- Who did this verification and when?
- What methods were used?
- Is the verification code available?

### Q2: What infinite families are known effectively?

For which residue classes mod m is ES known effectively?
- n ≡ 0 (mod 2): Yes, trivially
- n ≡ 0 (mod 3): Yes, trivially
- n ≡ 2 (mod 4): Yes (Mordell)
- n ≡ 3 (mod 4): Yes (Mordell)
- What about mod 8, mod 12, mod 24?

For each: What is the effective construction?

### Q3: Density Results

What is known about the density of n for which ES is effective?
- Is it known that ES holds for density 1 subset effectively?
- Are there effective bounds on the exceptional set?
- What sieves apply?

### Q4: Congruence Conditions

For primes p ≡ 1 (mod 4):
- Are there additional congruence conditions that give effective ES?
- E.g., is ES effective for p ≡ 1 (mod 24)?
- What about p ≡ 1 (mod 120)?

### Q5: Conditional Results

Besides GRH, what other hypotheses give effective ES?
- Elliott-Halberstam?
- Various zero-free region assumptions?
- Density hypotheses?

For each: What is the effective bound?

### Q6: Near Misses

Are there results that are "almost" effective ES?
- E.g., effective except for O(1) exceptions?
- Effective except for a finite explicit list?
- Effective with an explicit but impractically large threshold?

### Q7: The Gap

What is the gap between:
- Largest n verified computationally
- Smallest n where asymptotic results apply (effectively)

Is this gap shrinking over time?

## Desired Output

1. Table of known effective ES results
2. For each: the method, the bound, the reference
3. Assessment of the "frontier" of effective results
4. Where improvement is most likely possible
