# Prompt 63C: Quadruple Data for the Other 5 Hard Classes

## Context

From prompts 63A/63B, we have complete (p, x, k, m, e) data for the first 100 primes p ≡ 1 (mod 840).

The key structural finding was:
- x₀ = (p+3)/4 = 210n + 1 for p = 840n + 1
- Each k forces x into a fixed residue class mod 210
- The "built-in small prime" effect (k=2 → 3|x, k=4 → 5|x, k=6 → 7|x) explains why k ≤ 7 suffices

## The Other 5 Hard Classes

The 6 hard classes mod 840 are: p ≡ 1, 121, 169, 289, 361, 529 (mod 840)

These are the quadratic residues mod 840 (squares of units).

**Question:** Does the same k ≤ 7 pattern hold for the other 5 classes? What's the x₀ structure for each?

## Request

Please provide the (p, x, k, m, e) quadruple data for the **first 50 primes** in each of the other 5 hard classes:

### Class 1: p ≡ 121 (mod 840)

First 50 primes, format:
```
p | x | k | m | e | verification
```

Also compute: What is x₀ = ⌈p/4⌉ in terms of p = 840n + 121?

### Class 2: p ≡ 169 (mod 840)

First 50 primes, same format.

Also compute: What is x₀ in terms of p = 840n + 169?

### Class 3: p ≡ 289 (mod 840)

First 50 primes, same format.

Also compute: What is x₀ in terms of p = 840n + 289?

### Class 4: p ≡ 361 (mod 840)

First 50 primes, same format.

Also compute: What is x₀ in terms of p = 840n + 361?

### Class 5: p ≡ 529 (mod 840)

First 50 primes, same format.

Also compute: What is x₀ in terms of p = 840n + 529?

## Analysis Questions

For each class:

1. **k-distribution:** What's the frequency of k = 0,1,2,3,4,5,6,7?

2. **Max k observed:** Is k ≤ 7 always sufficient, or do some classes need larger k?

3. **x₀ structure:** What's the mod 210 residue of x₀ for this class? Does it have built-in small factors?

4. **Comparison to p ≡ 1:** Are the patterns similar or different?

## Summary Table

After the data, please provide a summary:

| Class (mod 840) | x₀ (mod 210) | Built-in factors | Max k observed | k=0 success rate |
|-----------------|--------------|------------------|----------------|------------------|
| 1 | 1 | none | 7 | 45% |
| 121 | ? | ? | ? | ? |
| 169 | ? | ? | ? | ? |
| 289 | ? | ? | ? | ? |
| 361 | ? | ? | ? | ? |
| 529 | ? | ? | ? | ? |

## Goal

Determine whether the Route C1 proof strategy (k ≤ 7 suffices due to mod 210 structure) applies uniformly across all 6 hard classes, or if different classes need different treatment.
