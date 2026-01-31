# Experiment 23 Analysis: 5-adic Tree Structure

## Key Findings

### 1. The tree is NOT a tree past level 3

The most striking finding: from level 4 onward, every admissible node has either 0 or 1 admissible children. The branching histogram at m=20:

| Level | 0-child | 1-child | 2-child | 3+ child | Avg children |
|-------|---------|---------|---------|----------|-------------|
| 2 | 0 | 0 | 0 | 4 | 4.50 |
| 3 | 0 | 0 | 1 | 17 | 3.22 |
| 4 | 4 | 54 | 0 | 0 | 0.93 |
| 5-20 | varies | varies | 0 | 0 | 0.67-1.00 |

From level 4 onward, each admissible node either dies (0 children) or has exactly 1 surviving child. The "tree" is actually a collection of single threads that terminate stochastically.

### 2. The termination rate drives finiteness

Since each node has at most 1 child, the number of surviving threads at level j is monotonically non-increasing. The number of threads decreases from ~L at level 3 to ~L*0.9^j at level j (since each thread dies with probability ~0.1 per level, matching the digit-zero probability).

For the small-index branch, the threads thin from ~L at level 3 to 0 by level m. At m=27, for the first time, ALL threads die before reaching level m.

### 3. The survival rate pattern

The overall survival rate (admissible / occupied classes) drops steadily:

| Level | m=20 rate | m=30 rate |
|-------|-----------|-----------|
| 1 | 1.00 | 1.00 |
| 2 | 0.90 | 0.90 |
| 5 | 0.69 | 0.60 |
| 10 | 0.36 | 0.35 |
| 15 | 0.12 | 0.12 |
| 20 | 0.09 | 0.09 |
| 25 | - | 0.05 |
| 30 | - | 0.03 |

At m=25, 13/25 levels have rate < 0.2. At m=30, 18/30 levels do.

### 4. Small-index vs generic branching: NO difference

Part E shows the small-index branching rate is essentially identical to the generic rate (~0.9 per level). The small-index threads die at the same rate as generic ones.

This means: the finiteness mechanism is NOT that small indices have worse branching. The mechanism is purely combinatorial: there are only L ~ 3.3m threads, each dying with probability ~0.1 per level, so after m levels, the expected number of survivors is L * 0.9^m ~ 3.3m * 0.9^m -> 0.

### 5. The role of early levels

Level 2 creates 18 threads from 20 occupied classes (kills 2).
Level 3 is the big narrowing: from ~L threads to ~L * (branching/5) threads.
But the branching at level 3 is 2-3 per node, not 4.5, so there's already a deficit.

After level 3, it's a simple death process: each thread dies independently with prob ~0.1 per level.

## Connection to Finiteness

The 5-adic tree picture gives a clean combinatorial model for finiteness:
- Start with L ~ 3.3m threads at level 3
- Each thread dies with probability p ~ 0.1 at each subsequent level
- After m-3 more levels, expected survivors = L * 0.9^{m-3} ~ 3.3m * 0.9^m
- This goes to 0 exponentially, so eventually all threads die

The difficulty in making this rigorous: the deaths are NOT independent across threads (they share the same orbit structure). Two threads at the same level have correlated fates because they correspond to nearby orbit indices.

## Implication for GPT 2B's Criterion

GPT 2B asked: does survival rate < 1/5 at a positive fraction of levels? YES, increasingly so as m grows. At m=30, 60% of levels have rate < 1/5.

But the criterion isn't quite right as stated. The survival rate being < 1/5 doesn't directly force exponential growth of the minimal survivor, because the 0-or-1 branching means each thread independently either lives or dies. The relevant quantity is the per-thread death probability at each level, which is consistently ~0.1 (matching generic behavior).

The real finiteness mechanism is simpler than GPT 2B expected: it's just the birthday problem / coupon collector in disguise. With L ~ m threads and m levels of ~10% death rate, the probability of ANY thread surviving all m levels is ~ 1 - (1 - 0.9^m)^L ~ L * 0.9^m -> 0.
