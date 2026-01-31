# Prompt 47: Research Decision Memo

## Context

From 45A and 45B, we identified three strategic "bets" for making progress on unconditional effective ES:

### Bet 1: Relax ED2 Requirements
- If ED2 works with squarefree q (not just prime q)
- Then effective Burgess + sieve could bypass Siegel entirely
- This is potentially the "easiest" path if it works

### Bet 2: Linnik-style Dichotomy
- For the specific characters χ_p and χ₄χ_p
- Either no exceptional zero (use explicit zero-free region)
- Or exceptional zero exists (use bias + DH repulsion)
- Goal: Get effective bound for the PRODUCT character

### Bet 3: Alternative Parameterizations
- Find ES representations that don't require the q-lemma
- Completely different reductions that avoid the bottleneck
- May exist in the literature but be obscure

## Request: Decision Memo

Please write a **research decision memo** that:

### Part 1: Probability Assessment
For each of the three bets:
- What is the probability of success (rough estimate)?
- What is the effort required if it works?
- What is the effort required to determine if it works?
- What would failure look like?

### Part 2: Dependencies
- Are any bets prerequisites for others?
- Can they be pursued in parallel?
- Are there synergies between approaches?

### Part 3: Literature Gaps
- What has NOT been tried that seems worth trying?
- Are there relevant papers we should read but haven't?
- Are there experts we should consult?

### Part 4: Recommendation
Based on the analysis:
- Which bet should be pursued FIRST?
- What is the minimal viable experiment for that bet?
- What would a positive result look like?
- What would make us abandon that bet and move to the next?

### Part 5: Timeline
If we allocate 40 hours to this exploration:
- How should that time be divided?
- What are the checkpoints?
- When do we declare victory or pivot?

## Constraints

We have:
- Already completed GRH → ES (effective, conditional)
- Pollack → ES (unconditional, ineffective)
- Constant-chase ruled out (p₀ > 10^{1000})
- Lean 4 formalization infrastructure

We want:
- Unconditional effective ES (if possible)
- Or clear understanding of why it's not currently achievable
- Ideally publishable regardless of outcome

## Output Format

Structure the memo as a professional decision document with:
1. Executive Summary (2-3 sentences)
2. Analysis by Bet
3. Recommendation
4. Next Actions
