# Codex Recursive Decomposition Prompt for the 86 Conjecture

## Instructions for Codex

You are working on the **86 Conjecture**: 2^86 is the largest power of 2 whose decimal expansion contains no digit 0. Your goal is to make rigorous mathematical progress toward proving this conjecture, or to identify exactly why it cannot be proved with current methods.

You operate under a **branching recursive decomposition** protocol. Follow this protocol exactly.

---

## The Recursive Decomposition Protocol

### Step 1: Attempt
Given a problem P, first try to solve it directly. "Solve" means: write Python code that either
(a) produces a rigorous proof or proof sketch with computational verification, or
(b) produces a definitive negative result ("this approach cannot work because X, verified computationally").

Run your code. Check whether it succeeds.

### Step 2: Evaluate
If your attempt SUCCEEDS (code runs, output is correct, claim is verified): mark P as SOLVED. Record the solution in `results.json`. Stop recursing on P.

If your attempt FAILS (code errors, output contradicts claim, or you cannot formulate a working approach within a reasonable effort): proceed to Step 3.

### Step 3: Decompose
Split P into two sub-problems P_left and P_right such that:
- Solving BOTH P_left and P_right would solve P
- Each sub-problem is strictly simpler than P (involves fewer variables, smaller parameter ranges, or a more specific structure)
- Each sub-problem is precisely stated as a mathematical claim that can be computationally tested

Record the decomposition in `tree.json`:
```json
{
  "problem": "P description",
  "status": "decomposed",
  "left": {"problem": "P_left description", "status": "pending"},
  "right": {"problem": "P_right description", "status": "pending"}
}
```

### Step 4: Recurse
Apply Steps 1-3 to P_left. Then apply Steps 1-3 to P_right.

If either sub-problem fails decomposition (cannot be meaningfully split further), mark it as BLOCKED and record why.

### Step 5: Backtrack
If a decomposition leads to a dead end (one branch is BLOCKED), try an ALTERNATIVE decomposition of the parent problem. You get up to 3 alternative decompositions per problem before marking the parent as BLOCKED.

---

## The Root Problem

**P_root**: Prove that for all n > 86, the decimal expansion of 2^n contains at least one digit 0.

### What is already known (DO NOT re-derive these, use them as given facts):

1. **Computationally verified**: No zeroless 2^n exists for n = 87..10000.
2. **The 4.5^k barrier**: Any proof strategy that works digit-by-digit from right to left hits a growth factor of 5 * (9/10) = 4.5 > 1 per digit level. This means survivor counts grow as ~4 * 4.5^(k-1), not decay. This barrier is fundamental and confirmed from 5 independent angles.
3. **CRT invisibility**: The zeroless constraint is invisible to mod 2^k alone (density 1.0 for all k) and mod 5^k alone (density 1.0 for all k). It lives ONLY in the joint mod 10^k structure, where density = (9/10)^(k-1).
4. **Fourier obstruction**: The additive Fourier spectrum of the zeroless set mod 10^k has max coefficient 1/9 (mod 5^k), not decaying with k.
5. **S-unit/Subspace Theorem dead**: Zeroless is positive-entropy (9^k possibilities), cannot be compressed to O(1) S-unit terms. Baker/Matveev also dead (truncation quotient has uncontrolled height).
6. **Suffix depth exceeds 91**: n=7931 has 115 consecutive nonzero trailing digits. So you cannot prove the conjecture by bounding suffix depth alone.
7. **Key structural fact**: 2^n mod 10^k is periodic in n with period T_k = 4 * 5^(k-1). Among T_k orbit elements, exactly 4 * 4.5^(k-1) are zeroless-compatible (density (9/10)^(k-1)).
8. **Heuristic**: For k-digit 2^n, about 3.32 values of n produce k digits. Expected zeroless count per level: 3.32 * (9/10)^(k-1). Sum over k >= 91: ~0.0025. So the expected total is already < 1.

### Suggested initial decompositions (you may choose differently):

**Decomposition A** (by digit region):
- P_left: "The trailing half of digits of 2^n (last k/2 positions) contains a 0 for all n > N_0."
- P_right: "The leading half of digits of 2^n (first k/2 positions) contains a 0 for all n > N_0."
- (Either one suffices; you don't need both.)

**Decomposition B** (by method):
- P_left: "Convert the heuristic expected-count argument (item 8) into a rigorous upper bound using equidistribution + discrepancy bounds."
- P_right: "Verify computationally that no zeroless 2^n exists for n up to the rigorous bound from P_left."

**Decomposition C** (by digit position):
- P_left: "For n > N_0, digit position floor(k/2) of 2^n equals 0 with probability bounded away from 0."
- P_right: "The events 'digit j is nonzero' for j = 1,...,k are sufficiently independent that their joint probability decays exponentially."

---

## Output Format

Maintain these files throughout your session:

### `tree.json`
The full decomposition tree with status of every node (SOLVED, PENDING, BLOCKED, DECOMPOSED).

### `results.json`
For each SOLVED node: the mathematical claim, the Python code that verifies it, and the output.

### `blocked.json`
For each BLOCKED node: the precise reason it's blocked, what was tried, and what would unblock it.

### `summary.md`
A running human-readable summary of:
- Current tree depth and breadth
- Which branches are alive vs dead
- The most promising open sub-problem
- Any surprising findings

---

## Computational Tools Available

You have Python with these libraries: `mpmath` (arbitrary precision), `sympy` (symbolic math), `numpy`, `scipy`. You can compute:
- 2^n to arbitrary precision for any n
- Digit extractions, carry analysis, modular arithmetic
- Fourier transforms, eigenvalue computations
- Discrepancy calculations, statistical tests

---

## Rules

1. Every claim must be accompanied by computational evidence (Python code + output).
2. Never assert a mathematical statement without either proving it or flagging it as a conjecture.
3. When decomposing, explain WHY solving both sub-problems would solve the parent.
4. Track your tree depth. If you reach depth 6 without progress, stop and write a summary of what you've learned.
5. Prioritize FALSIFIABLE sub-problems: ones where a Python computation can definitively say YES or NO.
6. Do not re-derive known dead ends (items 1-8 above). Build on them.
7. If you discover that a sub-problem is equivalent to a known open problem in mathematics, record this and mark it BLOCKED with the reference.

---

## Success Criteria

- **Full success**: A complete proof (possibly computer-assisted) that E = {n : 2^n is zeroless} is finite.
- **Partial success**: A new lemma or reduction that is rigorously proved and was not previously known, narrowing the gap.
- **Informative failure**: A clear map of exactly which sub-problems are tractable vs blocked, with precise statements of what remains open, producing a "proof landscape" more detailed than what currently exists.

Even an informative failure is valuable. The decomposition tree itself is a contribution.
