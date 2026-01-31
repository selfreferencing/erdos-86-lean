# Erdős 86 Conjecture: Approach Index
**Date:** January 31, 2026
**Purpose:** Quick reference for all 55+ approaches explored

---

## The Problem

**Conjecture:** 2^86 is the last power of 2 with no zero digit in base 10.

**Status:** OPEN (verified computationally to n = 2.5 billion)

---

## Current Focus: Three Missing Lemmas

Any ONE of these would prove the conjecture:

| Lemma | Description | Status |
|-------|-------------|--------|
| **ML1** | Structured Shrinking-Target Property | Active research (see ML1_RESEARCH_PLAN.md) |
| **ML2** | Digit Pattern → Linear Form Transfer | Open |
| **ML3** | Effective Discrepancy with Exponential Targets | Open |

---

## Key Approaches by Category

### 🔴 BLOCKED APPROACHES (Don't work)

| Approach | File | Why it failed |
|----------|------|---------------|
| 52: Markov Carry Model | APPROACH52_*.md | Exp 86: Killing pairs ENHANCED, not suppressed |
| 33: 5-adic Lifting | APPROACH33_*.md | Exp 87: No hidden structure, exactly (9/10)^K |
| 22-24: Gap Refinement | APPROACH22-24_*.md | Circular - equivalent to the conjecture |

### 🟡 PROMISING BUT INCOMPLETE

| Approach | File | What's missing |
|----------|------|----------------|
| **11: Danger Cylinders** ⭐ | APPROACH11_*.md | Need to prove O(1) components hit |
| 43: Danger Cylinder Finiteness | APPROACH43_*.md | Formalizes Approach 11 |
| 54: Clean Architecture | APPROACH54_*.md | Best formulation of the problem |
| 55: Shrinking Targets | APPROACH55_*.md | Need extension to exponential unions |

### 🟢 ESTABLISHED RESULTS (Proven)

| Result | Where |
|--------|-------|
| Density 0 of zeroless powers | Standard equidistribution |
| Infinitely many zeros at each position | Visit frequency = μ(I_j) > 0 |
| Last K digits periodic with period 4×5^(K-1) | Euler's theorem |

---

## Approach 11: Danger Cylinders (IMPORTANT)

**Location:** `GPT_PROMPTS/APPROACH11_DANGER_CYLINDERS.md` (+ 11A, 11B)

### The Idea

Instead of showing the orbit NEVER enters Z_L, show:
- Only O(1) "danger cylinders" can capture orbit points
- Use Baker bounds on these finitely many targets
- Combine to get finiteness

### Key Insight

From Exp 30: Maximum 9 components of Z_L are ever hit by the orbit
- This is empirically true but NOT proven
- If proven → reduces infinite problem to finite check

### Why It Might Work

1. **Geometric constraint**: Orbit points have specific Diophantine properties
2. **Cylinder rigidity**: Most cylinders are "too far" from orbit
3. **Finite reduction**: Only need to analyze O(1) dangerous cases

### Current Gap

- Empirical evidence strong (Exp 30, Exp 42)
- No rigorous proof that only O(1) components matter
- Need: Diophantine argument excluding most cylinders

### Related Files

- `APPROACH11_DANGER_CYLINDERS.md` - Main exposition
- `APPROACH11A_DANGER_CYLINDERS_COMBINATORIAL.md` - Combinatorial version
- `APPROACH11B_DANGER_CYLINDERS_DIOPHANTINE.md` - Diophantine version
- `APPROACH28_DANGER_CYLINDER_THEOREM.md` - Attempted theorem
- `APPROACH43_DANGER_CYLINDER_FINITENESS.md` - Finiteness formalization
- `Zeroless/exp30_danger_cylinder_census.py` - Experimental evidence

---

## Approach 54: Clean Architecture (THE REFERENCE)

**Location:** `GPT_PROMPTS/APPROACH54_CLEAN_ARCHITECTURE.md` (+ 54A, 54B responses)

### What It Does

Provides the **canonical formulation** of the problem:

1. **The dynamical system**: θ = log₁₀(2), orbit f_n = {nθ}
2. **The target sets**: Z_L = zeroless set with 9^L components
3. **The obstruction**: Rotations have pure point spectrum (no mixing)
4. **The missing lemmas**: ML1, ML2, ML3 precisely stated

### Why It Matters

- This is the "correct" way to think about the problem
- All other approaches should be understood in this framework
- See `APPROACH54A_RESPONSE.md` and `APPROACH54B_RESPONSE.md` for GPT's analysis

---

## Approach 55: Shrinking Targets (ML1 CONTEXT)

**Location:** `GPT_PROMPTS/APPROACH55_SHRINKING_TARGETS.md` (+ 55A response)

### What It Does

Surveys existing shrinking-target theorems and identifies the gap:

- **Existing results**: Single intervals/balls with monotone radii
- **What we need**: Unions of 9^L intervals with algebraic endpoints
- **The gap**: No STP theorem handles exponentially complex targets

### Key Finding

> "Rotations have pure point spectrum. Therefore μ(A) → 0 does NOT imply orbit eventually avoids A."

---

## Full Approach List (1-55)

### Foundational (1-10)
| # | Name | Status |
|---|------|--------|
| 1 | Digit Independence | ❌ False (digits correlated) |
| 2 | Sieve Theory | ❌ Doesn't apply |
| 3 | Exponential Sums | ❌ Doesn't give finiteness |
| 4 | Diophantine Dynamics | 🟡 Framework only |
| 5 | Various Analyses | 🟡 Mixed |
| 6 | Coboundary | ❌ Doesn't work for rotations |
| 7 | Phase Cancellation | ❌ No decay |
| 8 | Diophantine (Strategy F) | 🟡 Partial |
| 9 | Transfer Operator | ❌ Pure point spectrum blocks |
| 10 | Extremal Functions | 🟡 Interesting but incomplete |

### Danger Cylinders (11, 18, 28, 43)
| # | Name | Status |
|---|------|--------|
| **11** | **Danger Cylinders** | ⭐ Most promising alternative to ML1 |
| 18 | Danger Cylinders (v2) | 🟡 Refinement |
| 28 | Danger Cylinder Theorem | 🟡 Attempted formalization |
| 43 | Danger Cylinder Finiteness | 🟡 Finiteness approach |

### Fourier/Analytic (12, 17, 36-41)
| # | Name | Status |
|---|------|--------|
| 12 | Parseval/QI | ❌ No decay |
| 17 | Multi-digit Collapse | ❌ Doesn't give finiteness |
| 36 | Target Lemma Decomposition | 🟡 Framework |
| 37 | Decorrelation | ❌ Rotations don't decorrelate |
| 39 | Spectral Gap | ❌ No gap for rotations |
| 40 | Direct Fourier Computation | ❌ No decay (verified in ML1 research) |
| 41 | Maynard Adaptation | ❌ Doesn't fit |

### Baker/Diophantine (13, 29, 45)
| # | Name | Status |
|---|------|--------|
| 13 | Direct Baker | ❌ Missing ML2 bridge |
| 29 | Baker-Davenport | ❌ Bounds too weak |
| 45 | Baker Prefixes | ❌ Heights too large |

### Carry/Markov (44, 47, 50, 52)
| # | Name | Status |
|---|------|--------|
| 44 | Carry Automaton | ❌ Exp 86: Enhancement not suppression |
| 47 | Zero Forcing Structure | ❌ Same issue |
| 50 | Protected 5 Mechanism | ❌ No special structure |
| 52 | Carry Markov Model | ❌ **DEAD** (Exp 86) |

### 5-adic/Structural (33, 46, 51)
| # | Name | Status |
|---|------|--------|
| 33 | 5-adic Lifting Tree | ❌ **DEAD** (Exp 87) |
| 46 | Why 86? | 🟡 Descriptive only |
| 51 | Prefix vs Full Zeroless | 🟡 Framework |

### Clean Architecture (54, 55)
| # | Name | Status |
|---|------|--------|
| **54** | **Clean Architecture** | ⭐ THE canonical formulation |
| **55** | **Shrinking Targets** | ⭐ ML1 context |

---

## Experiments Summary

| Exp # | What it tests | Result |
|-------|--------------|--------|
| 30 | Danger cylinder census | Max 9 components hit |
| 42 | Dangerous prefixes | Confirms O(1) pattern |
| 82-85 | Carry/Markov analysis | Various |
| **86** | **Killing pairs in zeroless** | **ENHANCED 1.25x** (kills Markov) |
| **87** | **5-adic structure** | **No special structure** (kills 5-adic) |

---

## Recommended Reading Order for RA

1. **STATUS_CHECKPOINT_2026_01_30.md** - Current state
2. **APPROACH54A_RESPONSE.md** - Clean architecture (THE formulation)
3. **APPROACH55A_RESPONSE.md** - Shrinking target survey
4. **ML1_RESEARCH_PLAN.md** - Current task
5. **APPROACH11_DANGER_CYLINDERS.md** - Alternative approach
6. **M3_86_CONJECTURE_SESSION.md** - Deep Gemini analysis (optional)

---

## Key Files by Topic

### The Problem
- `STATUS_CHECKPOINT_2026_01_30.md`
- `APPROACH54_CLEAN_ARCHITECTURE.md` + responses

### ML1 (Shrinking Targets)
- `ML1_RESEARCH_PLAN.md`
- `ML1_LITERATURE_FINDINGS.md`
- `APPROACH55_SHRINKING_TARGETS.md` + response
- `Zeroless/fourier_analysis_ZL.py`
- `continued_fraction_theta.py`

### Danger Cylinders (Alternative)
- `APPROACH11_DANGER_CYLINDERS.md` + A/B versions
- `APPROACH43_DANGER_CYLINDER_FINITENESS.md`
- `Zeroless/exp30_danger_cylinder_census.py`

### Dead Ends (Know what doesn't work)
- `APPROACH52_CARRY_MARKOV_MODEL.md` (Exp 86 killed it)
- `APPROACH33_5ADIC_LIFTING_TREE.md` (Exp 87 killed it)
- `Zeroless/exp86_zeroless_only_transitions.py`
- `Zeroless/exp87_5adic_structure.py`

---

*Last updated: January 31, 2026*
