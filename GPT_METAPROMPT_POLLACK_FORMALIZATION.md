# Meta-Prompt: Staged Formalization of Pollack Bound

## Instructions for GPT 5.2 Pro Extended

You are the orchestrator for a multi-stage Lean 4 formalization project. Your task is to:

1. **Analyze** the theorem to be formalized
2. **Reflect** on your own capabilities and limitations
3. **Decompose** the formalization into stages (up to 20, but use only what's necessary)
4. **Generate** effective prompts for other GPT 5.2 instances to execute each stage

---

## The Theorem to Formalize

**Pollack Bound (as needed for ESC proof):**

```lean
axiom pollack_bound (p : ℕ) (hp : Nat.Prime p) (hp_mod : p % 4 = 1) (hp_ge : p ≥ 5) :
    ∃ q : ℕ, Nat.Prime q ∧ q % 4 = 3 ∧ q ≤ (p + 1) / 2
```

**In words:** For every prime p ≡ 1 (mod 4) with p ≥ 5, there exists a prime q ≡ 3 (mod 4) such that:
- q is a quadratic nonresidue mod p (this follows from q ≡ 3 mod 4 and quadratic reciprocity)
- q ≤ (p + 1) / 2

**Context:** This is used in the Erdős-Straus Conjecture proof. The bound q ≤ (p+1)/2 is much weaker than the full Pollack/Burgess bound (q ≪ p^0.152), which makes formalization tractable.

---

## Mathematical Background

The proof strategy likely involves:

1. **Quadratic Reciprocity**: For p ≡ 1 (mod 4), we have (q/p) = (p/q). So if q ≡ 3 (mod 4) and p is a QNR mod q, then q is a QNR mod p.

2. **Density of primes ≡ 3 (mod 4)**: By Dirichlet's theorem, primes ≡ 3 (mod 4) have density 1/2 among all primes.

3. **Existence argument**: Among primes q < (p+1)/2, at least one must satisfy the QNR condition, or else p would be a QR mod every such prime, which leads to contradiction via quadratic reciprocity constraints.

**Key Mathlib imports likely needed:**
- `Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity`
- `Mathlib.NumberTheory.DirichletCharacter.Bounds`
- `Mathlib.NumberTheory.ArithmeticFunction`
- `Mathlib.Data.Nat.Prime`

---

## Your Task

### Step 1: Capability Reflection

Before decomposing, reflect on:

1. **Your strengths**: What aspects of Lean 4 formalization are you good at? (e.g., setting up structures, writing tactic proofs, finding Mathlib lemmas)

2. **Your limitations**: Where do you typically struggle? (e.g., complex dependent types, obscure Mathlib API, long tactic chains that require interactive feedback)

3. **Ideal chunk size**: How much can a single GPT 5.2 instance reasonably handle in one prompt? (Consider: generating ~200 lines of Lean that compiles, vs. generating a full 1000-line file)

4. **Verification bottleneck**: Each stage's output must be verified by the Lean compiler before proceeding. How does this affect your decomposition?

### Step 2: Decomposition

Based on your reflection, decompose the formalization into N stages (1 ≤ N ≤ 20).

For each stage, specify:
- **Stage name**: Short descriptive title
- **Goal**: What theorem/definition is produced
- **Dependencies**: Which earlier stages must complete first
- **Estimated difficulty**: Easy / Medium / Hard
- **Verification checkpoint**: What should compile after this stage

Guidelines:
- **Don't over-decompose**: If a task is straightforward, don't split it artificially
- **Don't under-decompose**: If a task requires multiple non-trivial lemmas, split it
- **Parallelize where possible**: Independent stages can be run concurrently
- **Front-load infrastructure**: Definitions and basic lemmas before the main proof

### Step 3: Generate Prompts

For each stage, generate a complete prompt that another GPT 5.2 instance can execute. Each prompt must include:

1. **Context**: What has been completed in prior stages (provide code snippets or theorem statements)
2. **Task**: Precisely what to produce
3. **Constraints**:
   - Must use Lean 4 + Mathlib
   - Must compile without errors
   - Must not use `sorry` (or specify exactly which sorries are acceptable as placeholders)
4. **Output format**: Specify the exact structure expected
5. **Verification**: How the human will check correctness

---

## Output Format

Produce your response in this structure:

```markdown
## Capability Reflection

[Your honest assessment of GPT 5.2 capabilities for Lean formalization]

## Decomposition Summary

Total stages: N
Parallelizable groups: [list which stages can run concurrently]
Critical path: [the longest dependency chain]
Estimated total Lean lines: X

### Stage Dependency Graph

[ASCII diagram or description]

## Stage Details

### Stage 1: [Name]
- Goal: [theorem/definition]
- Dependencies: None
- Difficulty: [Easy/Medium/Hard]
- Checkpoint: [what compiles]

### Stage 2: [Name]
...

## Generated Prompts

### Prompt for Stage 1

[Complete prompt text]

---

### Prompt for Stage 2

[Complete prompt text]

---

[etc.]
```

---

## Constraints on Your Decomposition

1. **Minimum viable**: If you believe the entire formalization can be done in 1-3 stages, justify this and proceed
2. **Maximum useful**: Do not exceed 20 stages; if you think more are needed, identify which parts are out of scope
3. **Each stage must produce compilable code**: No stage should output code that requires future stages to compile
4. **Explicit Mathlib version**: Assume current Mathlib (as of January 2026)

---

## Reference: The Broader ESC Context

This `pollack_bound` axiom is part of a larger Erdős-Straus Conjecture formalization:

- **File**: `esc_complete_aristotle.lean` (0 sorries, 1 axiom currently)
- **The axiom to eliminate**: `pollack_bound`
- **Why it matters**: Formalizing this removes the last non-trivial axiom, giving a complete Lean proof of ESC

The formalized `pollack_bound` theorem should be a drop-in replacement for the axiom declaration.

---

## Begin

Reflect on your capabilities, then produce the staged decomposition and all prompts.
