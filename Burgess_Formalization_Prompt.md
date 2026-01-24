# Burgess Bound Formalization Prompt for GPT 5.2 Pro Extended

## Task Overview

Formalize the Burgess bound on least quadratic non-residues in Lean 4 with Mathlib. This is a proven mathematical result from 1962-1963 that we need for a complete formalization of the Erdős-Straus Conjecture.

## The Theorem to Formalize

**Burgess Bound (1962-1963)**: For any prime p and ε > 0, the least quadratic non-residue q modulo p satisfies:

```
q ≤ C(ε) · p^(1/(4√e) + ε)
```

where 1/(4√e) ≈ 0.1516. In practice, this gives q ≪ p^0.153 for large p.

## Why This Matters

This bound is needed to prove the Erdős-Straus Conjecture for primes p ≡ 1 (mod 4). We already have a fully verified Lean 4 proof for p ≡ 3 (mod 4). The Burgess bound completes the picture by ensuring we can always find a small enough quadratic non-residue to construct an ESC solution.

## Required Background Components

The Burgess bound proof requires formalizing these components:

### 1. Multiplicative Characters
- Definition of Dirichlet characters mod p
- Legendre symbol as a character
- Character orthogonality relations

### 2. Character Sums
- Gauss sums and their properties
- Jacobi sums
- The Pólya-Vinogradov inequality (a weaker prerequisite)

### 3. Weyl Sums and Exponential Sums
- Definition and basic properties
- Weyl differencing technique
- van der Corput's method

### 4. The Burgess Method
- The key combinatorial/analytic argument
- Shifting technique for character sums
- The amplification step

### 5. Final Assembly
- Combining all components
- The iteration argument
- Deriving the explicit bound

## Lean 4 Skeleton

```lean
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
import Mathlib.NumberTheory.DirichletCharacter.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.NumberTheory.SumFourSquares

/-!
# Burgess Bound on Least Quadratic Non-Residues

This file formalizes the Burgess bound (1962-1963), which states that
the least quadratic non-residue modulo a prime p is O(p^(1/(4√e) + ε)).

## Main Results

* `burgess_bound`: The main theorem giving an explicit upper bound
* `least_qnr_bound`: Existence of a small quadratic non-residue

## References

* D.A. Burgess, "On character sums and primitive roots",
  Proc. London Math. Soc. 12 (1962), 179-192
* D.A. Burgess, "The distribution of quadratic residues and non-residues",
  Mathematika 4 (1957), 106-112
-/

namespace Burgess

-- Part 1: Character sum infrastructure
section CharacterSums

/-- A multiplicative character sum over an interval -/
def char_sum (χ : DirichletCharacter ℂ p) (M N : ℕ) : ℂ :=
  ∑ n in Finset.Icc M (M + N - 1), χ n

/-- Pólya-Vinogradov inequality: |∑_{n≤N} χ(n)| ≤ √p log p -/
theorem polya_vinogradov (χ : DirichletCharacter ℂ p) (hχ : χ ≠ 1) (N : ℕ) :
    Complex.abs (∑ n in Finset.range N, χ n) ≤ Real.sqrt p * Real.log p := by
  sorry

end CharacterSums

-- Part 2: Weyl sum estimates
section WeylSums

/-- Weyl sum definition -/
def weyl_sum (α : ℝ) (N : ℕ) : ℂ :=
  ∑ n in Finset.range N, Complex.exp (2 * Real.pi * Complex.I * α * n)

/-- Weyl differencing bound -/
theorem weyl_differencing (α : ℝ) (N H : ℕ) (hH : H ≤ N) :
    Complex.abs (weyl_sum α N) ^ 2 ≤ N * (N / H + 1) +
      2 * ∑ h in Finset.Icc 1 H, (N - h) * ‖Real.cos (2 * Real.pi * α * h)‖ := by
  sorry

end WeylSums

-- Part 3: The Burgess amplification
section BurgessMethod

/-- The key Burgess estimate for character sums over short intervals -/
theorem burgess_character_sum_bound (χ : DirichletCharacter ℂ p) (hχ : χ ≠ 1)
    (M N r : ℕ) (hr : r ≥ 1) (hN : N ≥ p ^ (1 / (4 * r) : ℝ)) :
    Complex.abs (char_sum χ M N) ≤ C * N ^ (1 - 1 / (2 * r : ℝ)) * p ^ ((r + 1) / (4 * r^2) + ε) := by
  sorry

end BurgessMethod

-- Part 4: Main theorem
section MainTheorem

/-- The least quadratic non-residue modulo p -/
noncomputable def least_qnr (p : ℕ) [Fact (Nat.Prime p)] : ℕ :=
  Nat.find (exists_qnr p)

/-- Burgess bound: the least quadratic non-residue is ≤ p^(1/(4√e) + ε) -/
theorem burgess_bound (p : ℕ) [hp : Fact (Nat.Prime p)] (ε : ℝ) (hε : ε > 0) :
    (least_qnr p : ℝ) ≤ C(ε) * (p : ℝ) ^ (1 / (4 * Real.sqrt (Real.exp 1)) + ε) := by
  sorry

/-- Corollary: For sufficiently large p, least_qnr p ≤ p^0.16 -/
theorem least_qnr_bound (p : ℕ) [Fact (Nat.Prime p)] (hp_large : p ≥ 10^6) :
    (least_qnr p : ℝ) ≤ (p : ℝ) ^ (0.16 : ℝ) := by
  sorry

end MainTheorem

end Burgess
```

## Key Mathematical References

1. **Burgess's Original Papers**:
   - "On character sums and primitive roots" (1962)
   - "The distribution of quadratic residues and non-residues" (1957)

2. **Textbook Treatments**:
   - Iwaniec & Kowalski, "Analytic Number Theory", Chapter 12
   - Montgomery & Vaughan, "Multiplicative Number Theory I", Chapter 9
   - Davenport, "Multiplicative Number Theory", Chapter 23

3. **Survey Articles**:
   - Granville & Soundararajan, "Large character sums: pretentious characters and the Pólya-Vinogradov theorem"

---

## CRITICAL: MODULAR COMPLETION INSTRUCTIONS

**If you cannot complete the full formalization, follow these steps:**

### Step 1: Assess and Decompose
Break the task into these independent modules:
1. **Module A**: Character sum infrastructure (Dirichlet characters, basic sums)
2. **Module B**: Pólya-Vinogradov inequality
3. **Module C**: Weyl sums and exponential sum estimates
4. **Module D**: Burgess amplification method
5. **Module E**: Final theorem assembly

### Step 2: Complete What You Can
For each module:
- If you can fully formalize it, do so with no `sorry`
- If you can partially formalize it, complete the parts you can
- Mark each `sorry` with a comment explaining what's missing

### Step 3: Report Your Progress
At the end of your response, include a structured report:

```
## COMPLETION STATUS

### Module A: Character Sum Infrastructure
- Status: [COMPLETE / PARTIAL / NOT STARTED]
- Completed theorems: [list]
- Remaining sorries: [list with explanations]
- Estimated difficulty: [EASY / MEDIUM / HARD]
- Suggested next steps: [specific guidance]

### Module B: Pólya-Vinogradov
[same structure]

### Module C: Weyl Sums
[same structure]

### Module D: Burgess Method
[same structure]

### Module E: Final Assembly
[same structure]

## DEPENDENCIES
- Module B depends on: [A]
- Module C depends on: [A]
- Module D depends on: [A, B, C]
- Module E depends on: [A, B, C, D]

## RECOMMENDED NEXT AGENT TASKS
1. [Most important incomplete piece]
2. [Second priority]
3. [Third priority]
```

### Step 4: Make Each Module Self-Contained
Each module you produce should:
- Import only what it needs from Mathlib
- Have clear type signatures for all theorems
- Include `sorry` only where absolutely necessary
- Compile without errors (sorries are OK, type errors are not)

### Step 5: Prioritize Correctness Over Completeness
- A partial proof that compiles is more valuable than a complete proof with type errors
- If you're unsure about a step, use `sorry` and explain rather than guessing
- Test each definition by stating simple lemmas about it

---

## Verification Instructions

After generating code:
1. Ensure it compiles with `lake build`
2. Count remaining `sorry` statements
3. Verify each theorem statement matches the mathematical claim
4. Check that all imports are from Mathlib (no custom axioms)

## Output Format

Provide:
1. The complete Lean 4 code (or as much as you can complete)
2. The completion status report
3. Specific prompts for follow-up agents to handle incomplete modules

---

## Final Note

This is a challenging formalization that typically takes professional mathematicians months to complete manually. Any progress you make is valuable. Focus on getting the infrastructure right first (Modules A-C), as these are more tractable and provide the foundation for the harder analytical arguments in Module D.
