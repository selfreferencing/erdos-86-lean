# GPT Prompt 7: Hyperbola-Lattice Intersection Lemma Decomposition

## Context

We have proven infrastructure for the ED2 lattice approach:
- `ED2KernelLattice g b' c'` - the kernel lattice L = {(u,v) : g | u*b' + v*c'}
- `ed2_window_lemma` - any g×g rectangle contains a lattice point
- `lattice_point_gives_divisor` - if (u,v) satisfies certain conditions, we get ED2 parameters

The **missing piece**: showing that the hyperbola u² - v² = 4M intersects the lattice
within a suitable rectangle.

## The Gap

The window lemma gives us: ∃ (u,v) ∈ L with u ∈ [x₀, x₀+g) and v ∈ [y₀, y₀+g).

But we need: ∃ (u,v) ∈ L with u > 0, g | u, u ≡ v (mod 2), AND u² - v² = 4M.

The hyperbola constraint is the hard part. We need to show the hyperbola passes through
the lattice within the rectangle.

## Your Task

Break down the hyperbola-lattice intersection problem into the smallest possible
sub-lemmas. For each sub-lemma:
1. State it precisely in Lean
2. Classify it as: EASY (routine), MEDIUM (requires thought), or HARD (deep)
3. Explain the proof strategy or why it's hard

## Mathematical Background

The hyperbola u² - v² = 4M factors as (u-v)(u+v) = 4M.
Setting b' = (u+v)/2 and c' = (u-v)/2, we get b'*c' = M.

So the hyperbola corresponds to factorizations of M = A/α.

The lattice L has:
- Index g (the number of cosets of L in ℤ²)
- Diagonal period d' = g/α
- Basis vectors v₁ = (c', -b') and v₂ = (d', d')

## Questions to Answer

1. **What are the necessary conditions for the hyperbola to intersect L within a rectangle?**
   - Is it about the size of the rectangle vs. the "density" of the hyperbola?
   - Does the shape of L (determined by b', c', g) matter?

2. **Can we reduce to a counting argument?**
   - Count hyperbola points in the rectangle
   - Count lattice points in the rectangle
   - Show their intersection is non-empty

3. **Is there a direct construction?**
   - Given M = b'*c', can we directly construct (u,v) = (b'+c', b'-c') and show it's in L?
   - What conditions on b', c' ensure (b'+c', b'-c') ∈ L?

4. **What's the role of coprimality?**
   - The window lemma requires gcd(g, b') = gcd(g, c') = 1
   - How does this interact with the hyperbola constraint?

## Template for Sub-Lemmas

```lean
import Mathlib.Tactic
import ErdosStraus.ED2.WindowLattice

namespace ED2

/-! ## Sub-lemma 1: [Name]
    Difficulty: [EASY/MEDIUM/HARD]
    Strategy: [Brief description]
-/

/-- [Description] -/
lemma sublemma1 ... := by
  sorry

/-! ## Sub-lemma 2: [Name]
    Difficulty: [EASY/MEDIUM/HARD]
    Strategy: [Brief description]
-/

/-- [Description] -/
lemma sublemma2 ... := by
  sorry

-- Continue for all identified sub-lemmas...

/-! ## Main Theorem Assembly -/

/-- The hyperbola u² - v² = 4M intersects the kernel lattice L within any
    sufficiently large rectangle centered appropriately.

    This combines all the sub-lemmas above.
-/
theorem hyperbola_lattice_intersection
    {g : ℕ} (hg : 0 < g) {b' c' : ℤ}
    (hb : Nat.Coprime g (Int.natAbs b')) (hc : Nat.Coprime g (Int.natAbs c'))
    (M : ℕ) (hM : (b' * c' : ℤ) = M)
    -- Additional hypotheses as needed
    : ∃ u v : ℤ,
        (u, v) ∈ ED2KernelLattice g b' c' ∧
        0 < u ∧
        (g : ℤ) ∣ u ∧
        u % 2 = v % 2 ∧
        u ^ 2 - v ^ 2 = 4 * M := by
  sorry

end ED2
```

## Key Insight from the Paper

Dyachenko's proof (Lemma 9.22 + Proposition 9.25) works because:
1. The lattice L is defined so that (b'+c', b'-c') IS in L when b'*c' = M
2. The diagonal period d' = g/α means we can "translate" along the diagonal
3. The window lemma then finds SOME representative in any g×g box

The issue: our formalization defined L differently. We defined:
```lean
L = {(u,v) : g | u*b' + v*c'}
```

But the paper's lattice is more directly tied to the ED2 solution structure.

## Alternative Approach: Redefine the Lattice

Perhaps we should define L directly as the solution set:
```lean
def ED2SolutionLattice (M m : ℕ) : Set (ℤ × ℤ) :=
  {p | m ∣ p.1 ∧ p.1 % 2 = p.2 % 2 ∧ p.1 ^ 2 - p.2 ^ 2 = 4 * M}
```

Then show this is a lattice coset, and apply density arguments.

## Deliverable

Provide:
1. A list of 3-8 sub-lemmas that together would prove `hyperbola_lattice_intersection`
2. For each sub-lemma: precise Lean statement, difficulty rating, proof strategy
3. Identification of which sub-lemma is the "crux" that makes the whole thing hard
4. Optionally: proof of the easier sub-lemmas
