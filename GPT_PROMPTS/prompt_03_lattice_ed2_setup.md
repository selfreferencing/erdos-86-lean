# GPT Prompt 3: ED2 Lattice Setup (Lemma 9.22)

## Task

Formalize the setup that connects the ED2 kernel lattice to Type II solutions.
The kernel lattice L = {(u,v) : u*b' + v*c' ≡ 0 (mod g)} already exists in WindowLattice.lean.
Your job is to show that when we set up the parameters correctly, lattice points
satisfying additional constraints give ED2 solutions.

## Context: What's Already Proven

In WindowLattice.lean, we have:

```lean
/-- L = {(u,v) : u*b' + v*c' ≡ 0 (mod g)} -/
def ED2KernelLattice (g : ℕ) (b' c' : ℤ) : AddSubgroup (ℤ × ℤ)

/-- α = gcd(g, b'+c') -/
def ed2Alpha (g : ℕ) (b' c' : ℤ) : ℕ := Nat.gcd g (Int.natAbs (b' + c'))

/-- d' = g/α -/
def ed2Step (g : ℕ) (b' c' : ℤ) : ℕ := g / ed2Alpha g b' c'

/-- v1 = (c', -b') ∈ L -/
theorem v1_mem (g : ℕ) (b' c' : ℤ) : (c', -b') ∈ ED2KernelLattice g b' c'

/-- v2 = (d', d') ∈ L when d' = g/α -/
theorem v2_mem (g : ℕ) (hg : 0 < g) (b' c' : ℤ) :
    ((ed2Step g b' c' : ℤ), (ed2Step g b' c' : ℤ)) ∈ ED2KernelLattice g b' c'

/-- Any g×g rectangle contains a lattice point -/
theorem ed2_window_lemma
    {g : ℕ} (hg : 0 < g) {b' c' : ℤ}
    (_hb : Nat.Coprime g (Int.natAbs b')) (hc : Nat.Coprime g (Int.natAbs c')) :
    ∀ {x0 y0 : ℤ} {H W : ℕ},
      g ≤ H → g ≤ W →
      ∃ p : ℤ × ℤ, p ∈ ED2KernelLattice g b' c' ∧ p ∈ rect x0 y0 H W
```

## Mathematical Background

From Dyachenko's paper (Section 9.4 and Lemma 9.22):

The ED2 system looks for (b, c, δ) satisfying:
  (4b - 1)(4c - 1) = 4Pδ + 1

When factored through the α, d', b', c' parameterization:
  - A = α * b' * c' (the key value in the A-window)
  - δ = α * d'^2
  - b = α * d' * b'
  - c = α * d' * c'
  - m = 4A - P (the "step modulus")

The kernel lattice L is set up with:
  - g = m = 4A - P (so that the divisibility condition d' * m | (b' + c') is automatic)
  - b', c' coprime to g

## What You Need to Prove

Given:
  - A prime P ≡ 1 (mod 4)
  - A value A in the window [(P+3)/4, (3P-3)/4]
  - A factorization A = α * M where α is the "denominator parameter" and M = b' * c'

Show that:
1. If we find (u, v) ∈ L with u = m*d' for some d' > 0 and u² - v² = 4M,
   then b' = (u+v)/2 and c' = (u-v)/2 satisfy the ED2 identity.

2. The A-window bounds ensure the rectangle [1, g+1) × [-g/2, g/2) contains
   such a point.

## Lean Statements to Prove

```lean
import Mathlib.Tactic
import ErdosStraus.ED2.WindowLattice

namespace ED2

/-- Setup: from A and α, define the lattice parameters -/
structure ED2Setup (P : ℕ) (A : ℕ) (α : ℕ) where
  halpha_pos : 0 < α
  hA_pos : 0 < A
  halpha_dvd : α ∣ A
  hm_pos : P < 4 * A  -- ensures m = 4A - P > 0
  M : ℕ := A / α      -- M = b' * c' will be the product
  m : ℕ := 4 * A - P  -- the step modulus

/-- Given a lattice point (u, v) with the right properties, extract a valid A and divisor d.

The key insight from D.16: if m | u and u² - v² = 4M with u ≡ v (mod 2),
then b' = (u+v)/2 and c' = (u-v)/2 are positive integers with b'*c' = M.

From this we get:
  - d' = u/m
  - The ED2 parameters (α, d', b', c')
  - A divisor d = b' of A that satisfies the congruence
-/
theorem lattice_point_gives_divisor
    {P A α : ℕ} (setup : ED2Setup P A α)
    {u v : ℤ}
    (hu_pos : 0 < u)
    (hdiv : (setup.m : ℤ) ∣ u)
    (hparity : u % 2 = v % 2)
    (hhyper : u ^ 2 - v ^ 2 = 4 * (setup.M : ℤ))
    (hu_mem : (u, v) ∈ ED2KernelLattice setup.m (extractB' u v) (extractC' u v))
    : let b' := extractB' u v  -- (u + v) / 2
      let c' := extractC' u v  -- (u - v) / 2
      let d' := u / (setup.m : ℤ)
      0 < b' ∧ 0 < c' ∧ 0 < d' ∧
      b' * c' = setup.M ∧
      b' + c' = setup.m * d' := by
  sorry

/-- The lattice contains a point satisfying the constraints when A is in the window.

This uses ed2_window_lemma: any g×g box contains a lattice point.
The rectangle [1, m+1) × [-(m-1)/2, (m+1)/2) is an m×m box.
If it contains a point (u, v) with u² - v² = 4M, we're done.

The key is showing that the hyperbola u² - v² = 4M intersects this rectangle.
When A is in [(P+3)/4, (3P-3)/4], we have m = 4A - P ∈ [3, 2P-3],
and M = A/α. The hyperbola passes through (u, v) = (b'+c', b'-c')
for any factorization M = b'*c'. We need at least one such point in the box.
-/
theorem exists_lattice_point_in_window
    (P : ℕ) (hP_prime : Nat.Prime P) (hP4 : P % 4 = 1)
    (A : ℕ) (hA_lo : (P + 3) / 4 ≤ A) (hA_hi : A ≤ (3 * P - 3) / 4)
    (α : ℕ) (hα_pos : 0 < α) (hα_dvd : α ∣ A)
    : let m := 4 * A - P
      let M := A / α
      ∃ u v : ℤ, 0 < u ∧
        (m : ℤ) ∣ u ∧
        u % 2 = v % 2 ∧
        u ^ 2 - v ^ 2 = 4 * (M : ℤ) := by
  sorry

/-- Combined: from A in window, get a divisor d satisfying the modular condition.

This is the key connection to exists_good_A_and_divisor in ExistsGoodDivisor.lean.
The signature there needs:
  ∃ A d : ℕ, window_bounds ∧ d ∣ A^2 ∧ (4A - P) ∣ (d + A)

From the lattice point approach:
  - b' and c' give us d = A * b' / c' (when c' | A*b') or similar
  - The divisibility (4A - P) | (d + A) comes from the sum condition b' + c' = m*d'
-/
theorem lattice_gives_good_divisor
    (P : ℕ) (hP_prime : Nat.Prime P) (hP4 : P % 4 = 1)
    (A : ℕ) (hA_lo : (P + 3) / 4 ≤ A) (hA_hi : A ≤ (3 * P - 3) / 4)
    : ∃ d : ℕ, 0 < d ∧ d ∣ A ^ 2 ∧ (4 * A - P) ∣ (d + A) := by
  sorry

end ED2
```

## Proof Strategy

**For lattice_point_gives_divisor:**
1. From hparity, (u + v) and (u - v) are both even, so b' and c' are integers.
2. b' * c' = (u+v)(u-v)/4 = (u² - v²)/4 = M by hhyper.
3. b' + c' = u, and from hdiv, m | u, so b' + c' ≡ 0 (mod m).
4. d' = u/m is a positive integer since m | u and u > 0.
5. Positivity of b', c' requires sign analysis.

**For exists_lattice_point_in_window:**
1. The ed2_window_lemma gives us SOME point in the box.
2. We need to show the hyperbola u² - v² = 4M intersects the box.
3. This is where the A-window bounds matter: they ensure M is small enough
   relative to m that the hyperbola passes through the lattice's reach.

**For lattice_gives_good_divisor:**
1. Get the lattice point (u, v) from exists_lattice_point_in_window.
2. Extract b', c', d' from the lattice point.
3. Construct the divisor d from these parameters.
4. Verify d ∣ A² and (4A-P) ∣ (d + A).

## Key Insight

The hard part is showing the hyperbola u² - v² = 4M passes through the lattice
within the box. The paper handles this by:
- The diagonal period d' = g/α means the lattice has "diagonal slices"
- The window lemma ensures we hit SOME diagonal slice
- The hyperbola condition picks out the right point on that slice

For formalizing: you may need to restrict to specific α values (like α = 1)
to make the geometry simpler, then generalize.

## Hints

1. Work in ℤ to avoid subtraction issues.
2. The structure ED2Setup encapsulates the parameter relationships.
3. `extractB'` and `extractC'` are defined in prompt_02_D16_bridge.md.
4. You may need to import the results from prompt_01 and prompt_02.
5. The hyperbola u² - v² = 4M is the key constraint beyond the lattice.

## Deliverable

Provide complete Lean 4 proofs for all three theorems, or identify which
additional lemmas are needed as intermediate steps.
