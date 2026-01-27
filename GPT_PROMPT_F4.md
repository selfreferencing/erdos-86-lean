# Lean 4 Task: Prove `discrepancy_from_char_bound` (counting discrepancy)

## Environment
- **Lean**: `leanprover/lean4:v4.24.0`
- **Mathlib**: commit `f897ebcf72cd16f89ab4577d0c826cd14afaafc7`

## Task

Prove that if the character sums over a Finset are bounded, then the count of elements with any given value deviates from the average by at most 4C/5. Return only the Lean 4 code.

## What to prove

```lean
import Mathlib

namespace Zeroless

open scoped BigOperators

noncomputable def ω : ℂ := Complex.exp (2 * Real.pi * Complex.I / 5)

/-- Assumed: character orthogonality -/
axiom twisted_sum_zero (ℓ : ZMod 5) (hℓ : ℓ ≠ 0) :
    (∑ j : Fin 5, ω ^ (ℓ.val * j.val)) = 0

/-- Discrepancy bound: if |∑_{x∈S} ω^{ℓ·g(x)}| ≤ C for all ℓ ≠ 0,
    then the count with g(x) = a deviates from |S|/5 by at most 4C/5. -/
theorem discrepancy_from_char_bound {α : Type*} [DecidableEq α]
    (S : Finset α) (g : α → Fin 5) (a : Fin 5)
    (C : ℝ) (hC : C ≥ 0)
    (hbound : ∀ ℓ : ZMod 5, ℓ ≠ 0 →
      Complex.abs (∑ x in S, (ω ^ (ℓ.val * (g x).val) : ℂ)) ≤ C) :
    |((S.filter (fun x => g x = a)).card : ℝ) - (S.card : ℝ) / 5| ≤ 4 * C / 5 := by
  sorry

end Zeroless
```

## Mathematical content

By Fourier inversion on the group Z/5Z:

|{x ∈ S : g(x) = a}| = (1/5) ∑_{ℓ=0}^{4} ∑_{x∈S} ω^{ℓ(g(x) - a)}

The ℓ = 0 term gives |S|/5. The other 4 terms each contribute at most C/5 (by the bound on character sums). Triangle inequality gives total deviation ≤ 4C/5.

More precisely:

|{x : g(x) = a}| - |S|/5 = (1/5) ∑_{ℓ≠0} ∑_{x∈S} ω^{ℓ(g(x) - a)}

Taking absolute values and using triangle inequality:

| |{x : g(x) = a}| - |S|/5 | ≤ (1/5) ∑_{ℓ≠0} |∑_{x∈S} ω^{ℓ(g(x) - a)}|

Now |∑_{x} ω^{ℓ(g(x)-a)}| = |ω^{-ℓa}| · |∑_{x} ω^{ℓ·g(x)}| = |∑_{x} ω^{ℓ·g(x)}| ≤ C.

So the bound is ≤ (1/5) × 4 × C = 4C/5.

## Step-by-step proof strategy

### Step 1: Establish the Fourier inversion identity

For f : Fin 5 → ℂ, the function f(a) can be recovered from its Fourier transform:
f(a) = (1/5) ∑_{ℓ : ZMod 5} f̂(ℓ) ω^{-ℓa}

where f̂(ℓ) = ∑_{j : Fin 5} f(j) ω^{ℓj}.

Applied to f(j) = |{x ∈ S : g(x) = j}| (the counting function):
- f̂(0) = ∑_j f(j) = |S|
- f̂(ℓ) = ∑_j |{x : g(x) = j}| ω^{ℓj} = ∑_{x∈S} ω^{ℓ·g(x)}

### Step 2: Subtract the ℓ=0 term

f(a) - |S|/5 = (1/5) ∑_{ℓ≠0} f̂(ℓ) ω^{-ℓa}

### Step 3: Take absolute values

|f(a) - |S|/5| ≤ (1/5) ∑_{ℓ≠0} |f̂(ℓ)| · |ω^{-ℓa}| = (1/5) ∑_{ℓ≠0} |f̂(ℓ)|

Since |ω^{-ℓa}| = 1 (ω is on the unit circle).

### Step 4: Apply the bound

Each |f̂(ℓ)| ≤ C, and there are 4 nonzero ℓ values, so:

|f(a) - |S|/5| ≤ (1/5) × 4C = 4C/5.

## Recommended proof approach

Rather than going through the full Fourier inversion (which is hard to formalize), prove this more directly:

```lean
theorem discrepancy_from_char_bound ... := by
  -- We avoid the full Fourier inversion machinery.
  -- Instead, observe that the character sum bound directly gives the discrepancy.
  --
  -- Key insight: Don't need the counting identity explicitly.
  -- Can use a direct argument with the triangle inequality.
  --
  -- Let N_a = |{x : g(x) = a}| and N = |S|.
  -- We want: |N_a - N/5| ≤ 4C/5.
  --
  -- Equivalently: |5 N_a - N| ≤ 4C.
  --
  -- Note: 5 N_a - N = 5 N_a - ∑_{b : Fin 5} N_b = ∑_{b ≠ a} (N_a - N_b)
  --
  -- Alternative: use the real part of the character sum.
  sorry
```

### Actually simplest approach (if we accept a weaker statement):

Since we're working over ℝ, we can state a simpler version:

```lean
  -- Trivial bound approach: there are 4 nonzero characters.
  -- Each contributes at most C to the deviation. Triangle inequality gives 4C.
  -- Dividing by 5 gives 4C/5.
  --
  -- But we need the Fourier identity to connect counts to character sums.
  -- This is the hard part.
```

### Most direct proof (avoiding full Fourier):

```lean
theorem discrepancy_from_char_bound ... := by
  -- Just use the bound |N_a - N/5| ≤ 4C/5 as a consequence of:
  -- 5·N_a = N + Re(∑_{ℓ≠0} (∑_x ω^{ℓ g(x)}) · ω^{-ℓa})  (Fourier inversion)
  -- |5·N_a - N| ≤ ∑_{ℓ≠0} |∑_x ω^{ℓ g(x)}| ≤ 4C
  -- |N_a - N/5| ≤ 4C/5
  sorry
```

## API pitfalls

1. **`Complex.abs`**: The absolute value on ℂ. It's `Complex.abs z = ‖z‖` (the norm).
2. **`Complex.abs_mul`**: `|z * w| = |z| * |w|`.
3. **`Complex.abs_pow`**: `|z^n| = |z|^n`.
4. **Unit circle**: `Complex.abs (Complex.exp (i * θ)) = 1` for real θ.
5. **`Finset.filter_card_add_filter_neg_card_eq_card`**: Useful for counting.
6. **Casting**: `((n : ℕ) : ℝ)` for real-valued counts.
7. **The main difficulty** is connecting the Finset counting to the character sum. The Fourier inversion identity is the key, and it requires careful handling of ℂ → ℝ conversion.
8. **`abs_sub_le_iff`** or **`abs_le`**: `|a - b| ≤ c ↔ b - c ≤ a ∧ a ≤ b + c`.

## Constraints
- Must compile with Lean 4.24.0 + specified Mathlib
- Return the complete theorem with proof
- This is the HARDEST micro-prompt. Consider breaking into sub-lemmas.
- If full proof is too complex, prove a weaker version with different hypotheses.
