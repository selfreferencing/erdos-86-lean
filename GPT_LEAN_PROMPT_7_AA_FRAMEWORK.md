# TASK: Write Lean 4 Code for A·A Framework and Saturation Lemma

## Context

For the Erdős-Straus conjecture, we reformulate the witness condition using divisor residue sets.

## The Framework

**Definition:** For x, m ∈ ℕ with gcd(x, m) = 1, define:
- A_m(x) = {d mod m : d | x} ⊆ (ℤ/mℤ)*
- The product set A·A = {a·b mod m : a, b ∈ A_m(x)}

**Key Lemma (GPT6):** Divisors of x² have residues exactly A·A.

**Witness Condition:** A Type II witness exists ⟺ -x mod m ∈ A·A

**Equivalently (GPT6's Lemma B):** Witness exists ⟺ A_m(x) ∩ (-A_m(x)) ≠ ∅
(i.e., there exist divisors a, b of x with a ≡ -b mod m)

## The Saturation Lemma

**Lemma:** If |A_m(x)| > |G|/2 where G = (ℤ/mℤ)*, then A·A = G.

**Consequence:** If x has enough distinct prime factors, the divisor residue set is large enough to guarantee A·A covers all of G, including -x.

## Your Task

Write Lean 4 code:

```lean
import Mathlib.Data.Finset.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.Subgroup.Basic
import Mathlib.Tactic

/-- The divisor residue set mod m -/
def divisorResidueSet (x m : ℕ) (hm : 0 < m) : Finset (ZMod m) :=
  (Nat.divisors x).image (fun d => (d : ZMod m))

/-- Product of two Finsets in a monoid -/
def finsetProd (A B : Finset (ZMod m)) : Finset (ZMod m) :=
  (A ×ˢ B).image (fun ⟨a, b⟩ => a * b)

/-- Divisors of x² have residues in A·A -/
lemma divisors_sq_residues (x m : ℕ) (hm : 0 < m) (hx : 0 < x) (hgcd : Nat.gcd x m = 1) :
    ∀ d, d ∣ x^2 → (d : ZMod m) ∈ finsetProd (divisorResidueSet x m hm) (divisorResidueSet x m hm) := by
  sorry

/-- Negation of a Finset -/
def finsetNeg (A : Finset (ZMod m)) : Finset (ZMod m) :=
  A.image (fun a => -a)

/-- Lemma B: Witness exists iff A ∩ (-A) is nonempty -/
lemma witness_iff_intersection_nonempty (x m : ℕ) (hm : 1 < m) (hx : 0 < x) (hgcd : Nat.gcd x m = 1) :
    (∃ d, d ∣ x^2 ∧ (d : ZMod m) = -(x : ZMod m)) ↔
    (divisorResidueSet x m (Nat.zero_lt_of_lt hm) ∩
     finsetNeg (divisorResidueSet x m (Nat.zero_lt_of_lt hm))).Nonempty := by
  sorry

/-- Saturation: if |A| > |G|/2, then A·A = G -/
lemma saturation_lemma (m : ℕ) (hm : 1 < m) (A : Finset (ZMod m))
    (hA : 2 * A.card > Fintype.card (ZMod m)) :
    finsetProd A A = Finset.univ := by
  sorry

/-- Corollary: Large divisor set implies witness exists -/
lemma witness_of_large_divisor_set (x m : ℕ) (hm : 1 < m) (hx : 0 < x) (hgcd : Nat.gcd x m = 1)
    (hA : 2 * (divisorResidueSet x m (Nat.zero_lt_of_lt hm)).card > m) :
    ∃ d, d ∣ x^2 ∧ d ≤ x ∧ (x + d) % m = 0 := by
  sorry
```

## Imports

```lean
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Prod
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.NumberTheory.Divisors
import Mathlib.Tactic
```

## Note

The saturation lemma is a standard result about product sets in finite abelian groups. You may need to use Cauchy-Davenport or a simpler pigeonhole argument.

## Output Format

Provide complete, compilable Lean 4 code.
