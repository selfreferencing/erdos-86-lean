/-
  Erdős-Ginzburg-Ziv Theorem (1961)

  Statement: Among any 2n-1 integers, some n have sum divisible by n.

  Status: PROVED (1961). Formalized in Mathlib.

  M3 Application: Minimal - demonstrates Mathlib fluency and sets up
  the narrative for the harder problems in the portfolio.

  This file imports the Mathlib formalization directly.
-/

import Mathlib.Combinatorics.Additive.ErdosGinzburgZiv

/-!
# Erdős-Ginzburg-Ziv Theorem

The theorem states that among any 2n-1 integers, there exist n integers
whose sum is divisible by n.

## Main results from Mathlib

* `ZMod.erdos_ginzburg_ziv` - the theorem for sequences into ZMod n
* `Int.erdos_ginzburg_ziv` - the theorem for sequences into ℤ
* `Int.erdos_ginzburg_ziv_multiset` - the theorem for multisets of ℤ
* `ZMod.erdos_ginzburg_ziv_multiset` - the theorem for multisets of ZMod n

## M3 Portfolio Context

This is Problem 4 in our Erdős portfolio, serving as a warm-up to
demonstrate we can work with formalized mathematics before tackling
the open problems (ESC, Ternary Digits, 86 Conjecture).
-/

namespace ErdosPortfolio

variable {ι : Type*} {n : ℕ} {s : Finset ι}

/-- Erdős-Ginzburg-Ziv for ℤ: Among any 2n-1 integers indexed by s,
    some n have sum divisible by n.

    This is a direct re-export of `Int.erdos_ginzburg_ziv` from Mathlib. -/
theorem erdos_ginzburg_ziv_int (a : ι → ℤ) (hs : 2 * n - 1 ≤ s.card) :
    ∃ t ⊆ s, t.card = n ∧ (n : ℤ) ∣ ∑ i ∈ t, a i :=
  Int.erdos_ginzburg_ziv a hs

/-- Erdős-Ginzburg-Ziv for ZMod n: Among any 2n-1 elements of ZMod n,
    some n elements sum to zero.

    This is a direct re-export of `ZMod.erdos_ginzburg_ziv` from Mathlib. -/
theorem erdos_ginzburg_ziv_zmod (a : ι → ZMod n) (hs : 2 * n - 1 ≤ s.card) :
    ∃ t ⊆ s, t.card = n ∧ ∑ i ∈ t, a i = 0 :=
  ZMod.erdos_ginzburg_ziv a hs

/-- Erdős-Ginzburg-Ziv for multisets of ℤ: Among any 2n-1 integers,
    some n have sum divisible by n.

    This version works directly with multisets, which is often more
    convenient for stating the theorem in its classical form.

    This is a direct re-export of `Int.erdos_ginzburg_ziv_multiset` from Mathlib. -/
theorem erdos_ginzburg_ziv_multiset (s : Multiset ℤ) (hs : 2 * n - 1 ≤ Multiset.card s) :
    ∃ t ≤ s, Multiset.card t = n ∧ (n : ℤ) ∣ t.sum :=
  Int.erdos_ginzburg_ziv_multiset s hs

end ErdosPortfolio
