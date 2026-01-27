/-
  Erdős Covering Systems Problem

  Statement: Does there exist a covering system with all moduli distinct
  and all greater than any given k?

  Answer: NO (Hough, 2015). The minimum modulus of any distinct covering
  system is at most 10^16.

  Reference: Hough, "Solution of the minimum modulus problem for covering
  systems" (Annals of Mathematics, 2015).

  M3 Application:
  | Phase | AI System | Task |
  |-------|-----------|------|
  | Macro | Claude | Proof architecture from Hough (2015), key lemmas |
  | Micro | GPT | LCM bounds, density arguments, Lovász Local Lemma |
  | Multiple | Aristotle | Sorry-filling for technical lemmas |

  This problem fits M3 because:
  1. CRT-Based: Same machinery as ESC decision tree
  2. Modular Arithmetic: Residue class analysis
  3. Finite Obstruction: Proof shows covering systems cannot avoid small moduli
  4. Computational Component: Explicit bounds amenable to verification
-/

import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Nat.Prime.Basic

/-!
# Covering Systems and the Minimum Modulus Problem

## Main definitions

* `Congruence` - A congruence class a (mod m)
* `CoveringSystem` - A finite set of congruences covering all integers
* `CoveringSystem.IsDistinct` - All moduli are pairwise distinct
* `CoveringSystem.minModulus` - The smallest modulus in the system

## Main results

* `hough_minimum_modulus_bound` - Hough's Theorem: min modulus ≤ 10^16

## Proof Strategy (Hough 2015)

The proof uses the probabilistic method with the Lovász Local Lemma:

1. **Sieving by prime thresholds**: Filter moduli by P_i thresholds
2. **Good fibers**: Apply LLL to find "regular" uncovered subsets
3. **Measure reweighting**: Control variation via bias statistics
4. **Explicit computation**: Verify constraints allow infinite iteration

The key insight is that within numbers with few prime factors, most pairs
are coprime, making the Local Lemma applicable despite dependencies.
-/

namespace Erdos

/-- A congruence class: integers ≡ a (mod m) -/
structure Congruence where
  residue : ℤ
  modulus : ℕ
  modulus_pos : 0 < modulus
deriving DecidableEq

/-- An integer n satisfies congruence c if n ≡ c.residue (mod c.modulus) -/
def Congruence.satisfies (c : Congruence) (n : ℤ) : Prop :=
  n % c.modulus = c.residue % c.modulus

instance (c : Congruence) (n : ℤ) : Decidable (c.satisfies n) :=
  inferInstanceAs (Decidable (_ = _))

/-- A covering system is a finite set of congruences such that every
    integer satisfies at least one of them -/
structure CoveringSystem where
  congruences : Finset Congruence
  nonempty : congruences.Nonempty
  covers : ∀ n : ℤ, ∃ c ∈ congruences, c.satisfies n

/-- A covering system is distinct if all moduli are pairwise different -/
def CoveringSystem.IsDistinct (C : CoveringSystem) : Prop :=
  ∀ c₁ c₂ : Congruence, c₁ ∈ C.congruences → c₂ ∈ C.congruences →
    c₁.modulus = c₂.modulus → c₁ = c₂

/-- The minimum modulus of a covering system -/
noncomputable def CoveringSystem.minModulus (C : CoveringSystem) : ℕ :=
  C.congruences.image (·.modulus) |>.min' (by
    simp only [Finset.image_nonempty]
    exact C.nonempty)

/-- The maximum modulus of a covering system -/
noncomputable def CoveringSystem.maxModulus (C : CoveringSystem) : ℕ :=
  C.congruences.image (·.modulus) |>.max' (by
    simp only [Finset.image_nonempty]
    exact C.nonempty)

/-!
## Key Lemmas (Axiomatized)

The full proof of Hough's theorem requires:
1. The Lovász Local Lemma (probabilistic combinatorics)
2. Careful density estimates for integers avoiding congruences
3. Explicit numerical verification of convergence conditions

We axiomatize the key density lemma that drives the proof.
-/

/-- The density of integers in [1, N] not covered by a set of congruences.
    Returns a rational for computability. -/
noncomputable def uncoveredCount (congs : Finset Congruence) (N : ℕ) : ℕ :=
  (Finset.filter (fun n : Fin N => ∀ c ∈ congs, ¬c.satisfies n) Finset.univ).card

/-- Hough's key lemma: When the minimum modulus is large enough,
    there exist uncovered integers in any interval [1, N] for some N.

    This is the technical heart of the proof, using the Lovász Local Lemma
    with careful analysis of prime factor distributions.

    The proof proceeds by:
    1. Showing that sieving by congruences has limited dependency
    2. Applying LLL to guarantee positive density survives
    3. Computing explicit bounds showing this works when min > 10^16 -/
axiom hough_density_lemma
  (C : CoveringSystem) (hC : C.IsDistinct) (hmin : 10^16 < C.minModulus) :
  ∃ N : ℕ, 0 < N ∧ 0 < uncoveredCount C.congruences N

/-!
## Main Theorem
-/

/-- **Hough's Theorem** (2015): The minimum modulus of any distinct
    covering system is at most 10^16.

    This resolves Erdős's 1950 question in the negative: there is no
    distinct covering system with arbitrarily large minimum modulus.

    The bound was later improved to 616,000 by Balister et al. (2022). -/
theorem hough_minimum_modulus_bound (C : CoveringSystem) (hC : C.IsDistinct) :
    C.minModulus ≤ 10^16 := by
  by_contra h
  push_neg at h
  -- If min modulus > 10^16, then by hough_density_lemma there exist
  -- uncovered integers, contradicting that C is a covering system.
  obtain ⟨N, hN_pos, hcount⟩ := hough_density_lemma C hC h
  -- Positive count means some integer is uncovered
  rw [uncoveredCount] at hcount
  rw [Finset.card_pos] at hcount
  obtain ⟨n, hn⟩ := hcount
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hn
  -- This contradicts that C covers all integers
  obtain ⟨c, hc_mem, hc_sat⟩ := C.covers n
  exact hn c hc_mem hc_sat

/-- Corollary: There is no distinct covering system with all moduli > 10^16 -/
theorem no_large_modulus_covering_system :
    ¬∃ C : CoveringSystem, C.IsDistinct ∧ 10^16 < C.minModulus := by
  push_neg
  intro C hC
  exact hough_minimum_modulus_bound C hC

/-- The improved bound from Balister-Bollobás-Morris-Sahasrabudhe-Tiba (2022):
    The minimum modulus is at most 616,000.

    We state this as an axiom since the proof uses different techniques
    (the "distortion method"). -/
axiom bbmst_minimum_modulus_bound (C : CoveringSystem) (hC : C.IsDistinct) :
    C.minModulus ≤ 616000

end Erdos
