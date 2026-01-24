import Mathlib

import ErdosStraus.Basic
import ErdosStraus.Bradford
import ErdosStraus.Covering
-- import ErdosStraus.CertificatesK10_10M  -- Commented out to avoid stack overflow

import ErdosStraus.Families_k5
import ErdosStraus.Families_k7
import ErdosStraus.Families_k9
import ErdosStraus.Families_k11
import ErdosStraus.Families_k14
import ErdosStraus.Families_k17
import ErdosStraus.Families_k19
import ErdosStraus.Families_k23
import ErdosStraus.Families_k26
import ErdosStraus.Families_k29
import ErdosStraus.QRCommon
import ErdosStraus.TenKObstruction

/-!
# Stage 7 (scaffold): Unbounded covering for Mordell-hard primes

This file is the *Stage 7* upgrade of Stage 6B.

*Stage 6B* proved a **bounded** theorem for all Mordell-hard primes `p ≤ 10^7` by embedding
20,513 explicit certificates and discharging coverage by `native_decide`.

*Stage 7* aims to prove the **unbounded** theorem: every Mordell-hard prime (in the six Mordell
residue classes mod 840) has an Erdős–Straus decomposition.

The intended route (per the Stage 7 prompt) is a *finite residue-class covering system*:

1. Fix a master modulus `M` (divisible by all `m = 3 + 4k` values for `k ∈ K10`).
2. Partition Mordell-hard residues mod `M` into finitely many cases.
3. For each case, select `k ∈ K10` and prove the corresponding sufficiency lemma.

In this repository, the individual `k`-sufficiency predicates are defined in
`ErdosStraus/Families_k*.lean`. The key missing ingredient is the proof of the global
cover disjunction `ten_k_cover_complete`.

The file is structured so that, once `ten_k_cover_complete` is proved (by residue analysis),
the main unbounded theorem is a short case split.
-/

namespace ErdosStraus

/-- The master modulus requested in the Stage 7 prompt.

We take the lcm of 840 with the ten `m`-values

`{23,31,39,47,59,71,79,95,107,119}`.

Numerically this is:
`M = 4_185_369_236_605_294_920 = 2^3·3·5·7·13·17·19·23·31·47·59·71·79·107`.

Note: `M` is *astronomically* large; we do **not** enumerate `Fin M` in Lean.
Instead, the intended proof uses modular reasoning and `native_decide` only on small
sub-moduli.
-/
def M : ℕ := 4185369236605294920

/-- The six Mordell-hard residue classes modulo 840 as a `Finset`. -/
def MordellHardResidues840 : Finset ℕ := {1, 121, 169, 289, 361, 529}

/-- The ten k-values used for the Stage 6B/7 cover. -/
def K10 : Finset ℕ := {5, 7, 9, 11, 14, 17, 19, 23, 26, 29}

/-- A (non-computable) finset of all residues `r < M` that reduce to a Mordell-hard class mod 840.

This matches the *shape* requested by the Stage 7 prompt, but should not be evaluated.
-/
def MordellHardResiduesM : Finset ℕ :=
  (Finset.range M).filter (fun r => r % 840 ∈ MordellHardResidues840)

/-- Placeholder residue → `k` selector.

Stage 7 ultimately wants a *computable* selector derived from a covering proof.
At this stage we keep a total function returning a member of `K10` so that downstream
code has a concrete signature.

The real selector should be implemented as `coveringK` defined by a finite case split
on `r % m` / `r % (4m)` patterns.
-/
def coveringK (r : ℕ) (hr : r ∈ MordellHardResiduesM) : ℕ := 5

/-- Trivial membership proof for the placeholder `coveringK`.

Replace once `coveringK` becomes data-driven.
-/
theorem coveringK_in_K10 (r : ℕ) (hr : r ∈ MordellHardResiduesM) :
    coveringK r hr ∈ K10 := by
  -- `coveringK` is the constant `5`.
  simp [coveringK, K10]

/-!
## Global disjunction cover

The key theorem is: for any Mordell-hard prime `p`, at least one of the ten k-sufficiency
conditions holds.

Once this is in place, `erdos_straus_mordell_hard_unbounded` is a short `cases` proof.
-/

/-- The 10 sufficient conditions cover all Mordell-hard primes (KEY Stage 7 lemma).

Intended proof: residue analysis modulo a suitable master modulus and a finite amount of
computable checking.

This is *the* remaining gap between Stage 6B (bounded certificates) and a fully unbounded
covering proof.
-/
theorem ten_k_cover_complete (p : ℕ) (hp : Nat.Prime p) (hMH : MordellHard840 p) :
    k5Sufficient p ∨ k7Sufficient p ∨ k9Sufficient p ∨ k11Sufficient p ∨
    k14Sufficient p ∨ k17Sufficient p ∨ k19Sufficient p ∨ k23Sufficient p ∨
    k26Sufficient p ∨ k29Sufficient p := by
  classical
  -- Stage 8 reduction:
  -- If the whole 10-way disjunction failed, then each k-sufficient predicate is false.
  -- Since `kSufficient` is `d1Sufficient ∨ QRSufficient`, we would get `¬QRSufficient` for every k.
  -- By `not_QRSufficient_iff_obstruction` this yields the tenfold QR obstruction,
  -- contradicting `no_tenfold_obstruction`.
  by_contra h
  have hk5  : ¬ k5Sufficient p := by intro hk; exact h (Or.inl hk)
  have hk7  : ¬ k7Sufficient p := by intro hk; exact h (Or.inr (Or.inl hk))
  have hk9  : ¬ k9Sufficient p := by intro hk; exact h (Or.inr (Or.inr (Or.inl hk)))
  have hk11 : ¬ k11Sufficient p := by
    intro hk
    exact h (Or.inr (Or.inr (Or.inr (Or.inl hk))))
  have hk14 : ¬ k14Sufficient p := by
    intro hk
    exact h (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hk)))))
  have hk17 : ¬ k17Sufficient p := by
    intro hk
    exact h (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hk))))))
  have hk19 : ¬ k19Sufficient p := by
    intro hk
    exact h (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hk)))))))
  have hk23 : ¬ k23Sufficient p := by
    intro hk
    exact h (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hk))))))))
  have hk26 : ¬ k26Sufficient p := by
    intro hk
    exact h (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hk)))))))))
  have hk29 : ¬ k29Sufficient p := by
    intro hk
    exact h (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hk)))))))))

  -- Extract `¬QRSufficient` for each k from `¬(d1 ∨ QR)`.
  have hq5  : ¬ QRSufficient 5 p  := by intro hq; exact hk5  (Or.inr hq)
  have hq7  : ¬ QRSufficient 7 p  := by intro hq; exact hk7  (Or.inr hq)
  have hq9  : ¬ QRSufficient 9 p  := by intro hq; exact hk9  (Or.inr hq)
  have hq11 : ¬ QRSufficient 11 p := by intro hq; exact hk11 (Or.inr hq)
  have hq14 : ¬ QRSufficient 14 p := by intro hq; exact hk14 (Or.inr hq)
  have hq17 : ¬ QRSufficient 17 p := by intro hq; exact hk17 (Or.inr hq)
  have hq19 : ¬ QRSufficient 19 p := by intro hq; exact hk19 (Or.inr hq)
  have hq23 : ¬ QRSufficient 23 p := by intro hq; exact hk23 (Or.inr hq)
  have hq26 : ¬ QRSufficient 26 p := by intro hq; exact hk26 (Or.inr hq)
  have hq29 : ¬ QRSufficient 29 p := by intro hq; exact hk29 (Or.inr hq)

  -- Turn `¬QRSufficient` into the explicit obstruction conjunction for each k.
  have hob5  : PrimeFactorQR (mOfK 5) (xOfK p 5) ∧ TargetNQR (mOfK 5) (xOfK p 5) := by
    simpa using (not_QRSufficient_iff_obstruction (k := 5) (p := p)).1 hq5
  have hob7  : PrimeFactorQR (mOfK 7) (xOfK p 7) ∧ TargetNQR (mOfK 7) (xOfK p 7) := by
    simpa using (not_QRSufficient_iff_obstruction (k := 7) (p := p)).1 hq7
  have hob9  : PrimeFactorQR (mOfK 9) (xOfK p 9) ∧ TargetNQR (mOfK 9) (xOfK p 9) := by
    simpa using (not_QRSufficient_iff_obstruction (k := 9) (p := p)).1 hq9
  have hob11 : PrimeFactorQR (mOfK 11) (xOfK p 11) ∧ TargetNQR (mOfK 11) (xOfK p 11) := by
    simpa using (not_QRSufficient_iff_obstruction (k := 11) (p := p)).1 hq11
  have hob14 : PrimeFactorQR (mOfK 14) (xOfK p 14) ∧ TargetNQR (mOfK 14) (xOfK p 14) := by
    simpa using (not_QRSufficient_iff_obstruction (k := 14) (p := p)).1 hq14
  have hob17 : PrimeFactorQR (mOfK 17) (xOfK p 17) ∧ TargetNQR (mOfK 17) (xOfK p 17) := by
    simpa using (not_QRSufficient_iff_obstruction (k := 17) (p := p)).1 hq17
  have hob19 : PrimeFactorQR (mOfK 19) (xOfK p 19) ∧ TargetNQR (mOfK 19) (xOfK p 19) := by
    simpa using (not_QRSufficient_iff_obstruction (k := 19) (p := p)).1 hq19
  have hob23 : PrimeFactorQR (mOfK 23) (xOfK p 23) ∧ TargetNQR (mOfK 23) (xOfK p 23) := by
    simpa using (not_QRSufficient_iff_obstruction (k := 23) (p := p)).1 hq23
  have hob26 : PrimeFactorQR (mOfK 26) (xOfK p 26) ∧ TargetNQR (mOfK 26) (xOfK p 26) := by
    simpa using (not_QRSufficient_iff_obstruction (k := 26) (p := p)).1 hq26
  have hob29 : PrimeFactorQR (mOfK 29) (xOfK p 29) ∧ TargetNQR (mOfK 29) (xOfK p 29) := by
    simpa using (not_QRSufficient_iff_obstruction (k := 29) (p := p)).1 hq29

  -- Assemble the tenfold obstruction and contradict the target lemma.
  have hten : TenfoldObstruction p := by
    exact ⟨hob5, ⟨hob7, ⟨hob9, ⟨hob11, ⟨hob14, ⟨hob17, ⟨hob19, ⟨hob23, ⟨hob26, hob29⟩⟩⟩⟩⟩⟩⟩⟩⟩
  exact (no_tenfold_obstruction (p := p) hp hMH) hten

/-- Main Stage 7 theorem (unbounded): every Mordell-hard prime has an Erdős–Straus solution.

This theorem reduces immediately to `ten_k_cover_complete` plus the individual family lemmas.
-/
theorem erdos_straus_mordell_hard_unbounded
    (p : ℕ) (hp : Nat.Prime p) (hMH : MordellHard840 p) :
    HasSolution p := by
  have hcov := ten_k_cover_complete (p := p) hp hMH
  -- Dispatch to the appropriate `k` family.
  rcases hcov with
    h5 | h7 | h9 | h11 | h14 | h17 | h19 | h23 | h26 | h29
  · exact k5_gives_solution p hp hMH h5
  · exact k7_gives_solution p hp hMH h7
  · exact k9_gives_solution p hp hMH h9
  · exact k11_gives_solution p hp hMH h11
  · exact k14_gives_solution p hp hMH h14
  · exact k17_gives_solution p hp hMH h17
  · exact k19_gives_solution p hp hMH h19
  · exact k23_gives_solution p hp hMH h23
  · exact k26_gives_solution p hp hMH h26
  · exact k29_gives_solution p hp hMH h29

end ErdosStraus
