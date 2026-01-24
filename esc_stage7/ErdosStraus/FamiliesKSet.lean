import Mathlib
import ErdosStraus.Basic
import ErdosStraus.CertificatesK10_10M
import ErdosStraus.Covering

namespace ErdosStraus

/-- Certificates in the embedded table that use a given k. -/
def certsWithK (k : ℕ) : List K10Cert := certListK10.filter (fun c => c.k = k)

/-- A number `p` is covered by the k-family iff there exists a certificate in the table with that k. -/
def CoveredByK (k p : ℕ) : Prop :=
  ∃ i : Fin certsK10.size, (certsK10[i]).p = p ∧ (certsK10[i]).k = k

/-- Any `CoveredByK` proof yields a `HasSolution`. -/
theorem coveredByK_hasSolution {k p : ℕ} (h : CoveredByK k p) : HasSolution p := by
  rcases h with ⟨i, hip, _hik⟩
  have hok : CertOk certsK10[i] := all_certsK10_ok i
  -- `hasSolution_of_cert` yields `HasSolution (certsK10[i]).p`, so rewrite via `hip`.
  simpa [hip] using (hasSolution_of_cert (c := certsK10[i]) hok)

/-- The ten k-values used for the Stage 6B cover. -/
def K10List : List ℕ := [5,7,9,11,14,17,19,23,26,29]

 /-- A disjunctive cover statement over the ten k-values (bounded: p ≤ 10^7). -/
theorem ten_k_cover_upto_10M :
    ∀ p : Fin (N10M + 1), (Nat.Prime p.val ∧ MordellHard840 p.val) →
      (CoveredByK 5 p.val) ∨ (CoveredByK 7 p.val) ∨ (CoveredByK 9 p.val) ∨ (CoveredByK 11 p.val) ∨ (CoveredByK 14 p.val) ∨
      (CoveredByK 17 p.val) ∨ (CoveredByK 19 p.val) ∨ (CoveredByK 23 p.val) ∨ (CoveredByK 26 p.val) ∨ (CoveredByK 29 p.val) := by
  native_decide

/-- Main theorem in disjunctive "family" form (bounded: p ≤ 10^7). -/
theorem erdos_straus_mordell_hard_upto_10M_via_families
    (p : ℕ) (hp : Nat.Prime p) (hMH : MordellHard840 p) (hp_le : p ≤ 10_000_000) :
    HasSolution p := by
  have hp_lt : p < N10M + 1 := Nat.lt_succ_of_le (by
    simpa [N10M] using hp_le)
  let pf : Fin (N10M + 1) := ⟨p, hp_lt⟩
  have hcover := ten_k_cover_upto_10M (p := pf) ⟨hp, hMH⟩
  -- dispatch each disjunct to a solution
  rcases hcover with h5 | hrest
  · exact coveredByK_hasSolution h5
  rcases hrest with h7 | hrest
  · exact coveredByK_hasSolution h7
  rcases hrest with h9 | hrest
  · exact coveredByK_hasSolution h9
  rcases hrest with h11 | hrest
  · exact coveredByK_hasSolution h11
  rcases hrest with h14 | hrest
  · exact coveredByK_hasSolution h14
  rcases hrest with h17 | hrest
  · exact coveredByK_hasSolution h17
  rcases hrest with h19 | hrest
  · exact coveredByK_hasSolution h19
  rcases hrest with h23 | hrest
  · exact coveredByK_hasSolution h23
  rcases hrest with h26 | h29
  · exact coveredByK_hasSolution h26
  exact coveredByK_hasSolution h29

end ErdosStraus
