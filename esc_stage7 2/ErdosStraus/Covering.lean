import Mathlib
import ErdosStraus.Basic
-- import ErdosStraus.CertificatesK10_10M  -- Commented out to avoid stack overflow

namespace ErdosStraus

def N10M : ℕ := 10000000

/-- The six Mordell-hard residue classes modulo 840 (Mordell reduction). -/
def MordellHard840 (p : ℕ) : Prop :=
  p % 840 = 1 ∨ p % 840 = 121 ∨ p % 840 = 169 ∨ p % 840 = 289 ∨ p % 840 = 361 ∨ p % 840 = 529

/-- Any explicit ES certificate yields `HasSolution`. -/
lemma hasSolution_of_ES {n x y z : ℕ}
    (hx : x > 0) (hy : y > 0) (hz : z > 0) (hES : ES n x y z) :
    HasSolution n := by
  exact ⟨x, y, z, hx, hy, hz, hES⟩

/-!
## Certificate-based bounded verification (commented out due to stack overflow)

The following lemmas require `import ErdosStraus.CertificatesK10_10M` which causes
stack overflow due to the large certificate array (20,513 entries).

The unbounded theorem `erdos_straus_mordell_hard_unbounded` in `CoveringUnbounded.lean`
does NOT require these bounded verification lemmas.
-/

/-
/-- Turn a stored `K10Cert` into a `HasSolution` certificate. -/
lemma hasSolution_of_cert (c : K10Cert) (h : CertOk c) : HasSolution c.p := by
  rcases h with ⟨hk, hx, hy, hz, hES⟩
  exact hasSolution_of_ES (n := c.p) (x := c.x) (y := c.y) (z := c.z) hx hy hz hES

/-- The list view of the embedded certificates. -/
def certListK10 : List K10Cert := certsK10.toList

/-- Covered by the embedded K10 certificate list. -/
def Covered10M (p : ℕ) : Prop := ∃ i : Fin certsK10.size, (certsK10[i]).p = p

/-- If `p` is covered by the list, then `HasSolution p`. -/
theorem covered10M_hasSolution {p : ℕ} (hcov : Covered10M p) : HasSolution p := by
  rcases hcov with ⟨i, hi⟩
  have hok : CertOk certsK10[i] := all_certsK10_ok i
  have : (certsK10[i]).p = p := hi
  simpa [this] using (hasSolution_of_cert (c := certsK10[i]) hok)

/-- Completeness of the embedded certificate table (bounded: `p ≤ 10^7`). -/
theorem cover_complete_10M :
    ∀ p : Fin (N10M + 1), (Nat.Prime p.val ∧ MordellHard840 p.val) → Covered10M p.val := by
  native_decide

/-- Stage 6B: For every Mordell-hard prime `p ≤ 10^7`, ESC holds. -/
theorem erdos_straus_mordell_hard_upto_10M
    (p : ℕ) (hp : Nat.Prime p) (hMH : MordellHard840 p) (hp_le : p ≤ 10_000_000) :
    HasSolution p := by
  have hp_lt : p < N10M + 1 := Nat.lt_succ_of_le (by simpa [N10M] using hp_le)
  let pf : Fin (N10M + 1) := ⟨p, hp_lt⟩
  have hcov : Covered10M p := by
    have := cover_complete_10M (p := pf) ⟨hp, hMH⟩
    simpa using this
  exact covered10M_hasSolution (p := p) hcov
-/

end ErdosStraus
