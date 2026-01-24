import Mathlib
import ErdosStraus.Basic
import ErdosStraus.CertificatesK10_10M

namespace ErdosStraus

def N10M : ℕ := 10_000_000

/-- The six Mordell-hard residue classes modulo 840 (Mordell reduction). -/
def MordellHard840 (p : ℕ) : Prop :=
  p % 840 = 1 ∨ p % 840 = 121 ∨ p % 840 = 169 ∨ p % 840 = 289 ∨ p % 840 = 361 ∨ p % 840 = 529

/-- Any explicit ES certificate yields `HasSolution`. -/
lemma hasSolution_of_ES {n x y z : ℕ}
    (hx : x > 0) (hy : y > 0) (hz : z > 0) (hES : ES n x y z) :
    HasSolution n := by
  exact ⟨x, y, z, hx, hy, hz, hES⟩

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
  -- Fetch the certified record at index `i`.
  have hok : CertOk certsK10[i] := all_certsK10_ok i
  -- Rewrite the target p using the stored equality.
  have : (certsK10[i]).p = p := hi
  -- Assemble the solution.
  -- Note: `hasSolution_of_cert` proves `HasSolution (certsK10[i]).p`, so rewrite.
  simpa [this] using (hasSolution_of_cert (c := certsK10[i]) hok)

/--
Completeness of the embedded certificate table (bounded: `p ≤ 10^7`).

This is a decidable finite statement because it quantifies over `Fin (N10M+1)`.
-/
theorem cover_complete_10M :
    ∀ p : Fin (N10M + 1), (Nat.Prime p.val ∧ MordellHard840 p.val) → Covered10M p.val := by
  native_decide

/--
Stage 6B (bounded formalization):

For every Mordell-hard prime `p ≤ 10^7`, the embedded table supplies an explicit
triple `(x,y,z)` with `4/p = 1/x + 1/y + 1/z` (encoded as `ES p x y z`).

The proof uses `native_decide` to locate a certificate in the finite table.
-/
theorem erdos_straus_mordell_hard_upto_10M
    (p : ℕ) (hp : Nat.Prime p) (hMH : MordellHard840 p) (hp_le : p ≤ 10_000_000) :
    HasSolution p := by
  -- Package `p` as an element of `Fin (N10M+1)` using the bound.
  have hp_lt : p < N10M + 1 := Nat.lt_succ_of_le (by
    -- `hp_le : p ≤ 10_000_000`
    simpa [N10M] using hp_le)
  let pf : Fin (N10M + 1) := ⟨p, hp_lt⟩
  have hcov : Covered10M p := by
    have := cover_complete_10M (p := pf) ⟨hp, hMH⟩
    simpa using this
  exact covered10M_hasSolution (p := p) hcov

end ErdosStraus
