import ErdosStraus.Basic
import ErdosStraus.CoveringData
import Mathlib.Tactic

namespace ErdosStraus

/-- The 10-k cover set discovered empirically (covers all Mordell-hard primes ≤ 10^7). -/
def kList : List ℕ := [5, 7, 9, 11, 14, 17, 19, 23, 26, 29]

/-- As a `Finset` for membership checks. -/
def kSet : Finset ℕ := kList.toFinset

/-- Basic sanity predicate: the stored triple (x,y,z) is a valid Erdős–Straus certificate for `p`. -/
def CertOK (c : Cert) : Prop :=
  0 < c.x ∧ 0 < c.y ∧ 0 < c.z ∧ EscEq c.p c.x c.y c.z

/-- The stored `k` is in the 10-k cover set. -/
def CertKInSet (c : Cert) : Prop := c.k ∈ kSet

/-- The stored `m` matches the identity `m = 3 + 4k`. -/
def CertMMatches (c : Cert) : Prop := c.m = 3 + 4 * c.k

/-- A helper: extract membership facts from a `List.Forall`. -/
theorem forall_of_forall_mem {α : Type} {P : α → Prop} {l : List α} :
    List.Forall P l → ∀ a, a ∈ l → P a := by
  intro h a ha
  induction h with
  | nil =>
      cases ha
  | @cons a0 l0 hP hForall ih =>
      -- membership in a cons list
      simp at ha
      cases ha with
      | inl hEq =>
          simpa [hEq] using hP
      | inr hMem =>
          exact ih a hMem

/-- All stored certificates satisfy the Erdős–Straus identity and positivity. -/
theorem certs_all_ok : List.Forall CertOK certs := by
  native_decide

/-- All stored certificates use a `k` from the 10-k cover set. -/
theorem certs_all_k_in_set : List.Forall CertKInSet certs := by
  native_decide

/-- All stored certificates satisfy `m = 3 + 4k`. -/
theorem certs_all_m_matches : List.Forall CertMMatches certs := by
  native_decide

/-- A direct certificate implies the conjecture instance for that `p`. -/
theorem cert_ok_implies_conjecture (c : Cert) (h : CertOK c) : Conjecture c.p := by
  rcases h with ⟨hx, hy, hz, heq⟩
  refine ⟨c.x, c.y, c.z, hx, hy, hz, heq⟩

/-- Every `p` appearing in the dataset satisfies `Conjecture p`. -/
theorem conjecture_for_all_dataset_primes : List.Forall (fun c : Cert => Conjecture c.p) certs := by
  refine (certs_all_ok.imp ?_)
  intro c hc
  exact cert_ok_implies_conjecture c hc

/-- Convenience corollary: for any certificate `c` in the dataset, `Conjecture c.p` holds. -/
theorem conjecture_of_mem_certs (c : Cert) (hc : c ∈ certs) : Conjecture c.p := by
  have hall : List.Forall (fun c : Cert => Conjecture c.p) certs := conjecture_for_all_dataset_primes
  exact forall_of_forall_mem hall c hc



/-- If `p` appears as the `p`-field of some dataset certificate, then `Conjecture p` holds. -/
theorem conjecture_of_exists_dataset_cert (p : ℕ)
    (h : ∃ c ∈ certs, c.p = p) : Conjecture p := by
  rcases h with ⟨c, hc_mem, rfl⟩
  exact conjecture_of_mem_certs c hc_mem

/-
NOTE (Stage 6B): The dataset `certs` is known externally to contain *all* Mordell-hard primes p ≤ 10^7.
This file provides a fully checkable Lean proof that each listed prime satisfies Erdős–Straus,
and that each such prime is covered by one of the 10 k-values.

Upgrading this to an *unbounded* proof for all Mordell-hard primes requires replacing the finite
dataset with parametric families, or proving a residue-class cover theorem that implies the
existence of a Bradford witness divisor `d` for some k in `kSet`.
-/

end ErdosStraus
