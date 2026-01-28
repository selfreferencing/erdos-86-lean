/-
  ErdosStraus/ED2/Certificate.lean

  Computational verification that ED2 parameters exist for all primes
  p ≡ 1 (mod 4) below the certificate bound.

  Three-case search:
  1. p ≡ 5 (mod 8): α = (p+3)/8, d' = 1, b' = 1, c' = 2
  2. p ≡ 1 (mod 8), p ≡ 2 (mod 3): α = 1, d' = 1, b' = (p+1)/3, c' = 1
  3. p ≡ 1 (mod 24): parametric search over (α, r, s) with
     M = 4αsr - 1, M | (p + 4αs²), yielding b' = s, c' = mr - s, d' = r

  Key identity: δ = 4αb'c' - p = (p + 4αs²)/M = m,
  and b' + c' = mr = δ·d', so the sum condition is automatic.

  Architecture:
  - `findED2` is a Bool search function (three cases)
  - `findED2_sound` extracts the witness from the Bool result
  - `checkAllED2` iterates over all p < bound
  - `ed2_certificate_check` uses native_decide to verify checkAllED2
  - `ed2_params_below_certBound` is the final theorem

  ## Sorry status
  None (all proofs are by native_decide or structural).
-/

import Mathlib.Tactic

namespace ED2

/-- Upper bound for the certificate-based verification.
    All primes p ≡ 1 (mod 4) with p < certBound are verified computationally. -/
def certBound : ℕ := 1000001

/-- The ED2 existence predicate: there exist parameters satisfying the
    Dyachenko conditions (Theorem 9.21 / Condition III). -/
def HasED2Params (p : ℕ) : Prop :=
  ∃ α d' b' c' : ℕ,
    0 < α ∧ 0 < d' ∧ 0 < b' ∧ 0 < c' ∧
    p < 4 * α * b' * c' ∧
    b' + c' = (4 * α * b' * c' - p) * d'

/-- The search function for ED2 parameters. Cases 1 and 2 use Prop-level
    if/else (for split_ifs). Case 3 puts all conditions into a single
    decide call to avoid split_ifs issues with nested let/if. -/
def findED2 (p : ℕ) : Bool :=
  -- Case 1: p ≡ 5 (mod 8)
  if p % 8 = 5 then
    let α := (p + 3) / 8
    decide (0 < α ∧ p < 4 * α * 1 * 2 ∧ 1 + 2 = (4 * α * 1 * 2 - p) * 1)
  -- Case 2: p ≡ 1 (mod 8), p ≡ 2 (mod 3)
  else if p % 3 = 2 then
    let b' := (p + 1) / 3
    decide (0 < b' ∧ p < 4 * 1 * b' * 1 ∧ b' + 1 = (4 * 1 * b' * 1 - p) * 1)
  -- Case 3: p ≡ 1 (mod 24), parametric search
  else
    (List.range 5).any fun ai =>
      (List.range 50).any fun si =>
        (List.range 50).any fun ri =>
          let α := ai + 1
          let s := si + 1
          let r := ri + 1
          let M := 4 * α * s * r - 1
          let val := p + 4 * α * s * s
          let m := val / M
          let c := m * r - s
          decide (val % M = 0 ∧ 0 < c ∧ p < 4 * α * s * c ∧
                  s + c = (4 * α * s * c - p) * r)

/-- Soundness of findED2: if it returns true, ED2 parameters exist. -/
theorem findED2_sound {p : ℕ} (h : findED2 p = true) : HasED2Params p := by
  simp only [findED2] at h
  split_ifs at h with h8 h3
  · -- Case 1: p ≡ 5 (mod 8)
    rw [decide_eq_true_eq] at h
    exact ⟨(p + 3) / 8, 1, 1, 2, h.1, Nat.one_pos, Nat.one_pos, by omega, h.2.1, h.2.2⟩
  · -- Case 2: p ≡ 2 (mod 3)
    rw [decide_eq_true_eq] at h
    exact ⟨1, 1, (p + 1) / 3, 1, Nat.one_pos, Nat.one_pos, h.1, Nat.one_pos, h.2.1, h.2.2⟩
  · -- Case 3: parametric search (all conditions in one decide)
    simp only [List.any_eq_true, List.mem_range] at h
    obtain ⟨ai, _, si, _, ri, _, h⟩ := h
    rw [decide_eq_true_eq] at h
    exact ⟨ai + 1, ri + 1, si + 1, _, by omega, by omega, by omega,
           h.2.1, h.2.2.1, h.2.2.2⟩

/-- Verify that all primes p ≡ 1 (mod 4) below the bound pass findED2. -/
def checkAllED2 (bound : ℕ) : Bool :=
  (List.range bound).all fun p =>
    if p < 5 then true
    else if p % 4 ≠ 1 then true
    else if ¬Nat.Prime p then true
    else findED2 p

/-- All primes p ≡ 1 (mod 4) below certBound have ED2 parameters.
    The computational core: native_decide evaluates findED2 for each
    of the ~40,000 primes p ≡ 1 (mod 4) up to 10^6. -/
theorem ed2_certificate_check : checkAllED2 certBound = true := by
  native_decide

/-- Soundness of checkAllED2: if it returns true, every qualifying prime
    below the bound satisfies HasED2Params. -/
theorem checkAllED2_sound {bound : ℕ} (h : checkAllED2 bound = true)
    {p : ℕ} (hp : Nat.Prime p) (hp4 : p % 4 = 1) (hlt : p < bound) :
    HasED2Params p := by
  have hfind : findED2 p = true := by
    simp only [checkAllED2, List.all_eq_true, List.mem_range] at h
    have h1 := h p hlt
    have h_ge5 : ¬(p < 5) := by have := hp.two_le; omega
    have h_mod4 : ¬(p % 4 ≠ 1) := by push_neg; exact hp4
    have h_prime : ¬¬Nat.Prime p := not_not.mpr hp
    rw [if_neg h_ge5, if_neg h_mod4, if_neg h_prime] at h1
    exact h1
  exact findED2_sound hfind

/-- Main certificate theorem: for all primes p ≡ 1 (mod 4) below certBound,
    ED2 parameters (α, d', b', c') exist satisfying the Dyachenko conditions. -/
theorem ed2_params_below_certBound {p : ℕ} (hp : Nat.Prime p) (hp4 : p % 4 = 1)
    (hlt : p < certBound) :
    ∃ α d' b' c' : ℕ,
      0 < α ∧ 0 < d' ∧ 0 < b' ∧ 0 < c' ∧
      p < 4 * α * b' * c' ∧
      b' + c' = (4 * α * b' * c' - p) * d' :=
  checkAllED2_sound ed2_certificate_check hp hp4 hlt

end ED2
