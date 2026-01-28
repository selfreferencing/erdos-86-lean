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
  - `HasED2Params p` is the proposition (existence of α, d', b', c')
  - `decideED2 p` is a Decidable instance for bounded search
  - The certificate theorem uses native_decide on this Decidable instance
  - Soundness is built into the Decidable instance itself

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

/-- Bounded version: restrict search to α ≤ αB, d' ≤ dB, b' ≤ bB, c' ≤ cB. -/
def HasED2ParamsBounded (p αB dB bB cB : ℕ) : Prop :=
  ∃ α ≤ αB, ∃ d' ≤ dB, ∃ b' ≤ bB, ∃ c' ≤ cB,
    0 < α ∧ 0 < d' ∧ 0 < b' ∧ 0 < c' ∧
    p < 4 * α * b' * c' ∧
    b' + c' = (4 * α * b' * c' - p) * d'

instance (p αB dB bB cB : ℕ) : Decidable (HasED2ParamsBounded p αB dB bB cB) :=
  inferInstance

theorem HasED2ParamsBounded.to_unbounded {p αB dB bB cB : ℕ}
    (h : HasED2ParamsBounded p αB dB bB cB) : HasED2Params p := by
  obtain ⟨α, _, d', _, b', _, c', _, hα, hd', hb', hc', hbound, hsum⟩ := h
  exact ⟨α, d', b', c', hα, hd', hb', hc', hbound, hsum⟩

/-- The full check: for all p in [5, bound) with p prime and p ≡ 1 (mod 4),
    ED2 parameters exist within search bounds.

    Search strategy:
    - p ≡ 5 (mod 8): check α = (p+3)/8, d' = 1, b' = 1, c' = 2
    - p ≡ 2 (mod 3): check α = 1, d' = 1, b' = (p+1)/3, c' = 1
    - p ≡ 1 (mod 24): search α ≤ 5, d'(=r) ≤ 50, b'(=s) ≤ 50, c' ≤ p

    For native_decide, we encode this as a single Bool computation
    rather than using the Decidable instance on HasED2ParamsBounded
    (which would enumerate all 4-tuples and be too slow). -/
def findED2 (p : ℕ) : Bool :=
  -- Case 1: p ≡ 5 (mod 8)
  if p % 8 == 5 then
    let α := (p + 3) / 8
    0 < α && p < 4 * α * 1 * 2 && 1 + 2 == (4 * α * 1 * 2 - p) * 1
  -- Case 2: p ≡ 1 (mod 8), p ≡ 2 (mod 3)
  else if p % 3 == 2 then
    let b' := (p + 1) / 3
    0 < b' && p < 4 * 1 * b' * 1 && b' + 1 == (4 * 1 * b' * 1 - p) * 1
  -- Case 3: p ≡ 1 (mod 24), parametric search
  else
    (List.range 5).any fun ai =>
      let α := ai + 1
      (List.range 50).any fun si =>
        let s := si + 1
        let val := p + 4 * α * s * s
        (List.range 50).any fun ri =>
          let r := ri + 1
          if 4 * α * s * r ≤ 1 then false
          else
            let M := 4 * α * s * r - 1
            if val % M != 0 then false
            else
              let m := val / M
              if m * r ≤ s then false
              else
                let c := m * r - s
                0 < α && 0 < r && 0 < s && 0 < c &&
                p < 4 * α * s * c && s + c == (4 * α * s * c - p) * r

/-- Soundness of findED2: if it returns true, ED2 parameters exist.

    The proof extracts the witness from whichever case succeeded. -/
theorem findED2_sound {p : ℕ} (h : findED2 p = true) : HasED2Params p := by
  simp only [findED2, beq_iff_eq, bne_iff_ne, Bool.and_eq_true,
    decide_eq_true_eq] at h
  split at h
  · -- Case 1: p ≡ 5 (mod 8)
    obtain ⟨⟨hα, hbound⟩, hsum⟩ := h
    exact ⟨(p + 3) / 8, 1, 1, 2, hα, Nat.one_pos, Nat.one_pos,
      by omega, hbound, hsum⟩
  · split at h
    · -- Case 2: p ≡ 2 (mod 3)
      obtain ⟨⟨hb, hbound⟩, hsum⟩ := h
      exact ⟨1, 1, (p + 1) / 3, 1, Nat.one_pos, Nat.one_pos, hb,
        Nat.one_pos, hbound, hsum⟩
    · -- Case 3: parametric search
      simp only [List.any_eq_true, List.mem_range] at h
      obtain ⟨ai, _, h⟩ := h
      simp only [List.any_eq_true, List.mem_range] at h
      obtain ⟨si, _, h⟩ := h
      simp only [List.any_eq_true, List.mem_range] at h
      obtain ⟨ri, _, h⟩ := h
      -- Unfold the conditionals
      split at h
      · exact absurd h Bool.false_ne_true
      · split at h
        · exact absurd h Bool.false_ne_true
        · split at h
          · exact absurd h Bool.false_ne_true
          · simp only [Bool.and_eq_true, decide_eq_true_eq] at h
            obtain ⟨⟨⟨⟨⟨hα, hr⟩, hs⟩, hc⟩, hbound⟩, hsum⟩ := h
            exact ⟨ai + 1, ri + 1, si + 1, _, hα, hr, hs, hc, hbound, hsum⟩

/-- Verify that all primes p ≡ 1 (mod 4) below the bound pass findED2. -/
def checkAllED2 (bound : ℕ) : Bool :=
  (List.range bound).all fun p =>
    p < 5 || p % 4 != 1 || !(decide (Nat.Prime p)) || findED2 p

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
    have := h p hlt
    simp only [Bool.or_eq_true, bne_iff_ne, Bool.not_eq_true',
      decide_eq_false_iff_not, decide_eq_true_eq] at this
    rcases this with h5 | h4 | hnp | hfind
    · exact absurd h5 (by omega)
    · exact absurd h4 (by omega)
    · exact absurd hp hnp
    · exact hfind
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
