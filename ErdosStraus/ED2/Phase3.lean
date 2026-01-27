/-
  ErdosStraus/ED2/Phase3.lean

  Asymptotic ED2 (Type II) existence: algebraic core + Dyachenko bridge.

  Main result: `ed2_large_prime` shows that for primes p ≡ 1 (mod 4)
  above an explicit bound, the Type II equation has a solution.

  ## Architecture (4-layer proof)

  1. **Algebraic core** (`ed2_of_good_divisor`, PROVEN):
     Given a factorization of A², construct the Type II solution.

  2. **Dyachenko bridge** (`ed2_dyachenko_bridge`, PROVEN):
     Given Dyachenko's parameters (α, d', b', c') satisfying
     Theorem D.1's sum condition, construct the factorization data.

  3. **Dyachenko existence** (`ed2_dyachenko_params_exist`, SORRY):
     For large p ≡ 1 (mod 4), Dyachenko's parameters exist.
     This is Theorem 9.21 / Prop 9.25 from arXiv:2511.07465.

  4. **Assembly** (`ed2_large_prime`, PROVEN from 1+2+3):
     The final theorem combining all layers.

  ## Why variable δ is necessary

  The original approach fixed δ = 3. At the sorry site in Existence.lean,
  p ≡ 1 (mod 24), so A = (p+3)/4 ≡ 1 (mod 6). The factorization
  (3b - A)(3c - A) = A² requires a divisor of A² congruent to -A ≡ 2 (mod 3).
  When all prime factors of A are ≡ 1 (mod 3), no such divisor exists.

  The variable-δ approach avoids this: the Dyachenko construction
  chooses δ = 4αb'c' - p depending on the prime, using the lattice
  density argument (Prop 9.25) to guarantee suitable b', c' exist.
-/

import Mathlib.Tactic

namespace ED2

/-- Explicit bound for the asymptotic argument. Set to 2 so that
    `ed2_large_prime` applies to ALL primes (since Nat.Prime implies p ≥ 2).
    When certificate integration is complete, raise this to 10^7 and prove
    `ed2_dyachenko_params_exist` only for p ≥ 10^7 (using certificates below). -/
def ed2LargeBound : ℕ := 2

/-!
## Algebraic core

The Type II equation (p+δ)(b+c) = 4δbc factors as

    (δb - A)(δc - A) = A²

where A = (p+δ)/4. Given a positive divisor d of A² with δ | (d + A),
setting b = (d + A)/δ and c = (A²/d + A)/δ gives a solution.

The proof uses the identity:
  From δ·b = d + A and δ·c = e + A and d·e = A²,
  substitute d = δb - A, e = δc - A into d·e = A² to get
  δ²bc - Aδ(b+c) + A² = A², hence δ·bc = A·(b+c),
  hence 4δbc = 4A(b+c) = (p+δ)(b+c).
-/

/-- Given a factorization of A², construct a Type II solution.

The caller provides:
- `A` such that `p + δ = 4A`
- Positive integers `d`, `e` with `d · e = A²`
- Integers `b_val`, `c_val` with `δ · b_val = d + A` and `δ · c_val = e + A`

The theorem produces natural numbers `b`, `c > 0` satisfying
`(p + δ)(b + c) = 4δbc`. -/
theorem ed2_of_good_divisor
    (p δ : ℕ) (hδ_pos : 0 < δ)
    (A : ℤ) (hA : (↑p : ℤ) + ↑δ = 4 * A)
    (d e : ℤ) (hd_pos : 0 < d) (he_pos : 0 < e)
    (hde : d * e = A ^ 2)
    (b_val c_val : ℤ)
    (hb_def : (↑δ : ℤ) * b_val = d + A)
    (hc_def : (↑δ : ℤ) * c_val = e + A) :
    ∃ b c : ℕ,
      b > 0 ∧ c > 0 ∧
      (↑p + ↑δ : ℤ) * (↑b + ↑c) = 4 * ↑δ * ↑b * ↑c := by
  -- A is positive: 4A = p + δ ≥ 0 + 1 > 0
  have hδ_int : (0 : ℤ) < ↑δ := Nat.cast_pos.mpr hδ_pos
  have hδ_ne : (↑δ : ℤ) ≠ 0 := ne_of_gt hδ_int
  have hp_nn : (0 : ℤ) ≤ (↑p : ℤ) := Nat.cast_nonneg p
  have hA_pos : 0 < A := by linarith
  -- b_val is positive: δ · b_val = d + A > 0 and δ > 0
  have hb_pos : 0 < b_val := by
    by_contra h
    push_neg at h
    have h1 : 0 < (↑δ : ℤ) * b_val := by linarith
    have h2 : (↑δ : ℤ) * b_val ≤ (↑δ : ℤ) * 0 := by
      exact mul_le_mul_of_nonneg_left h (le_of_lt hδ_int)
    simp at h2; linarith
  -- c_val is positive: δ · c_val = e + A > 0 and δ > 0
  have hc_pos : 0 < c_val := by
    by_contra h
    push_neg at h
    have h1 : 0 < (↑δ : ℤ) * c_val := by linarith
    have h2 : (↑δ : ℤ) * c_val ≤ (↑δ : ℤ) * 0 := by
      exact mul_le_mul_of_nonneg_left h (le_of_lt hδ_int)
    simp at h2; linarith
  -- Provide witnesses as natural numbers
  refine ⟨b_val.toNat, c_val.toNat, ?_, ?_, ?_⟩
  -- b_val.toNat > 0
  · omega
  -- c_val.toNat > 0
  · omega
  · -- Cast back to ℤ: since b_val > 0, ↑(b_val.toNat) = b_val
    have hb_nn : 0 ≤ b_val := le_of_lt hb_pos
    have hc_nn : 0 ≤ c_val := le_of_lt hc_pos
    -- The key algebraic identity
    -- From d = δ·b_val - A and e = δ·c_val - A, substituting into d·e = A²:
    --   (δ·b_val - A)(δ·c_val - A) = A²
    --   δ²·b_val·c_val - A·δ·(b_val + c_val) + A² = A²
    --   δ²·b_val·c_val = A·δ·(b_val + c_val)
    -- Cancel δ > 0:
    --   δ·b_val·c_val = A·(b_val + c_val)
    -- Multiply by 4 and use 4A = p + δ:
    --   4·δ·b_val·c_val = (p+δ)·(b_val + c_val)
    have hd_eq : d = (↑δ : ℤ) * b_val - A := by linarith
    have he_eq : e = (↑δ : ℤ) * c_val - A := by linarith
    -- Substituted factorization
    have hde2 : ((↑δ : ℤ) * b_val - A) * ((↑δ : ℤ) * c_val - A) = A ^ 2 := by
      rw [← hd_eq, ← he_eq]; exact hde
    -- Scaled key identity: δ² · b_val · c_val = A · δ · (b_val + c_val)
    have key_scaled : (↑δ : ℤ) * ((↑δ : ℤ) * b_val * c_val - A * (b_val + c_val)) = 0 := by
      nlinarith [hde2, sq_nonneg A]
    -- Cancel δ ≠ 0 to get: δ · b_val · c_val = A · (b_val + c_val)
    have key : (↑δ : ℤ) * b_val * c_val = A * (b_val + c_val) := by
      have := mul_eq_zero.mp key_scaled
      rcases this with h | h
      · exact absurd h hδ_ne
      · linarith
    -- Goal in ℤ: (p + δ) * (b_val + c_val) = 4 * δ * b_val * c_val
    -- This follows from key and hA
    have goal_int : (↑p + ↑δ : ℤ) * (b_val + c_val) = 4 * ↑δ * b_val * c_val := by
      nlinarith [key, hA]
    -- Rewrite the ℕ casts using b_val.toNat and c_val.toNat
    -- We need: ↑(b_val.toNat) = b_val and ↑(c_val.toNat) = c_val
    -- This holds since b_val ≥ 0 and c_val ≥ 0
    conv_lhs => rw [show (↑(b_val.toNat) : ℤ) = b_val from by omega]
    conv_lhs => rw [show (↑(c_val.toNat) : ℤ) = c_val from by omega]
    conv_rhs => rw [show (↑(b_val.toNat) : ℤ) = b_val from by omega]
    conv_rhs => rw [show (↑(c_val.toNat) : ℤ) = c_val from by omega]
    exact goal_int

/-!
## Dyachenko bridge

Dyachenko (2025, Theorem D.1, arXiv:2511.07465) shows the ED2 identity
  (4αd'b' - 1)(4αd'c' - 1) = 4αPd'² + 1
is equivalent to: b' + c' = (4αb'c' - P) · d'.

Given α, d', b', c' satisfying this condition, we construct:
- δ = 4αb'c' - p  (automatically ≡ 3 mod 4 since p ≡ 1 mod 4)
- A = αb'c'        (so p + δ = 4A)
- d = αb'², e = αc'² (so d · e = A²)
- b_val = αd'b', c_val = αd'c'

The key identity for the divisibility conditions:
  δ · αd'b' = αb' · (δd') = αb' · (b'+c') = αb'² + αb'c' = d + A.
Similarly: δ · αd'c' = αc'² + αb'c' = e + A.
-/

/-- Bridge from Dyachenko's parameterization to the algebraic core format.

Given squarefree α ≥ 1, diagonal period d' ≥ 1, and reduced parameters
b', c' ≥ 1 satisfying Theorem D.1's sum condition, construct all data
needed by `ed2_of_good_divisor`. -/
theorem ed2_dyachenko_bridge
    (p : ℕ) (hp4 : p % 4 = 1)
    (α d' b' c' : ℕ)
    (hα : 0 < α) (hd' : 0 < d') (hb' : 0 < b') (hc' : 0 < c')
    (hbound : p < 4 * α * b' * c')
    (hsum : b' + c' = (4 * α * b' * c' - p) * d') :
    ∃ (δ : ℕ) (A d e b_val c_val : ℤ),
      0 < δ ∧ δ % 4 = 3 ∧
      (↑p : ℤ) + ↑δ = 4 * A ∧
      0 < d ∧ 0 < e ∧
      d * e = A ^ 2 ∧
      (↑δ : ℤ) * b_val = d + A ∧
      (↑δ : ℤ) * c_val = e + A := by
  set δ := 4 * α * b' * c' - p with hδ_def
  refine ⟨δ, ↑(α * b' * c'), ↑(α * b' * b'), ↑(α * c' * c'),
          ↑(α * d' * b'), ↑(α * d' * c'), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- 0 < δ
    omega
  · -- δ % 4 = 3 (since p ≡ 1 mod 4 and 4 | 4αb'c')
    have : 4 ∣ (4 * α * b' * c') := ⟨α * b' * c', by ring⟩
    omega
  · -- ↑p + ↑δ = 4 * ↑(α * b' * c')
    have hassoc : 4 * (α * b' * c') = 4 * α * b' * c' := by ring
    have hle : p ≤ 4 * α * b' * c' := Nat.le_of_lt hbound
    have h : p + δ = 4 * (α * b' * c') := by
      rw [hassoc, hδ_def]; exact Nat.add_sub_cancel' hle
    exact_mod_cast h
  · -- 0 < ↑(α * b' * b')
    exact_mod_cast Nat.mul_pos (Nat.mul_pos hα hb') hb'
  · -- 0 < ↑(α * c' * c')
    exact_mod_cast Nat.mul_pos (Nat.mul_pos hα hc') hc'
  · -- d * e = A² : ↑(α*b'*b') * ↑(α*c'*c') = ↑(α*b'*c') ^ 2
    push_cast; ring
  · -- δ * b_val = d + A : δ * ↑(α*d'*b') = ↑(α*b'*b') + ↑(α*b'*c')
    -- Key: δ·d' = b'+c' by hsum, so δ·αd'b' = αb'·(b'+c') = αb'² + αb'c'
    have h : δ * (α * d' * b') = α * b' * b' + α * b' * c' := by
      calc δ * (α * d' * b') = α * b' * (δ * d') := by ring
        _ = α * b' * (b' + c') := by rw [← hsum]
        _ = α * b' * b' + α * b' * c' := by ring
    exact_mod_cast h
  · -- δ * c_val = e + A : δ * ↑(α*d'*c') = ↑(α*c'*c') + ↑(α*b'*c')
    have h : δ * (α * d' * c') = α * c' * c' + α * b' * c' := by
      calc δ * (α * d' * c') = α * c' * (δ * d') := by ring
        _ = α * c' * (b' + c') := by rw [← hsum]
        _ = α * c' * c' + α * b' * c' := by ring
    exact_mod_cast h

/-!
## Number-theoretic existence (sorry'd)

The remaining content is Dyachenko (2025, Theorem 9.21, condition III,
arXiv:2511.07465): for every prime p ≡ 1 (mod 4), there exist
parameters (α, d', b', c') satisfying:
- α, d', b', c' ≥ 1
- p < 4αb'c' (so that δ = 4αb'c' - p > 0)
- b' + c' = δ · d' (the lattice condition from Theorem D.1)

### Equivalent formulations (Appendix D)

By Theorem D.1, the conditions are equivalent to:
  (4αd'b' - 1)(4αd'c' - 1) = 4αpd'² + 1

By Theorem D.2 (quadratic reparameterization), setting A = αb'c',
m = 4A - p, S = m·d', the conditions are equivalent to:
  b', c' are roots of x² - Sx + (A/α) = 0
i.e., the discriminant Δ = S² - 4A/α is a perfect square.

By Lemma D.16, this is equivalent to: there exist A, α, d' with
α | A, A ∈ [(p+3)/4, (3p-3)/4], and d' ≥ 1, such that
(4A - p)²d'² - 4A/α is a perfect square.

### Why the sorry is irreducible without the full lattice argument

The D.6 construction (Lemma D.6) produces moduli M = 4αsr - 1 ≡ 3 (mod 4).
For such M, -1 is a QNR, so D.6 residue conditions P ≡ -4αs² (mod M)
force P into QNR classes. The QR classes (p mod 7 ∈ {1,2,4}, p mod 5 ∈ {1,4})
are STRUCTURALLY unreachable by any D.6 extension.

The simplest approach (α = d' = 1) reduces to factoring 4p+1 into two
factors ≡ 3 (mod 4), but 4p+1 can be prime (≡ 1 mod 4), so this fails.

The full proof requires Dyachenko's lattice density argument:
1. Choose A in the window, set g = αd' for appropriate α
2. The kernel lattice L = {(u,v) : g | ub' + vc'} has index g
   (proven in `WindowLattice.lean` as `kernel_lattice_index`)
3. The window lemma (Prop 9.25, proven as `ed2_window_lemma`)
   guarantees any g×g rectangle contains a lattice point
4. By D.33, any lattice point automatically satisfies the discriminant
   condition (Δ = v² is always a perfect square under normalization)
5. For the Type I box, sides ~ (log P)^A₀ >> d' = g/α, so
   the window lemma applies

### Mathlib ingredients available

- `Nat.Prime.sq_add_sq` : p ≡ 1 (mod 4) → ∃ a b, a² + b² = p
- `ZMod.exists_sq_eq_neg_one_iff` : IsSquare (-1 : ZMod p) ↔ p % 4 ≠ 3
- `Fintype.exists_ne_map_eq_of_card_lt` : pigeonhole principle
- `ED2.ed2_window_lemma` : g×g rectangle hits the kernel lattice
- `ED2.kernel_lattice_index` : the lattice has index g

### Estimated formalization effort

~500-1000 lines of new Lean code, primarily:
- Parameter selection logic (~200 LOC)
- Box size vs d' comparison (~100 LOC)
- Lattice point decoding to (b', c') (~150 LOC)
- Showing the Type I box satisfies H, W ≥ g (~200 LOC)

This is the ONLY remaining sorry in the Phase 3 asymptotic argument.
All other components (algebraic core, bridge, assembly) are fully proven.
-/

/-- Dyachenko's existence claim (Theorem 9.21, Condition III).
    For primes p ≡ 1 (mod 4) above the explicit bound, parameters
    (α, d', b', c') exist such that the ED2 identity holds.

    The algebraic infrastructure is proven:
    - `ed2_of_good_divisor`: factorization → Type II solution
    - `ed2_dyachenko_bridge`: (α,d',b',c') → factorization data
    - `ed2_window_lemma` (WindowLattice.lean): g×g box → lattice point

    What remains is the parameter selection argument showing that
    for some (α, d'), the window lemma produces valid (b', c').
    See `dyachenko_paper_notes.md` for the full mathematical content. -/
theorem ed2_dyachenko_params_exist
    (p : ℕ) (hp : Nat.Prime p) (hp4 : p % 4 = 1) (hp_large : p ≥ ed2LargeBound) :
    ∃ α d' b' c' : ℕ,
      0 < α ∧ 0 < d' ∧ 0 < b' ∧ 0 < c' ∧
      p < 4 * α * b' * c' ∧
      b' + c' = (4 * α * b' * c' - p) * d' := by
  sorry

/-- For large primes p ≡ 1 (mod 4), the algebraic core data exists.
    Proved by combining the Dyachenko bridge with the existence claim. -/
theorem ed2_exists_good_offset
    (p : ℕ) (hp : Nat.Prime p) (hp4 : p % 4 = 1) (hp_large : p ≥ ed2LargeBound) :
    ∃ (δ : ℕ) (A d e b_val c_val : ℤ),
      0 < δ ∧ δ % 4 = 3 ∧
      (↑p : ℤ) + ↑δ = 4 * A ∧
      0 < d ∧ 0 < e ∧
      d * e = A ^ 2 ∧
      (↑δ : ℤ) * b_val = d + A ∧
      (↑δ : ℤ) * c_val = e + A := by
  obtain ⟨α, d', b', c', hα, hd', hb', hc', hbound, hsum⟩ :=
    ed2_dyachenko_params_exist p hp hp4 hp_large
  exact ed2_dyachenko_bridge p hp4 α d' b' c' hα hd' hb' hc' hbound hsum

/-!
## Main asymptotic theorem

Combines the proven algebraic core with the Dyachenko bridge and
existence claim.
-/

/-- For primes p ≡ 1 (mod 4) above the explicit bound, the Type II equation
    has a solution with offset ≡ 3 (mod 4).

    Designed to be callable at the sorry location in `ed2_qr_classes` in
    `Existence.lean`, after splitting on `p < ed2LargeBound` (handled by
    finite certificates) vs `p ≥ ed2LargeBound` (this theorem). -/
theorem ed2_large_prime
    (p : ℕ) (hp : Nat.Prime p) (hp4 : p % 4 = 1) (hp_large : p ≥ ed2LargeBound) :
    ∃ offset b c : ℕ,
      offset % 4 = 3 ∧ b > 0 ∧ c > 0 ∧
      (↑p + ↑offset : ℤ) * (↑b + ↑c) = 4 * ↑offset * ↑b * ↑c := by
  -- Obtain the number-theoretic data
  obtain ⟨δ, A, d, e, b_val, c_val, hδ_pos, hδ_mod, hA, hd_pos, he_pos, hde, hb_def, hc_def⟩ :=
    ed2_exists_good_offset p hp hp4 hp_large
  -- Apply the proven algebraic core
  obtain ⟨b, c, hb_pos, hc_pos, hEq⟩ :=
    ed2_of_good_divisor p δ hδ_pos A hA d e hd_pos he_pos hde b_val c_val hb_def hc_def
  exact ⟨δ, b, c, hδ_mod, hb_pos, hc_pos, hEq⟩

end ED2
