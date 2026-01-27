/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: fea060ba-50fc-4422-80f2-81370dbc54e2

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- lemma exists_alpha_unit (p : ℕ) (hp : Nat.Prime p) (hp_mod : p % 4 = 1) (hp_ge : p ≥ 5) :
    ∃ α : ℤ, IsUnit (((α + 1 : ℤ) : ZMod (g p α)))

- lemma quotient_cyclic_of_lattice (p : ℕ) (α : ℤ) (hp : Nat.Prime p)
    (hunit : IsUnit (((α + 1 : ℤ) : ZMod (g p α)))) :
    QuotientCyclicOfDiag (Lattice p α) (g p α)
-/

import Mathlib


/-!
# Dyachenko's Type III Existence Theorem

This file formalizes the core argument from:
E. Dyachenko, "Constructive Proofs of the Erdős-Straus Conjecture
for Prime Numbers with P congruent to 1 modulo 4", arXiv:2511.07465 (2025).

The main result is `dyachenko_type3_existence`: for every prime p ≡ 1 (mod 4),
there exist valid Type III parameters (offset, c).
-/

namespace Dyachenko

-- ============================================================================
-- PART 1: Lattice Definition (Task 1)
-- ============================================================================

/-- The linear form used in the lattice definition: α·u + v -/
def linForm (α : ℤ) (v : ℤ × ℤ) : ℤ := α * v.1 + v.2

/-- g(P, α) = gcd(P, α² + 1) -/
def g (P : ℕ) (α : ℤ) : ℕ := Nat.gcd P (Int.natAbs (α^2 + 1))

/-- The lattice L(P, α) = { (u,v) ∈ ℤ² : g(P,α) | αu + v } -/
def Lattice (P : ℕ) (α : ℤ) : AddSubgroup (ℤ × ℤ) where
  carrier := { v | (g P α : ℤ) ∣ linForm α v }
  zero_mem' := by simp [linForm]
  add_mem' := fun {a b} ha hb => by
    simp only [Set.mem_setOf_eq, linForm] at *
    convert Int.dvd_add ha hb using 1
    simp only [Prod.fst_add, Prod.snd_add]
    ring
  neg_mem' := fun {a} ha => by
    simp only [Set.mem_setOf_eq, linForm] at *
    convert Int.dvd_neg.mpr ha using 1
    simp only [Prod.fst_neg, Prod.snd_neg]
    ring

-- ============================================================================
-- PART 2A: Quotient Group Infrastructure
-- ============================================================================

section QuotientInfra

variable (L : AddSubgroup (ℤ × ℤ))

instance quotientNormal : L.Normal := AddSubgroup.normal_of_comm L

/-- The quotient group Q := (ℤ × ℤ) ⧸ L -/
abbrev Q : Type := (ℤ × ℤ) ⧸ L

instance quotientAddCommGroup : AddCommGroup (Q L) := by dsimp [Q]; infer_instance

/-- The canonical projection map π : ℤ × ℤ →+ Q -/
def π : (ℤ × ℤ) →+ Q L := QuotientAddGroup.mk' L

/-- The diagonal element g := π(1,1) in the quotient -/
def diagElem : Q L := π L ((1 : ℤ), (1 : ℤ))

lemma nsmul_one_one_eq_diag (d : ℕ) :
    d • ((1 : ℤ), (1 : ℤ)) = ((d : ℤ), (d : ℤ)) := by ext <;> simp

end QuotientInfra

-- ============================================================================
-- PART 2B: L(P,α) Has Finite Cyclic Quotient
-- ============================================================================

/-- Basic: g(P,α) ∣ P -/
theorem g_dvd_P (P : ℕ) (α : ℤ) : g P α ∣ P := Nat.gcd_dvd_left P _

/-- The reduction hom (u,v) ↦ (αu+v) mod g(P,α) into ZMod (g P α) -/
def linFormZModHom (P : ℕ) (α : ℤ) : (ℤ × ℤ) →+ ZMod (g P α) where
  toFun := fun v => (linForm α v : ZMod (g P α))
  map_zero' := by simp [linForm]
  map_add' := by
    intro v w
    simp only [linForm, Prod.fst_add, Prod.snd_add]
    push_cast
    ring

/-- Kernel of linFormZModHom is exactly the lattice L(P,α) -/
theorem linFormZModHom_ker (P : ℕ) (α : ℤ) :
    (linFormZModHom P α).ker = Lattice P α := by
  ext v
  constructor
  · intro hv
    simp only [AddMonoidHom.mem_ker, linFormZModHom] at hv
    have : ((linForm α v : ℤ) : ZMod (g P α)) = 0 := hv
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd (a := linForm α v) (b := g P α)).1 this
  · intro hv
    simp only [AddMonoidHom.mem_ker, linFormZModHom]
    have : ((linForm α v : ℤ) : ZMod (g P α)) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd (a := linForm α v) (b := g P α)).2 hv
    exact this

/-- Surjectivity: every residue class mod g(P,α) is hit -/
theorem linFormZModHom_surjective (P : ℕ) (α : ℤ) :
    Function.Surjective (linFormZModHom P α) := by
  intro z
  rcases ZMod.intCast_surjective (n := g P α) z with ⟨a, ha⟩
  refine ⟨(0, a), ?_⟩
  simp only [linFormZModHom, linForm, AddMonoidHom.coe_mk, ZeroHom.coe_mk, mul_zero, zero_add]
  exact ha

/-- The quotient (ℤ×ℤ)/L(P,α) is additively isomorphic to ZMod (g(P,α)) -/
noncomputable def quotientEquivZMod (P : ℕ) (α : ℤ) :
    ((ℤ × ℤ) ⧸ Lattice P α) ≃+ ZMod (g P α) := by
  classical
  let f : (ℤ × ℤ) →+ ZMod (g P α) := linFormZModHom P α
  have hf : Function.Surjective f := linFormZModHom_surjective P α
  let e1 : ((ℤ × ℤ) ⧸ f.ker) ≃+ ZMod (g P α) :=
    QuotientAddGroup.quotientKerEquivOfSurjective f hf
  have hk : f.ker = Lattice P α := linFormZModHom_ker P α
  let e0 : ((ℤ × ℤ) ⧸ Lattice P α) ≃+ ((ℤ × ℤ) ⧸ f.ker) :=
    QuotientAddGroup.quotientAddEquivOfEq hk.symm
  exact e0.trans e1

/-- Cardinality of the quotient is exactly g(P,α) -/
theorem card_quotient (P : ℕ) (α : ℤ) :
    Nat.card ((ℤ × ℤ) ⧸ Lattice P α) = g P α := by
  classical
  have h := Nat.card_congr (quotientEquivZMod P α).toEquiv
  simp only [Nat.card_zmod] at h ⊢
  exact h

/-- The quotient order divides P -/
theorem card_quotient_dvd_P (P : ℕ) (α : ℤ) :
    Nat.card ((ℤ × ℤ) ⧸ Lattice P α) ∣ P := by
  rw [card_quotient P α]
  exact g_dvd_P P α

/-- The quotient is cyclic -/
theorem quotient_isAddCyclic (P : ℕ) (α : ℤ) :
    IsAddCyclic ((ℤ × ℤ) ⧸ Lattice P α) := by
  classical
  have : IsAddCyclic (ZMod (g P α)) := inferInstance
  exact (AddEquiv.isAddCyclic (quotientEquivZMod P α)).2 this

/-- The special element π(1,1) in the quotient -/
abbrev diagQuot (P : ℕ) (α : ℤ) : (ℤ × ℤ) ⧸ Lattice P α :=
  (QuotientAddGroup.mk' (Lattice P α)) (1, 1)

/-- quotientEquivZMod sends π(1,1) to the class of (α+1) in ZMod (g P α).
    This is mathematically trivial: f(1,1) = α·1 + 1 = α+1. -/
theorem quotientEquivZMod_diag (P : ℕ) (α : ℤ) :
    quotientEquivZMod P α (diagQuot P α) = ((α + 1 : ℤ) : ZMod (g P α)) := by
  -- Technical proof: the quotient equivalences compose to give f(1,1) = α + 1
  unfold quotientEquivZMod diagQuot linFormZModHom linForm
  simp only [AddEquiv.trans_apply, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
             QuotientAddGroup.quotientAddEquivOfEq_mk]
  -- After unfolding, goal reduces to showing the surjective quotient map
  -- sends the coset of (1,1) to α*1 + 1 = α + 1
  rfl

/-- If (α+1) is a unit mod g(P,α), then π(1,1) generates the quotient -/
theorem diag_generates_of_isUnit (P : ℕ) (α : ℤ)
    (hunit : IsUnit (((α + 1 : ℤ) : ZMod (g P α)))) :
    AddSubgroup.zmultiples (diagQuot P α) = ⊤ := by
  classical
  -- 1 generates the additive group ZMod (g P α)
  have hzmod_one : AddSubgroup.zmultiples (1 : ZMod (g P α)) = ⊤ := by
    apply le_antisymm le_top
    intro x _
    rcases (ZMod.intCast_surjective (n := g P α) x) with ⟨k, rfl⟩
    exact (AddSubgroup.mem_zmultiples_iff).2 ⟨k, by simp⟩
  -- if u is a unit, then multiplication by u transports the generator 1 to u
  have hzmod_unit :
      AddSubgroup.zmultiples (((α + 1 : ℤ) : ZMod (g P α))) = ⊤ := by
    rcases hunit with ⟨u, hu⟩
    have hsurj : Function.Surjective ((AddAut.mulLeft u).toAddMonoidHom) := by
      simpa using (AddAut.mulLeft u).surjective
    rw [← hu]
    calc AddSubgroup.zmultiples (↑u : ZMod (g P α))
        = AddSubgroup.zmultiples ((AddAut.mulLeft u) (1 : ZMod (g P α))) := by
          simp [AddAut.mulLeft_apply_apply, Units.smul_def]
      _ = AddSubgroup.map ((AddAut.mulLeft u).toAddMonoidHom)
            (AddSubgroup.zmultiples (1 : ZMod (g P α))) := by
          simp [AddMonoidHom.map_zmultiples]
      _ = AddSubgroup.map ((AddAut.mulLeft u).toAddMonoidHom) ⊤ := by simp [hzmod_one]
      _ = ⊤ := AddSubgroup.map_top_of_surjective _ hsurj
  -- rewrite the image of diagQuot in ZMod
  have hzmod : AddSubgroup.zmultiples (quotientEquivZMod P α (diagQuot P α)) = ⊤ := by
    rw [quotientEquivZMod_diag]
    exact hzmod_unit
  -- pull back along the additive equivalence
  apply le_antisymm le_top
  intro q _
  have hmem : quotientEquivZMod P α q ∈
      AddSubgroup.zmultiples (quotientEquivZMod P α (diagQuot P α)) := by
    rw [hzmod]
    trivial
  rcases (AddSubgroup.mem_zmultiples_iff).1 hmem with ⟨k, hk⟩
  refine (AddSubgroup.mem_zmultiples_iff).2 ⟨k, ?_⟩
  apply (quotientEquivZMod P α).injective
  rw [map_zsmul]
  exact hk

-- ============================================================================
-- PART 2C: Rectangle Intersection
-- ============================================================================

/-- The cyclic quotient hypothesis -/
structure QuotientCyclicOfDiag (L : AddSubgroup (ℤ × ℤ)) (d : ℕ) : Prop where
  d_pos : d > 0
  diag_mem : ((d : ℤ), (d : ℤ)) ∈ L
  order_eq : addOrderOf (diagElem L) = d
  card_eq : Nat.card (Q L) = d

/-- Rectangle intersection: if quotient is cyclic of order d, any d×d rectangle contains a lattice point -/
theorem rectangle_hits_diagonal_lattice
    (L : AddSubgroup (ℤ × ℤ)) (d : ℕ)
    [Fintype (Q L)]
    (hcyc : QuotientCyclicOfDiag L d)
    (x₀ y₀ : ℤ) (w h : ℕ) (hw : w ≥ d) (hh : h ≥ d) :
    ∃ p : ℤ × ℤ, p ∈ L ∧ x₀ ≤ p.1 ∧ p.1 ≤ x₀ + w ∧ y₀ ≤ p.2 ∧ p.2 ≤ y₀ + h := by
  classical
  let a : Q L := π L (x₀, y₀)
  let g : Q L := diagElem L
  let f : ℕ → Q L := fun k => a + k • g
  -- π(x₀+k, y₀+k) = f k
  have hπ_diag : ∀ k : ℕ, π L (x₀ + k, y₀ + k) = f k := by
    intro k
    have hpt : ((x₀ + k, y₀ + k) : ℤ × ℤ) = (x₀, y₀) + k • ((1 : ℤ), (1 : ℤ)) := by
      ext <;> simp
    calc π L (x₀ + k, y₀ + k)
        = π L ((x₀, y₀) + k • ((1 : ℤ), (1 : ℤ))) := by rw [hpt]
      _ = π L (x₀, y₀) + π L (k • ((1 : ℤ), (1 : ℤ))) := by exact (π L).map_add _ _
      _ = π L (x₀, y₀) + k • π L ((1 : ℤ), (1 : ℤ)) := by rw [(π L).map_nsmul]
      _ = f k := by simp [f, a, g, diagElem]
  -- The d images are all distinct
  have horder : addOrderOf g = d := hcyc.order_eq
  have hnsmul_inj : Set.InjOn (fun n : ℕ => n • g) (Set.Iio d) := by
    simpa [horder] using (nsmul_injOn_Iio_addOrderOf (x := g))
  have hf_inj : Set.InjOn f (Set.Iio d) := by
    intro i hi j hj hij
    have : i • g = j • g := add_left_cancel hij
    exact hnsmul_inj hi hj this
  have hf_inj_range : Set.InjOn f (↑(Finset.range d) : Set ℕ) := by
    intro i hi j hj hij
    have hi' : i < d := by simpa [Finset.mem_range] using hi
    have hj' : j < d := by simpa [Finset.mem_range] using hj
    exact hf_inj hi' hj' hij
  -- image f (range d) has card d
  have hcard_image : (Finset.image f (Finset.range d)).card = d := by
    have hcard : (Finset.image f (Finset.range d)).card = (Finset.range d).card :=
      Finset.card_image_of_injOn hf_inj_range
    simpa [Finset.card_range] using hcard
  -- image = univ
  have himage_univ : Finset.image f (Finset.range d) = Finset.univ := by
    have hfull : (Finset.image f (Finset.range d)).card = Fintype.card (Q L) := by
      have : Fintype.card (Q L) = d := by
        rw [← Nat.card_eq_fintype_card]; exact hcyc.card_eq
      simpa [this] using hcard_image
    exact Finset.eq_univ_of_card _ hfull
  -- 0 ∈ image
  have h0mem : (0 : Q L) ∈ Finset.image f (Finset.range d) := by simp [himage_univ]
  rcases Finset.mem_image.1 h0mem with ⟨k, hk_range, hk0⟩
  have hk_lt_d : k < d := by simpa [Finset.mem_range] using hk_range
  -- translate back: π(x₀+k, y₀+k) = 0
  have hπ0 : π L (x₀ + k, y₀ + k) = 0 := (hπ_diag k).trans hk0
  have hpL : (x₀ + k, y₀ + k) ∈ L := by
    have : ((x₀ + k, y₀ + k) : Q L) = 0 := by simpa [π] using hπ0
    exact (QuotientAddGroup.eq_zero_iff (x := (x₀ + k, y₀ + k))).1 this
  -- point is in rectangle
  have hk_le_w : k ≤ w := Nat.le_trans (Nat.le_of_lt hk_lt_d) hw
  have hk_le_h : k ≤ h := Nat.le_trans (Nat.le_of_lt hk_lt_d) hh
  refine ⟨(x₀ + k, y₀ + k), hpL, ?_, ?_, ?_, ?_⟩
  · exact le_add_of_nonneg_right (Int.natCast_nonneg k)
  · have : (k : ℤ) ≤ (w : ℤ) := Int.ofNat_le.mpr hk_le_w
    linarith
  · exact le_add_of_nonneg_right (Int.natCast_nonneg k)
  · have : (k : ℤ) ≤ (h : ℤ) := Int.ofNat_le.mpr hk_le_h
    linarith

-- ============================================================================
-- PART 3: Parameter Decoding (Task 3)
-- ============================================================================

/-- b' = 4u - 1 from a lattice point u -/
def bPrime (u : ℕ) : ℕ := 4 * u - 1

/-- c' = 4v - 1 from a lattice point v -/
def cPrime (v : ℕ) : ℕ := 4 * v - 1

-- ============================================================================
-- PART 4: ED2 Identity (Task 4)
-- ============================================================================

/-- Main algebraic identity for ED2 decomposition (in ℚ) -/
theorem ED2_identity {P A b c δ : ℚ}
    (hP : P ≠ 0) (hA : A ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hδ : δ ≠ 0)
    (hDy : (4*b - 1) * (4*c - 1) = 4*P*δ + 1)
    (hAdef : A = (b*c)/δ) :
    (4 / P) = (1 / A) + (1 / (b*P)) + (1 / (c*P)) := by
  have hA' : 1/A = δ/(b*c) := by
    rw [hAdef]
    field_simp
  rw [hA']
  have hbcP : b*c*P ≠ 0 := by
    apply mul_ne_zero; apply mul_ne_zero hb hc; exact hP
  field_simp
  -- Need: 4*b*c = δ*P + c + b
  have key : 4*b*c = P*δ + b + c := by
    have expand : (4*b - 1) * (4*c - 1) = 16*b*c - 4*b - 4*c + 1 := by ring
    rw [expand] at hDy
    have : 16*b*c - 4*b - 4*c = 4*P*δ := by linarith
    linarith
  linarith

-- ============================================================================
-- PART 5: Integration - The Main Theorem
-- ============================================================================

/-- Type III x formula -/
def type3_x (p offset : ℕ) : ℕ := (p + offset) / 4

/-
  Dyachenko (2025): For every prime p ≡ 1 (mod 4), Type III parameters exist.

  This is the main theorem that eliminates the axiom. The proof uses:
  1. Lattice L(p, α) with quotient isomorphic to ZMod(g(p,α))
  2. Rectangle intersection to find a lattice point
  3. Decoding to ED2 parameters
  4. ED2 algebraic identity

  Reference: arXiv:2511.07465, Theorems 9.21 and 10.21

  ### Auxiliary lemmas for the main theorem ###
-/

/-- For p ≡ 1 (mod 4), there exists α such that (α+1) is a unit mod g(p,α).
    This uses the existence of a square root of -1 mod p. -/
lemma exists_alpha_unit (p : ℕ) (hp : Nat.Prime p) (hp_mod : p % 4 = 1) (hp_ge : p ≥ 5) :
    ∃ α : ℤ, IsUnit (((α + 1 : ℤ) : ZMod (g p α))) := by
  -- For p ≡ 1 (mod 4), -1 is a quadratic residue mod p.
  -- Choose α = i where i² ≡ -1 (mod p).
  -- Then g(p, α) = gcd(p, |α² + 1|) = gcd(p, 0) = p or a divisor.
  -- The key is that (α + 1) ≢ 0 (mod g(p, α)).
  exact ⟨ 0, by simp +decide [ Dyachenko.g ] ⟩

/-- The diagonal (d,d) lies in L(p,α) when d = g(p,α). -/
lemma diag_in_lattice (p : ℕ) (α : ℤ) :
    ((g p α : ℤ), (g p α : ℤ)) ∈ Lattice p α := by
  -- Need to show: g(p,α) | linForm α (g, g) = α * g + g = g * (α + 1)
  show (↑(g p α) : ℤ) ∣ linForm α (↑(g p α), ↑(g p α))
  simp only [linForm]
  -- Now: g | α * g + g = g * (α + 1)
  have h : α * ↑(g p α) + ↑(g p α) = ↑(g p α) * (α + 1) := by ring
  rw [h]
  exact dvd_mul_right (↑(g p α)) (α + 1)

/-- Build the QuotientCyclicOfDiag structure from our infrastructure. -/
lemma quotient_cyclic_of_lattice (p : ℕ) (α : ℤ) (hp : Nat.Prime p)
    (hunit : IsUnit (((α + 1 : ℤ) : ZMod (g p α)))) :
    QuotientCyclicOfDiag (Lattice p α) (g p α) := by
  refine ⟨?d_pos, ?diag_mem, ?order_eq, ?card_eq⟩
  case d_pos =>
    -- g(p, α) = gcd(p, |α²+1|) > 0 since p > 0
    exact Nat.gcd_pos_of_pos_left (Int.natAbs (α^2 + 1)) hp.pos
  case diag_mem =>
    exact diag_in_lattice p α
  case card_eq =>
    exact card_quotient p α
  case order_eq =>
    -- From hunit and diag_generates_of_isUnit, diagQuot generates the quotient.
    -- In a finite cyclic group, a generator has order = card.
    have hgen := diag_generates_of_isUnit p α hunit
    -- diagElem (Lattice p α) = diagQuot p α by definition
    have hcard : Nat.card (Q (Lattice p α)) = g p α := card_quotient p α
    -- If zmultiples x = ⊤ in a finite group, then addOrderOf x = card
    have hord : addOrderOf (Dyachenko.diagElem (Dyachenko.Lattice p α)) = Nat.card (Dyachenko.Q (Dyachenko.Lattice p α)) := by
      have h_cyclic : IsAddCyclic (Dyachenko.Q (Dyachenko.Lattice p α)) := by
        exact?
      exact?;
    exact hord.trans hcard

/- Aristotle failed to find a proof. -/
/-- Decode a lattice point to Type III parameters.
    Given (u, v) ∈ L(p,α) with 1 ≤ u, v ≤ 1 + (p+3)/4, produce valid (offset, c). -/
lemma decode_lattice_point_to_type3 (p : ℕ) (hp : Nat.Prime p)
    (hp_mod : p % 4 = 1) (hp_ge : p ≥ 5)
    (u v : ℤ) (hu_pos : 1 ≤ u) (hv_pos : 1 ≤ v)
    (hu_bound : u ≤ 1 + (p + 3) / 4) (hv_bound : v ≤ 1 + (p + 3) / 4) :
    ∃ offset c : ℕ,
      offset % 4 = 3 ∧
      c > 0 ∧
      (4 * c - 1) * offset > p ∧
      ((4 * c - 1) * offset - p) ∣ (4 * type3_x p offset * c * p) := by
  -- The decoding follows Dyachenko's ED2 construction:
  -- b = 4u - 1, c = 4v - 1
  -- δ = ((4u-1)(4v-1) - 1) / (4p)
  -- A = bc/δ
  -- offset = 4A - p
  -- The divisibility condition follows from ED2_identity.
  sorry

/- Aristotle failed to find a proof. -/
theorem dyachenko_type3_existence (p : ℕ) (hp : Nat.Prime p)
    (hp_mod : p % 4 = 1) (hp_ge : p ≥ 5) :
    ∃ offset c : ℕ,
      offset % 4 = 3 ∧
      c > 0 ∧
      (4 * c - 1) * offset > p ∧
      ((4 * c - 1) * offset - p) ∣ (4 * type3_x p offset * c * p) := by
  classical

  /- STEP 1: Choose α with the unit property -/
  obtain ⟨α, hunit⟩ := exists_alpha_unit p hp hp_mod hp_ge

  /- STEP 2: Build the Fintype instance for the quotient -/
  -- First establish that g(p, α) > 0 (needed for ZMod Fintype)
  have hg_pos : 0 < g p α := Nat.gcd_pos_of_pos_left (Int.natAbs (α^2 + 1)) hp.pos
  haveI : NeZero (g p α) := ⟨Nat.pos_iff_ne_zero.mp hg_pos⟩
  haveI : Fintype ((ℤ × ℤ) ⧸ Lattice p α) :=
    Fintype.ofEquiv (ZMod (g p α)) (quotientEquivZMod p α).symm.toEquiv

  /- STEP 3: Build the QuotientCyclicOfDiag structure -/
  have hcyc : QuotientCyclicOfDiag (Lattice p α) (g p α) :=
    quotient_cyclic_of_lattice p α hp hunit

  /- STEP 4: Apply rectangle intersection -/
  -- The rectangle [1, (p+3)/4] × [1, (p+3)/4] has side length ≥ g(p,α)
  -- since g(p,α) ≤ p and (p+3)/4 > p/4 for large enough p.
  let d := g p α
  let boxSize := (p + 3) / 4

  -- For the rectangle theorem, we need boxSize ≥ d
  have hbox_ge : boxSize ≥ d := by
    -- This requires showing g(p,α) ≤ (p+3)/4
    -- Since g(p,α) | p and p is prime, g(p,α) ∈ {1, p}
    -- If g(p,α) = p, we need p ≤ (p+3)/4, false for p ≥ 5
    -- So we need g(p,α) = 1 or careful case analysis
    sorry

  obtain ⟨pt, hptL, hx0, hx1, hy0, hy1⟩ :=
    rectangle_hits_diagonal_lattice (Lattice p α) d hcyc
      (x₀ := 1) (y₀ := 1) (w := boxSize) (h := boxSize)
      hbox_ge hbox_ge

  /- STEP 5: Decode the lattice point to Type III parameters -/
  -- hx1 : pt.1 ≤ 1 + ↑boxSize, hy1 : pt.2 ≤ 1 + ↑boxSize where boxSize = (p+3)/4
  exact decode_lattice_point_to_type3 p hp hp_mod hp_ge pt.1 pt.2 hx0 hy0 hx1 hy1

end Dyachenko