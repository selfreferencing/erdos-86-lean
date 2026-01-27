/-
  ED2 Window Lattice
  ==================

  Implementation of the ED2 kernel lattice and window lemma (Proposition 9.25)
  from Dyachenko 2025 preprint (arXiv:2511.07465).

  The key objects:
  - ED2KernelLattice: L = {(u,v) : u*b' + v*c' ≡ 0 (mod g)}
  - ed2Alpha: α = gcd(g, b'+c')
  - ed2Step: d' = g/α (the diagonal step)
  - ed2_window_lemma: If H, W ≥ g, then any H×W rectangle contains a lattice point

  NOTE: The window bound is g (not d'). GPT identified a counterexample for d':
  g=3, b'=1, c'=2 gives d'=1 but a 1×1 box [0,1)×[1,2) misses the lattice.
-/

import Mathlib.Data.Int.ModEq
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Tactic

namespace ED2

/-! ## Core Definitions -/

/-- The ED2 kernel lattice: L = {(u,v) : u*b' + v*c' ≡ 0 (mod g)}.
    This is the kernel of the homomorphism φ : ℤ² → ℤ/gℤ given by (u,v) ↦ u*b' + v*c'. -/
def ED2KernelLattice (g : ℕ) (b' c' : ℤ) : AddSubgroup (ℤ × ℤ) where
  carrier := {p | (g : ℤ) ∣ (p.1 * b' + p.2 * c')}
  add_mem' := by
    intros a b ha hb
    simp only [Set.mem_setOf_eq, Prod.fst_add, Prod.snd_add] at *
    have : (a.1 + b.1) * b' + (a.2 + b.2) * c' = (a.1 * b' + a.2 * c') + (b.1 * b' + b.2 * c') := by ring
    rw [this]
    exact dvd_add ha hb
  zero_mem' := by simp
  neg_mem' := by
    intro x hx
    simp only [Set.mem_setOf_eq, Prod.fst_neg, Prod.snd_neg] at *
    have : (-x.1) * b' + (-x.2) * c' = -(x.1 * b' + x.2 * c') := by ring
    rw [this]
    exact dvd_neg.mpr hx

/-- Membership criterion for kernel lattice -/
theorem mem_kernel_iff (g : ℕ) (b' c' : ℤ) (p : ℤ × ℤ) :
    p ∈ ED2KernelLattice g b' c' ↔ (g : ℤ) ∣ (p.1 * b' + p.2 * c') := by
  rfl

/-- α := gcd(g, b'+c') -/
def ed2Alpha (g : ℕ) (b' c' : ℤ) : ℕ := Nat.gcd g (Int.natAbs (b' + c'))

/-- d' := g/α (the diagonal step size) -/
def ed2Step (g : ℕ) (b' c' : ℤ) : ℕ := g / ed2Alpha g b' c'

/-! ## Lattice Vectors -/

/-- v1 = (c', -b') is in the kernel lattice (since c'*b' - b'*c' = 0) -/
theorem v1_mem (g : ℕ) (b' c' : ℤ) : (c', -b') ∈ ED2KernelLattice g b' c' := by
  rw [mem_kernel_iff]
  have h : c' * b' + (-b') * c' = 0 := by ring
  rw [h]; exact dvd_zero _

/-- v2 = (d', d') is in the kernel lattice when d' = g/gcd(g, b'+c').
    Proof: d'*(b'+c') = (g/α)*(b'+c'). Since α | (b'+c'), write (b'+c') = α*m.
    Then (g/α)*α*m = g*m, which is divisible by g. -/
theorem v2_mem (g : ℕ) (hg : 0 < g) (b' c' : ℤ) :
    ((ed2Step g b' c' : ℤ), (ed2Step g b' c' : ℤ)) ∈ ED2KernelLattice g b' c' := by
  rw [mem_kernel_iff]
  have hlin : (ed2Step g b' c' : ℤ) * b' + (ed2Step g b' c' : ℤ) * c'
      = (ed2Step g b' c' : ℤ) * (b' + c') := by ring
  rw [hlin]
  -- d' * (b' + c') is divisible by g
  -- Key facts: α | g, α | |b'+c'|, and d' * α = g
  have hα_dvd_g : ed2Alpha g b' c' ∣ g :=
    Nat.gcd_dvd_left g (Int.natAbs (b' + c'))
  have hα_dvd_bc_nat : ed2Alpha g b' c' ∣ Int.natAbs (b' + c') :=
    Nat.gcd_dvd_right g (Int.natAbs (b' + c'))
  -- d' * α = g (in ℕ)
  have h_step_mul : ed2Step g b' c' * ed2Alpha g b' c' = g :=
    Nat.div_mul_cancel hα_dvd_g
  -- Lift to ℤ: ↑d' * ↑α = ↑g
  have h_int : (↑(ed2Step g b' c') : ℤ) * (↑(ed2Alpha g b' c') : ℤ) = (↑g : ℤ) := by
    exact_mod_cast h_step_mul
  -- ↑α | (b'+c') in ℤ (from α | |b'+c'| in ℕ)
  have hα_dvd_int : (↑(ed2Alpha g b' c') : ℤ) ∣ (b' + c') := by
    obtain ⟨k, hk⟩ := hα_dvd_bc_nat
    have hk_int : (↑(Int.natAbs (b' + c')) : ℤ) = (↑(ed2Alpha g b' c') : ℤ) * (↑k : ℤ) := by
      exact_mod_cast hk
    by_cases h : 0 ≤ b' + c'
    · have hab : (↑(Int.natAbs (b' + c')) : ℤ) = b' + c' := Int.natAbs_of_nonneg h
      rw [hab] at hk_int; exact ⟨↑k, hk_int⟩
    · push_neg at h
      have hab : (↑(Int.natAbs (b' + c')) : ℤ) = -(b' + c') := by omega
      rw [hab] at hk_int
      exact ⟨-(↑k : ℤ), by linarith [mul_neg (↑(ed2Alpha g b' c') : ℤ) (↑k : ℤ)]⟩
  -- Factor: ↑d' * (b'+c') = ↑d' * (↑α * q) = (↑d' * ↑α) * q = ↑g * q
  obtain ⟨q, hq⟩ := hα_dvd_int
  exact ⟨q, by rw [hq, ← mul_assoc, h_int]⟩

/-! ## Unique Representative in Interval

Lemma 9.23: For any d > 0 and starting point x0,
there exists a unique representative in [x0, x0 + d) for each residue class mod d.
-/

/-- For any integer u0 and interval [x0, x0 + d), there exists a unique representative.
    The representative is x0 + ((u0 - x0) % d). -/
theorem exists_unique_Ico_modEq {d : ℤ} (hd : 0 < d) (x0 u0 : ℤ) :
    ∃! u : ℤ, u ∈ Set.Ico x0 (x0 + d) ∧ u ≡ u0 [ZMOD d] := by
  set r := (u0 - x0) % d with hr_def
  have hd0 : d ≠ 0 := ne_of_gt hd
  have r_nonneg : 0 ≤ r := Int.emod_nonneg _ hd0
  have r_lt : r < d := Int.emod_lt_of_pos _ hd
  -- Key: d | (u0 - x0) - r, since r = (u0 - x0) % d
  have hdvd : d ∣ (u0 - x0) - r :=
    ⟨(u0 - x0) / d, by linarith [Int.emod_add_mul_ediv (u0 - x0) d]⟩
  -- So x0 + r ≡ u0 (mod d)
  have hcong : x0 + r ≡ u0 [ZMOD d] := by
    rw [Int.modEq_iff_dvd]
    have : u0 - (x0 + r) = (u0 - x0) - r := by ring
    rw [this]; exact hdvd
  -- Existence
  refine ⟨x0 + r, ⟨⟨by linarith, by linarith⟩, hcong⟩, ?_⟩
  -- Uniqueness
  intro u ⟨⟨hux_le, hux_lt⟩, hu_cong⟩
  have hmod : u ≡ x0 + r [ZMOD d] := hu_cong.trans hcong.symm
  rw [Int.modEq_iff_dvd] at hmod
  obtain ⟨m, hm⟩ := hmod
  -- hm : (x0 + r) - u = d * m, and both in [x0, x0+d)
  have hb1 : -(d : ℤ) < (x0 + r) - u := by linarith
  have hb2 : (x0 + r) - u < d := by linarith
  -- So -d < d*m < d, meaning m = 0
  have hm0 : m = 0 := by
    have hgt : -1 < m := by
      by_contra hle
      push_neg at hle -- hle : m ≤ -1
      have := mul_le_mul_of_nonneg_left hle (le_of_lt hd) -- d * m ≤ d * (-1)
      simp only [mul_neg, mul_one] at this
      linarith
    have hlt : m < 1 := by
      by_contra hle
      push_neg at hle -- hle : 1 ≤ m
      have := mul_le_mul_of_nonneg_left hle (le_of_lt hd) -- d * 1 ≤ d * m
      simp only [mul_one] at this
      linarith
    omega
  have : d * m = 0 := by rw [hm0]; ring
  linarith

/-! ## ED2 Window Lemma

The main geometric result: any rectangle of size H × W where H, W ≥ g
contains at least one point of the kernel lattice.
-/

/-- Axis-parallel rectangle [x0, x0+H) × [y0, y0+W) -/
def rect (x0 y0 : ℤ) (H W : ℕ) : Set (ℤ × ℤ) :=
  {p | p.1 ∈ Set.Ico x0 (x0 + (H : ℤ)) ∧ p.2 ∈ Set.Ico y0 (y0 + (W : ℤ))}

/-- ED2 window lemma: any rectangle of size ≥ g × g contains a lattice point.

The key idea: since gcd(g, c') = 1, for any fixed x, there exists y with
x*b' + y*c' ≡ 0 (mod g), and among g consecutive y-values we find such a y.
So any x in [x0, x0+H) works, and we find y in [y0, y0+W) since W ≥ g. -/
theorem ed2_window_lemma
    {g : ℕ} (hg : 0 < g) {b' c' : ℤ}
    (_hb : Nat.Coprime g (Int.natAbs b')) (hc : Nat.Coprime g (Int.natAbs c')) :
    ∀ {x0 y0 : ℤ} {H W : ℕ},
      g ≤ H →
      g ≤ W →
      ∃ p : ℤ × ℤ, p ∈ ED2KernelLattice g b' c' ∧ p ∈ rect x0 y0 H W := by
  intro x0 y0 H W hH hW
  have hg_int : (0 : ℤ) < (↑g : ℤ) := by exact_mod_cast hg
  -- Bezout: gcd(g, |c'|) = 1, so ↑g * s + c' * t = 1
  -- Get bezout BEFORE set, so set will fold gcdA/gcdB into s/t
  have bezout := Int.gcd_eq_gcd_ab (↑g : ℤ) c'
  rw [show Int.gcd (↑g : ℤ) c' = 1 from hc, Nat.cast_one] at bezout
  set s := Int.gcdA (↑g : ℤ) c'
  set t := Int.gcdB (↑g : ℤ) c'
  -- bezout : (1 : ℤ) = ↑g * s + c' * t (folded by set)
  -- y_sol satisfies x0*b' + y_sol*c' ≡ 0 (mod g)
  -- Use let so ring/linear_combination can see through it
  let y_sol := -(x0 * b') * t
  have hy_sol_dvd : (↑g : ℤ) ∣ (x0 * b' + y_sol * c') :=
    ⟨x0 * b' * s, by linear_combination x0 * b' * bezout⟩
  -- Find y in [y0, y0+g) with y ≡ y_sol (mod g)
  obtain ⟨y, ⟨⟨hy_lo, hy_hi⟩, hy_cong⟩, _⟩ := exists_unique_Ico_modEq hg_int y0 y_sol
  -- The point (x0, y)
  refine ⟨(x0, y), ?_, ?_⟩
  · -- Lattice membership: g | x0*b' + y*c'
    rw [mem_kernel_iff]
    have hshift : x0 * b' + y * c' = (x0 * b' + y_sol * c') + (y - y_sol) * c' := by ring
    rw [hshift]
    apply dvd_add hy_sol_dvd
    apply dvd_mul_of_dvd_left
    rw [show (y : ℤ) - y_sol = -(y_sol - y) from by ring]
    exact dvd_neg.mpr (Int.modEq_iff_dvd.mp hy_cong)
  · -- Rectangle membership: (x0, y) ∈ rect x0 y0 H W
    simp only [rect, Set.mem_setOf_eq, Set.mem_Ico]
    refine ⟨⟨le_refl _, ?_⟩, ⟨hy_lo, ?_⟩⟩
    · -- x0 < x0 + ↑H
      have : (0 : ℤ) < ↑H := by exact_mod_cast lt_of_lt_of_le hg hH
      linarith
    · -- y < y0 + ↑W
      have : (↑g : ℤ) ≤ ↑W := by exact_mod_cast hW
      linarith

/-! ## Index Calculation -/

/-- The quotient ℤ²/L is isomorphic to ℤ/gℤ when gcd(g, b') = 1 -/
theorem kernel_lattice_index (g : ℕ) (hg : 0 < g) (b' c' : ℤ)
    (hb : Nat.Coprime g (Int.natAbs b')) :
    (ED2KernelLattice g b' c').index = g := by
  classical
  haveI : NeZero g := ⟨Nat.ne_of_gt hg⟩
  -- The homomorphism φ : ℤ×ℤ → ℤ/gℤ given by (u,v) ↦ u*b' + v*c' (mod g)
  let φ : (ℤ × ℤ) →+ ZMod g :=
    { toFun := fun p => (p.1 * b' + p.2 * c' : ℤ)
      map_zero' := by simp
      map_add' := by
        intro a b
        simp [mul_add, add_mul, add_assoc, add_comm, add_left_comm] }
  -- Identify ker(φ) with the ED2 kernel lattice
  have hker : φ.ker = ED2KernelLattice g b' c' := by
    ext p
    simp only [AddMonoidHom.mem_ker]
    show ((p.1 * b' + p.2 * c' : ℤ) : ZMod g) = 0 ↔ (g : ℤ) ∣ (p.1 * b' + p.2 * c')
    exact ZMod.intCast_zmod_eq_zero_iff_dvd _ g
  -- Surjectivity of φ from coprimality of g and natAbs(b')
  have hsurj : Function.Surjective φ := by
    intro y
    obtain ⟨z, rfl⟩ := ZMod.intCast_surjective (n := g) y
    -- Bezout: gcd(g, b') = 1 gives g * s + b' * u = 1
    have bezout := Int.gcd_eq_gcd_ab (↑g : ℤ) b'
    rw [show Int.gcd (↑g : ℤ) b' = 1 from by exact_mod_cast hb, Nat.cast_one] at bezout
    set s := Int.gcdA (↑g : ℤ) b'
    set u := Int.gcdB (↑g : ℤ) b'
    -- u * b' ≡ 1 (mod g) in ZMod g
    have hub : ((u * b' : ℤ) : ZMod g) = 1 := by
      rw [show (1 : ZMod g) = ((1 : ℤ) : ZMod g) from by simp,
          ← sub_eq_zero, ← Int.cast_sub, ZMod.intCast_zmod_eq_zero_iff_dvd]
      exact ⟨-s, by linear_combination -bezout⟩
    refine ⟨(z * u, 0), ?_⟩
    have h_eval : φ (z * u, 0) = ((z * (u * b') : ℤ) : ZMod g) := by
      simp only [φ, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
      congr 1; ring
    rw [h_eval, Int.cast_mul, hub, mul_one]
  -- First isomorphism theorem gives (ℤ×ℤ)/ker φ ≃+ ZMod g
  let e : ((ℤ × ℤ) ⧸ φ.ker) ≃+ ZMod g :=
    QuotientAddGroup.quotientKerEquivOfSurjective φ hsurj
  -- Put a Fintype structure on the quotient via the equivalence
  haveI : Fintype ((ℤ × ℤ) ⧸ φ.ker) :=
    Fintype.ofEquiv (ZMod g) e.symm.toEquiv
  -- Compute card(ZMod g) = g using the standard equivalence Fin g ≃ ZMod g
  have hcardZ : Fintype.card (ZMod g) = g := by
    have hc := Fintype.card_congr (ZMod.finEquiv g).toEquiv
    simpa using (hc.symm.trans (by simp))
  -- Rewrite lattice as ker φ and count cosets
  have hker' : ED2KernelLattice g b' c' = φ.ker := by simpa using hker.symm
  rw [hker']
  calc
    φ.ker.index = Fintype.card ((ℤ × ℤ) ⧸ φ.ker) := by
      simpa using (AddSubgroup.index_eq_card (φ.ker))
    _ = Fintype.card (ZMod g) := by
      simpa using (Fintype.card_congr e.toEquiv)
    _ = g := hcardZ

end ED2
