import Mathlib

open scoped Pointwise

namespace AAFramework

/-- `A_m(x)`: the residues mod `m` of the (positive) divisors of `x`. -/
def divisorResidueSet (x m : ℕ) (hm : 0 < m) : Finset (ZMod m) :=
  (Nat.divisors x).image (fun d : ℕ => (d : ZMod m))

/-- Pointwise product set `A·B = {ab | a∈A, b∈B}`. -/
def finsetProd {α : Type*} [DecidableEq α] [Mul α] (A B : Finset α) : Finset α :=
  Finset.image₂ (· * ·) A B

/-- Pointwise negation `-A`. -/
def finsetNeg {α : Type*} [DecidableEq α] [Neg α] (A : Finset α) : Finset α :=
  A.image (fun a => -a)

/-- Divisors of `x^2` have residues in `A_m(x)·A_m(x)`. -/
lemma divisors_sq_residues (x m : ℕ) (hm : 0 < m) (hx : 0 < x) (hgcd : Nat.gcd x m = 1) :
    ∀ d, d ∣ x^2 →
      (d : ZMod m) ∈ finsetProd (divisorResidueSet x m hm) (divisorResidueSet x m hm) := by
  intro d hd
  classical
  -- `hm` and `hgcd` are not needed for this lemma, but we keep them to match the prompt.
  have hx_ne : x ≠ 0 := Nat.ne_of_gt hx
  have hx2_ne : x^2 ≠ 0 := pow_ne_zero 2 hx_ne
  have hd_mem : d ∈ Nat.divisors (x^2) := (Nat.mem_divisors).2 ⟨hd, hx2_ne⟩
  have hd_mem_mul : d ∈ Nat.divisors x * Nat.divisors x := by
    have : d ∈ Nat.divisors (x * x) := by
      simpa [pow_two] using hd_mem
    simpa [Nat.divisors_mul] using this
  rcases (Finset.mem_mul).1 hd_mem_mul with ⟨a, ha, b, hb, rfl⟩
  have haA : (a : ZMod m) ∈ divisorResidueSet x m hm :=
    Finset.mem_image.2 ⟨a, ha, rfl⟩
  have hbA : (b : ZMod m) ∈ divisorResidueSet x m hm :=
    Finset.mem_image.2 ⟨b, hb, rfl⟩
  refine Finset.mem_image₂.2 ?_
  refine ⟨(a : ZMod m), haA, (b : ZMod m), hbA, ?_⟩
  simp

/--
Witness for `-(x mod m)` among residues of divisors of `x^2`
is equivalent to having some divisor-residue `a` with `a ∈ A_m(x)` and `-a ∈ A_m(x)`.
-/
lemma witness_iff_intersection_nonempty
    (x m : ℕ) (hm : 1 < m) (hx : 0 < x) (hgcd : Nat.gcd x m = 1) :
    (∃ d, d ∣ x^2 ∧ ((d : ZMod m) = -(x : ZMod m)))
      ↔
    (divisorResidueSet x m (Nat.zero_lt_of_lt hm) ∩
        finsetNeg (divisorResidueSet x m (Nat.zero_lt_of_lt hm))).Nonempty := by
  classical
  let A : Finset (ZMod m) := divisorResidueSet x m (Nat.zero_lt_of_lt hm)
  constructor
  · intro h
    rcases h with ⟨d, hd_dvd, hd_eq⟩
    have hd_mem : (d : ZMod m) ∈ finsetProd A A :=
      divisors_sq_residues x m (Nat.zero_lt_of_lt hm) hx hgcd d hd_dvd
    have hnegx_mem : (-(x : ZMod m)) ∈ finsetProd A A := by
      simpa [A, hd_eq] using hd_mem
    rcases (Finset.mem_image₂).1 hnegx_mem with ⟨a, haA, b, hbA, hab⟩

    -- pull back to naturals
    rcases (Finset.mem_image).1 haA with ⟨aNat, haNat_div, haEq⟩
    rcases (Finset.mem_image).1 hbA with ⟨bNat, hbNat_div, hbEq⟩
    have hab' : (aNat : ZMod m) * (bNat : ZMod m) = -(x : ZMod m) := by
      have haEq' : a = (aNat : ZMod m) := haEq.symm
      have hbEq' : b = (bNat : ZMod m) := hbEq.symm
      simpa [haEq', hbEq'] using hab

    -- write `x = bNat * cNat`
    have hb_dvd : bNat ∣ x := Nat.dvd_of_mem_divisors hbNat_div
    rcases hb_dvd with ⟨cNat, hx_eq⟩

    -- show `cNat` is also a divisor of `x`
    have hx_ne : x ≠ 0 := Nat.ne_of_gt hx
    have hc_dvd : cNat ∣ x := by
      refine ⟨bNat, ?_⟩
      simpa [Nat.mul_comm] using hx_eq
    have hc_mem : cNat ∈ Nat.divisors x := (Nat.mem_divisors).2 ⟨hc_dvd, hx_ne⟩

    -- cancel `bNat` using invertibility mod m (via `gcd(x,m)=1`)
    have hcop : Nat.Coprime x m := by simpa [Nat.Coprime] using hgcd
    have hb_coprime : Nat.Coprime bNat m := hcop.coprime_dvd_left hb_dvd
    have hb_mul_inv :
        ((bNat : ZMod m) * (bNat : ZMod m)⁻¹) = (1 : ZMod m) :=
      ZMod.coe_mul_inv_eq_one bNat hb_coprime

    have ha_eq_neg_c : (aNat : ZMod m) = -(cNat : ZMod m) := by
      have hab_mul_inv := congrArg (fun t => t * ((bNat : ZMod m)⁻¹)) hab'
      simpa [hx_eq, mul_assoc, mul_left_comm, mul_comm, hb_mul_inv] using hab_mul_inv

    -- build a witness in the intersection
    refine ⟨(aNat : ZMod m), ?_⟩
    have ha_memA : (aNat : ZMod m) ∈ A :=
      Finset.mem_image.2 ⟨aNat, haNat_div, rfl⟩
    have hc_memA : (cNat : ZMod m) ∈ A :=
      Finset.mem_image.2 ⟨cNat, hc_mem, rfl⟩
    have ha_memNegA : (aNat : ZMod m) ∈ finsetNeg A := by
      -- `finsetNeg A = A.image (fun t => -t)`
      refine Finset.mem_image.2 ?_
      refine ⟨(cNat : ZMod m), hc_memA, ?_⟩
      simpa [finsetNeg] using ha_eq_neg_c.symm
    exact Finset.mem_inter.2 ⟨ha_memA, ha_memNegA⟩

  · intro hNonempty
    rcases hNonempty with ⟨z, hz⟩
    have hzA : z ∈ A := (Finset.mem_inter.1 hz).1
    have hzNegA : z ∈ finsetNeg A := (Finset.mem_inter.1 hz).2

    rcases (Finset.mem_image).1 hzA with ⟨aNat, haNat_div, haEq⟩
    have hz_def : z = (aNat : ZMod m) := haEq.symm

    rcases (Finset.mem_image).1 hzNegA with ⟨bRes, hbRes_memA, hbResEq⟩
    -- `hbResEq : -bRes = z`
    rcases (Finset.mem_image).1 hbRes_memA with ⟨bNat, hbNat_div, hbNatEq⟩
    have hbRes_def : bRes = (bNat : ZMod m) := hbNatEq.symm

    have hab_cong : (aNat : ZMod m) = -(bNat : ZMod m) := by
      have : -(bNat : ZMod m) = (aNat : ZMod m) := by
        simpa [hz_def, hbRes_def] using hbResEq
      simpa using this.symm

    have hb_dvd : bNat ∣ x := Nat.dvd_of_mem_divisors hbNat_div
    rcases hb_dvd with ⟨cNat, hx_eq⟩
    have ha_dvd : aNat ∣ x := Nat.dvd_of_mem_divisors haNat_div
    have hc_dvd : cNat ∣ x := by
      refine ⟨bNat, ?_⟩
      simpa [Nat.mul_comm] using hx_eq

    have hdiv : aNat * cNat ∣ x * x := Nat.mul_dvd_mul ha_dvd hc_dvd
    have hdiv2 : aNat * cNat ∣ x^2 := by
      simpa [pow_two] using hdiv

    refine ⟨aNat * cNat, hdiv2, ?_⟩
    calc
      ((aNat * cNat : ℕ) : ZMod m)
          = (aNat : ZMod m) * (cNat : ZMod m) := by simp [Nat.cast_mul]
      _ = (-(bNat : ZMod m)) * (cNat : ZMod m) := by simpa [hab_cong]
      _ = -((bNat : ZMod m) * (cNat : ZMod m)) := by simp [neg_mul]
      _ = -(x : ZMod m) := by
        simpa [hx_eq, Nat.cast_mul]

/-- `A_m(x)` as a finset of units of `ZMod m`, assuming `gcd(x,m)=1`. -/
def divisorUnitSet (x m : ℕ) (hgcd : Nat.gcd x m = 1) : Finset (ZMod m)ˣ :=
  let hcop : Nat.Coprime x m := by
    simpa [Nat.Coprime] using hgcd
  (Nat.divisors x).attach.image (fun d =>
    ZMod.unitOfCoprime d.1 (hcop.coprime_dvd_left (Nat.dvd_of_mem_divisors d.2)))

/-- (General) Saturation lemma: a subset of a finite group larger than half the group
has product set equal to `univ`. -/
lemma prod_set_saturates {G : Type*} [Group G] [Fintype G] [DecidableEq G]
    (A : Finset G) (hA : 2 * A.card > Fintype.card G) :
    finsetProd A A = Finset.univ := by
  classical
  ext g
  constructor
  · intro _; simp
  · intro _
    let B : Finset G := A.image (fun a => g * a⁻¹)
    have h_inj : Function.Injective (fun a : G => g * a⁻¹) := by
      intro a1 a2 h
      have : a1⁻¹ = a2⁻¹ := by
        exact mul_left_cancel h
      exact inv_injective this
    have hBcard : B.card = A.card := by
      simpa [B] using
        (Finset.card_image_of_injective (s := A) (f := fun a : G => g * a⁻¹) h_inj)

    have hInter : (A ∩ B).Nonempty := by
      by_contra hEmpty
      have hInterEmpty : A ∩ B = ∅ := (Finset.not_nonempty_iff_eq_empty).1 hEmpty
      have h_union_le : (A ∪ B).card ≤ Fintype.card G :=
        Finset.card_le_univ (A ∪ B)
      have h_card_union : (A ∪ B).card = A.card + B.card := by
        have h := Finset.card_union_add_card_inter A B
        have h' : (A ∪ B).card + 0 = A.card + B.card := by
          simpa [hInterEmpty] using h
        simpa using h'
      have h_sum_le : A.card + A.card ≤ Fintype.card G := by
        have : A.card + B.card ≤ Fintype.card G := by
          simpa [h_card_union] using h_union_le
        simpa [hBcard] using this
      have hA' : Fintype.card G < A.card + A.card := by
        simpa [two_mul] using hA
      exact (not_lt_of_ge h_sum_le) hA'

    rcases hInter with ⟨a, haInter⟩
    have haA : a ∈ A := (Finset.mem_inter.1 haInter).1
    have haB : a ∈ B := (Finset.mem_inter.1 haInter).2
    rcases (Finset.mem_image).1 haB with ⟨b, hbA, hbEq⟩
    have hgb : g = a * b := by
      have := congrArg (fun t => t * b) hbEq
      simpa [mul_assoc] using this
    have habg : a * b = g := by simpa using hgb.symm
    refine Finset.mem_image₂.2 ?_
    exact ⟨a, haA, b, hbA, habg⟩

/--
**Important correction**: the "A·A saturates" argument applies to a *finite group*.
For modular arithmetic this should be the multiplicative group of units `(ZMod m)ˣ`
(not `ZMod m` under multiplication, which is not a group when `m` is not prime).
-/
lemma saturation_lemma (m : ℕ) [Fact (0 < m)]
    (A : Finset (ZMod m)ˣ)
    (hA : 2 * A.card > Fintype.card (ZMod m)ˣ) :
    finsetProd A A = (Finset.univ : Finset (ZMod m)ˣ) := by
  simpa using (prod_set_saturates (A := A) hA)

/--
If `A_m(x)` (viewed inside the unit group) contains more than half of the units of `ZMod m`,
then there exists a divisor `d ∣ x^2` with `d ≡ -x (mod m)`.

This is the standard "A·A saturates the group" step of the framework.
-/
theorem witness_of_large_divisor_set
    (x m : ℕ) (hx : 0 < x) (hgcd : Nat.gcd x m = 1) [Fact (0 < m)]
    (hA : 2 * (divisorUnitSet x m hgcd).card > Fintype.card (ZMod m)ˣ) :
    ∃ d, d ∣ x^2 ∧ ((d : ZMod m) = -(x : ZMod m)) := by
  classical
  have hcop : Nat.Coprime x m := by
    simpa [Nat.Coprime] using hgcd
  let ux : (ZMod m)ˣ := ZMod.unitOfCoprime x hcop

  have hSat :
      finsetProd (divisorUnitSet x m hgcd) (divisorUnitSet x m hgcd)
        = (Finset.univ : Finset (ZMod m)ˣ) :=
    saturation_lemma m (A := divisorUnitSet x m hgcd) hA

  have hneg_mem :
      (-(ux) : (ZMod m)ˣ) ∈
        finsetProd (divisorUnitSet x m hgcd) (divisorUnitSet x m hgcd) := by
    have : (-(ux) : (ZMod m)ˣ) ∈ (Finset.univ : Finset (ZMod m)ˣ) :=
      Finset.mem_univ _
    simpa [hSat] using this

  rcases (Finset.mem_image₂).1 hneg_mem with ⟨u, hu, v, hv, huv⟩
  rcases (Finset.mem_image).1 hu with ⟨aSub, _, rfl⟩
  rcases (Finset.mem_image).1 hv with ⟨bSub, _, rfl⟩

  -- underlying natural divisors
  let a : ℕ := aSub.1
  let b : ℕ := bSub.1
  have ha_div : a ∣ x := Nat.dvd_of_mem_divisors aSub.2
  have hb_div : b ∣ x := Nat.dvd_of_mem_divisors bSub.2

  refine ⟨a * b, ?_, ?_⟩
  · have : a * b ∣ x * x := Nat.mul_dvd_mul ha_div hb_div
    simpa [pow_two] using this
  · have huv_zmod : (a : ZMod m) * (b : ZMod m) = -(x : ZMod m) := by
      have := congrArg (fun w : (ZMod m)ˣ => (w : ZMod m)) huv
      simpa [ux, a, b] using this
    simpa [Nat.cast_mul] using huv_zmod

end AAFramework
