/-
  Zeroless/Fourier_Proven.lean
  Fourier Bridge: Killed-index uniformity + Discrepancy + Good ratio + Geometric decay

  Proved results (0 sorry):
  - F5: Survivor subsets S4/S5/S_all, killed_index (kills + unique)
  - F3: Character orthogonality on Z/5Z
  - F4: Discrepancy bound via Fourier inversion
  - F6: Good ratio lower bound
  - F7: Geometric decay computation 4*(91/100)^90 < 1

  Single axiom: no_zeroless_k_ge_91 (OPEN PROBLEM, see note below)

  Status (January 2026):
  The original proof strategy attempted to show that a "forced-tail" survivor count
  decays geometrically at each digit level with ratio <= 91/100. This strategy is
  FUNDAMENTALLY FLAWED: the net growth factor per level is 5 * (9/10) = 4.5 > 1,
  so the survivor count grows as ~4.5^k rather than decaying. This barrier appears
  in every digit-by-digit formulation we tested (forced-tail, covering congruences,
  SAT certificates, Fourier spectrum). The axiom no_zeroless_k_ge_91 represents an
  open problem in mathematics. The 86 conjecture itself remains open as of 2026.

  A previous axiom char_sum_bounded was REMOVED because it is provably false:
  the character sum grows as 4*5^(k-1), unbounded. See git history for the
  original statement.

  Dependency: F5 (defs + proofs) → F3 (char ortho) → F4 (discrepancy) → F6 (good ratio)
              → F7 (geometric decay)
-/

import Zeroless.FiveAdic_Extended
-- import Zeroless.TransferOperator  -- TODO: re-enable after fixing ring_nf errors

namespace Zeroless

open scoped BigOperators

noncomputable section

/-- Primitive 5th root of unity (local copy; canonical version in TransferOperator.lean) -/
noncomputable def ω' : ℂ := Complex.exp (2 * Real.pi * Complex.I / 5)

/-! ## Section 1: Survivor Subsets (F5) -/

/-- 4-child survivors: nonzero top digit AND nonzero step (lo mod 5 ≠ 0) -/
def S4 (k : ℕ) : Finset (ZMod (5^(k+1))) :=
  Finset.univ.filter fun u =>
    (top_digit k u).val ≠ 0 ∧ u.val % 5^k % 5 ≠ 0

/-- 5-child survivors: nonzero top digit AND zero step (lo mod 5 = 0) -/
def S5 (k : ℕ) : Finset (ZMod (5^(k+1))) :=
  Finset.univ.filter fun u =>
    (top_digit k u).val ≠ 0 ∧ u.val % 5^k % 5 = 0

/-- All survivors: nonzero top digit -/
def S_all (k : ℕ) : Finset (ZMod (5^(k+1))) :=
  Finset.univ.filter fun u => (top_digit k u).val ≠ 0

/-- S4 and S5 are disjoint (step ≠ 0 vs step = 0) -/
theorem S4_S5_disjoint (k : ℕ) : Disjoint (S4 k) (S5 k) := by
  apply Finset.disjoint_left.mpr
  intro u hu hs5
  simp only [S4, Finset.mem_filter, Finset.mem_univ, true_and] at hu
  simp only [S5, Finset.mem_filter, Finset.mem_univ, true_and] at hs5
  exact hu.2 hs5.2

/-- S4 ∪ S5 = S_all (every survivor has step = 0 or step ≠ 0) -/
theorem S4_union_S5 (k : ℕ) : S4 k ∪ S5 k = S_all k := by
  ext u
  simp only [S4, S5, S_all, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
  · intro h
    by_cases hstep : u.val % 5^k % 5 = 0
    · right; exact ⟨h, hstep⟩
    · left; exact ⟨h, hstep⟩

/-! ## Section 2: Killed Index (F5) -/

/-- Killed index: for a 4-child survivor u, the unique j ∈ Fin 5 such that
    u * m^j has top digit = 0.
    Formula: j₀ = -(hi) * (step₅)⁻¹ in ZMod 5,
    where hi = u.val / 5^k, step₅ = ((u.val % 5^k) % 5 : ZMod 5) * 3. -/
def killed_index (k : ℕ) (u : ZMod (5^(k+1))) : Fin 5 :=
  let hi : ℕ := u.val / 5^k
  let lo_mod5 : ℕ := u.val % 5^k % 5
  let step5 : ZMod 5 := ((lo_mod5 : ℕ) : ZMod 5) * (3 : ZMod 5)
  let hi5 : ZMod 5 := (hi : ZMod 5)
  let j0z : ZMod 5 := (-hi5) * step5⁻¹
  ⟨j0z.val, j0z.val_lt⟩

/-- killed_index identifies a dead child: u * m^{killed_index} does NOT survive.

    Proof: The top digit of u * m^j is (hi + lo * j * 3) % 5 (by product_zmod_eq chain).
    At j = killed_index, this equals hi + step5 * ((-hi) * step5⁻¹) = hi - hi = 0 in ZMod 5.
    Since the result is 0 mod 5 and < 5, it equals 0, so the top digit is 0. -/
theorem killed_index_kills (k : ℕ) (hk : k ≥ 1) (u : ZMod (5^(k+1)))
    (hu : u ∈ S4 k) :
    ¬survives k (u * (m k)^(killed_index k u).val) := by
  classical
  -- Extract S4 membership: top digit ≠ 0, step ≠ 0
  simp only [S4, Finset.mem_filter, Finset.mem_univ, true_and] at hu
  obtain ⟨_hhi_ne, hstep_ne⟩ := hu
  -- Setup shorthands (using let, not set, to avoid free-variable issues with decide/simpa)
  let q : ℕ := 5^k
  let hi : ℕ := u.val / q
  let lo : ℕ := u.val % q
  let lo_mod5 : ℕ := lo % 5
  let j0 := killed_index k u
  let b : ℕ := (hi + lo * j0.val * 3) % 5
  -- Positivity
  have hq_pos : 0 < q := Nat.pos_of_ne_zero (by positivity)
  have hlo_lt : lo < q := Nat.mod_lt u.val hq_pos
  have hb_lt5 : b < 5 := Nat.mod_lt _ (by decide)
  -- Step 1: Product decomposition (from product_zmod_eq)
  have hprod : u * (m k : ZMod (5^(k+1)))^j0.val =
      (lo : ZMod (5^(k+1))) + (b : ZMod (5^(k+1))) * (q : ZMod (5^(k+1))) :=
    product_zmod_eq k hk u j0.val
  -- Step 2: Compute .val (from val_of_small_nat)
  have hcast : (lo : ZMod (5^(k+1))) + (b : ZMod (5^(k+1))) * (q : ZMod (5^(k+1))) =
      ((lo + b * q : ℕ) : ZMod (5^(k+1))) := by push_cast; ring
  have hval : (u * (m k : ZMod (5^(k+1)))^j0.val).val = lo + b * q := by
    rw [hprod, hcast]; exact val_of_small_nat k lo b hlo_lt hb_lt5
  -- Step 3: Division gives b (from nat_add_mul_div)
  have hdiv : (u * (m k : ZMod (5^(k+1)))^j0.val).val / q = b := by
    rw [hval]; exact nat_add_mul_div lo q b hlo_lt hq_pos
  -- The top digit of the product is b
  have htop : (top_digit k (u * (m k)^j0.val)).val = b := hdiv
  -- Step 4: Show b = 0 using ZMod 5 algebra
  -- 4a: Cast b to ZMod 5
  have hb_zmod5 : (b : ZMod 5) =
      (hi : ZMod 5) + ((lo_mod5 : ℕ) : ZMod 5) * (3 : ZMod 5) * (j0.val : ZMod 5) :=
    mod_cast_eq_digit hi lo j0.val
  -- 4b: j0.val in ZMod 5 = (-hi) * step5⁻¹ (from killed_index definition)
  haveI : Fact (Nat.Prime 5) := ⟨by decide⟩
  let step5 : ZMod 5 := ((lo_mod5 : ℕ) : ZMod 5) * (3 : ZMod 5)
  let hi5 : ZMod 5 := (hi : ZMod 5)
  let j0z : ZMod 5 := (-hi5) * step5⁻¹
  have hj0z_cast : (j0.val : ZMod 5) = j0z := by
    refine Fin.val_injective ?_
    show (j0.val : ZMod 5).val = j0z.val
    rw [ZMod.val_natCast]
    change j0z.val % 5 = j0z.val
    exact Nat.mod_eq_of_lt j0z.val_lt
  -- 4c: step5 ≠ 0
  have hlo5_ne : ((lo_mod5 : ℕ) : ZMod 5) ≠ 0 := by
    intro h0
    have hdvd : 5 ∣ lo_mod5 := by
      simpa using (ZMod.natCast_zmod_eq_zero_iff_dvd lo_mod5 5).1 h0
    have hlt : lo_mod5 < 5 := Nat.mod_lt lo (by decide)
    exact hstep_ne (Nat.eq_zero_of_dvd_of_lt hdvd hlt)
  have h3_ne : (3 : ZMod 5) ≠ 0 := by
    intro h
    have : 5 ∣ (3 : ℕ) := by
      have := (ZMod.natCast_zmod_eq_zero_iff_dvd 3 5).mp
      exact this (by exact_mod_cast h)
    omega
  have hstep_ne' : step5 ≠ 0 := mul_ne_zero hlo5_ne h3_ne
  have hinv : step5 * step5⁻¹ = 1 := mul_inv_cancel₀ hstep_ne'
  -- 4d: Algebraic cancellation: hi + step5 * ((-hi) * step5⁻¹) = 0
  have hb_zero_zmod : (b : ZMod 5) = 0 := by
    rw [hb_zmod5, hj0z_cast]
    show hi5 + step5 * ((-hi5) * step5⁻¹) = 0
    calc hi5 + step5 * ((-hi5) * step5⁻¹)
        = hi5 + (-hi5) * (step5 * step5⁻¹) := by ring
      _ = hi5 + (-hi5) * 1 := by rw [hinv]
      _ = 0 := by ring
  -- 4e: b = 0 in ℕ (from cast = 0 and b < 5)
  have hb_zero : b = 0 := by
    by_contra hne
    exact ((ne_zero_iff_cast_ne_zero b hb_lt5).mp hne) hb_zero_zmod
  -- Step 5: Conclude ¬survives (top digit = 0)
  show ¬survives k (u * (m k)^j0.val)
  unfold survives
  rw [htop, hb_zero]
  simp

/-- killed_index is the UNIQUE dead child.

    Proof: If u * m^j doesn't survive, the top digit (hi + lo * j * 3) % 5 = 0.
    In ZMod 5: step5 * j = -hi. Since step5 ≠ 0 (u ∈ S4), j = (-hi) * step5⁻¹ = killed_index. -/
theorem killed_index_unique (k : ℕ) (hk : k ≥ 1) (u : ZMod (5^(k+1)))
    (hu : u ∈ S4 k) (j : Fin 5) (hj : ¬survives k (u * (m k)^j.val)) :
    j = killed_index k u := by
  classical
  -- Extract S4 membership
  simp only [S4, Finset.mem_filter, Finset.mem_univ, true_and] at hu
  obtain ⟨_hhi_ne, hstep_ne⟩ := hu
  -- Setup shorthands (using let, not set)
  let q : ℕ := 5^k
  let hi : ℕ := u.val / q
  let lo : ℕ := u.val % q
  let lo_mod5 : ℕ := lo % 5
  let j0 := killed_index k u
  let bj : ℕ := (hi + lo * j.val * 3) % 5
  -- Positivity
  have hq_pos : 0 < q := Nat.pos_of_ne_zero (by positivity)
  have hlo_lt : lo < q := Nat.mod_lt u.val hq_pos
  have hbj_lt5 : bj < 5 := Nat.mod_lt _ (by decide)
  -- Step 1: Product decomposition for j
  have hprod : u * (m k : ZMod (5^(k+1)))^j.val =
      (lo : ZMod (5^(k+1))) + (bj : ZMod (5^(k+1))) * (q : ZMod (5^(k+1))) :=
    product_zmod_eq k hk u j.val
  have hcast : (lo : ZMod (5^(k+1))) + (bj : ZMod (5^(k+1))) * (q : ZMod (5^(k+1))) =
      ((lo + bj * q : ℕ) : ZMod (5^(k+1))) := by push_cast; ring
  have hval : (u * (m k : ZMod (5^(k+1)))^j.val).val = lo + bj * q := by
    rw [hprod, hcast]; exact val_of_small_nat k lo bj hlo_lt hbj_lt5
  have hdiv : (u * (m k : ZMod (5^(k+1)))^j.val).val / q = bj := by
    rw [hval]; exact nat_add_mul_div lo q bj hlo_lt hq_pos
  -- Step 2: From ¬survives, get bj = 0
  have htop : (top_digit k (u * (m k)^j.val)).val = bj := hdiv
  have hbj_zero : bj = 0 := by
    by_contra hne
    apply hj
    show (top_digit k (u * (m k)^j.val)).val ≠ 0
    rw [htop]; exact hne
  -- Step 3: From bj = 0, get step5 * j = -hi in ZMod 5
  haveI : Fact (Nat.Prime 5) := ⟨by decide⟩
  let step5 : ZMod 5 := ((lo_mod5 : ℕ) : ZMod 5) * (3 : ZMod 5)
  let hi5 : ZMod 5 := (hi : ZMod 5)
  -- Cast bj to ZMod 5
  have hbj_zmod5 : (bj : ZMod 5) =
      hi5 + step5 * (j.val : ZMod 5) :=
    mod_cast_eq_digit hi lo j.val
  -- bj = 0 implies digit(j) = 0 in ZMod 5
  have hdigit_zero : hi5 + step5 * (j.val : ZMod 5) = 0 := by
    rw [← hbj_zmod5, hbj_zero]; simp
  -- Solve for j: step5 * j = -hi5
  have hj_solve : step5 * (j.val : ZMod 5) = -hi5 := by
    linear_combination hdigit_zero
  -- step5 ≠ 0
  have hlo5_ne : ((lo_mod5 : ℕ) : ZMod 5) ≠ 0 := by
    intro h0
    have hdvd : 5 ∣ lo_mod5 := by
      simpa using (ZMod.natCast_zmod_eq_zero_iff_dvd lo_mod5 5).1 h0
    have hlt : lo_mod5 < 5 := Nat.mod_lt lo (by decide)
    exact hstep_ne (Nat.eq_zero_of_dvd_of_lt hdvd hlt)
  have h3_ne : (3 : ZMod 5) ≠ 0 := by
    intro h
    have : 5 ∣ (3 : ℕ) := by
      have := (ZMod.natCast_zmod_eq_zero_iff_dvd 3 5).mp
      exact this (by exact_mod_cast h)
    omega
  have hstep_ne' : step5 ≠ 0 := mul_ne_zero hlo5_ne h3_ne
  -- j = (-hi5) * step5⁻¹ in ZMod 5
  have hinv : step5⁻¹ * step5 = 1 := inv_mul_cancel₀ hstep_ne'
  have hj_zmod : (j.val : ZMod 5) = (-hi5) * step5⁻¹ := by
    calc (j.val : ZMod 5)
        = step5⁻¹ * (step5 * (j.val : ZMod 5)) := by
            rw [← mul_assoc, hinv, one_mul]
      _ = step5⁻¹ * (-hi5) := by rw [hj_solve]
      _ = (-hi5) * step5⁻¹ := by ring
  -- j0 = killed_index has the same ZMod 5 value
  let j0z : ZMod 5 := (-hi5) * step5⁻¹
  have hj0_zmod : (j0.val : ZMod 5) = j0z := by
    refine Fin.val_injective ?_
    show (j0.val : ZMod 5).val = j0z.val
    rw [ZMod.val_natCast]
    change j0z.val % 5 = j0z.val
    exact Nat.mod_eq_of_lt j0z.val_lt
  -- Both j and j0 have values < 5 and equal casts to ZMod 5, so they're equal
  apply Fin.ext
  have hzmod_eq : (j.val : ZMod 5) = (j0.val : ZMod 5) := by
    rw [hj_zmod, hj0_zmod]
  have hj_lt : j.val < 5 := j.isLt
  have hj0_lt : j0.val < 5 := j0.isLt
  calc j.val
      = (j.val : ZMod 5).val := by
          rw [ZMod.val_natCast]; exact (Nat.mod_eq_of_lt hj_lt).symm
    _ = (j0.val : ZMod 5).val := by rw [hzmod_eq]
    _ = j0.val := by
          rw [ZMod.val_natCast]; exact Nat.mod_eq_of_lt hj0_lt

/-! ## Section 3: Character Orthogonality (F3) -/

theorem omega'_pow_five : ω' ^ 5 = 1 := by
  simpa [ω'] using (Complex.isPrimitiveRoot_exp 5 (by norm_num)).pow_eq_one

/-- Twisted sum vanishes for nonzero ℓ: ∑_{j=0}^4 ω'^{ℓj} = 0.
    Proof: geometric series telescoping. Let ξ = ω'^ℓ. Then ξ^5 = 1 and ξ ≠ 1.
    (ξ^0 + ξ^1 + ξ^2 + ξ^3 + ξ^4)(ξ - 1) = ξ^5 - 1 = 0,
    and ξ - 1 ≠ 0, so the sum = 0. -/
theorem twisted_sum_zero' (ℓ : ZMod 5) (hℓ : ℓ ≠ 0) :
    (∑ j : Fin 5, ω' ^ (ℓ.val * j.val)) = 0 := by
  -- Rewrite as geometric series of ξ = ω'^ℓ
  have hξ_eq : ∀ j : Fin 5, ω' ^ (ℓ.val * j.val) = (ω' ^ ℓ.val) ^ j.val := by
    intro j; exact pow_mul ω' ℓ.val j.val
  simp_rw [hξ_eq]
  -- ξ^5 = 1
  have hξ5 : (ω' ^ ℓ.val) ^ 5 = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, omega'_pow_five, one_pow]
  -- ξ ≠ 1 (ω' is primitive 5th root; 0 < ℓ.val < 5)
  have hprim : IsPrimitiveRoot ω' 5 := by
    simpa [ω'] using Complex.isPrimitiveRoot_exp 5 (by norm_num)
  have hℓ_ne : ℓ.val ≠ 0 := by
    intro h; exact hℓ ((ZMod.val_eq_zero ℓ).mp h)
  have hξ_ne : ω' ^ ℓ.val ≠ 1 :=
    hprim.pow_ne_one_of_pos_of_lt hℓ_ne (ZMod.val_lt ℓ)
  -- Telescoping: (sum) * (ξ - 1) = ξ^5 - 1 = 0
  suffices h : (∑ j : Fin 5, (ω' ^ ℓ.val) ^ j.val) * (ω' ^ ℓ.val - 1) = 0 by
    exact (mul_eq_zero.mp h).resolve_right (sub_ne_zero.mpr hξ_ne)
  simp only [Fin.sum_univ_five]
  simp only [show (0 : Fin 5).val = 0 from rfl,
             show (1 : Fin 5).val = 1 from rfl,
             show (2 : Fin 5).val = 2 from rfl,
             show (3 : Fin 5).val = 3 from rfl,
             show (4 : Fin 5).val = 4 from rfl]
  linear_combination hξ5

/-- Character orthogonality on Z/5Z:
    ∑_{ℓ : ZMod 5} ω'^{ℓ(a-b)} = if a = b then 5 else 0 -/
theorem char_ortho (a b : Fin 5) :
    (∑ ℓ : ZMod 5, (ω' ^ (ℓ.val * a.val)) * (ω' ^ (ℓ.val * b.val))⁻¹) =
      if a = b then 5 else 0 := by
  classical
  by_cases hab : a = b
  · subst hab
    have hω : ω' ≠ 0 := by simp [ω']
    simp [hω]
  · have hω : ω' ≠ 0 := by simp [ω']
    -- Lift a, b to ZMod 5 to avoid Fin 5 / ZMod 5 coercion issues
    let a' : ZMod 5 := a
    let b' : ZMod 5 := b
    let diff : ZMod 5 := a' - b'
    have hd : diff ≠ 0 := by
      intro hd0
      apply hab
      have h : a' = b' := sub_eq_zero.mp hd0
      exact_mod_cast h
    have hval : (diff.val + b.val) % 5 = a.val := by
      have hdiff : diff + b' = a' := sub_add_cancel a' b'
      have h := congrArg ZMod.val hdiff
      simp only [ZMod.val_add] at h
      exact h
    have hMul : ω' ^ diff.val * ω' ^ b.val = ω' ^ a.val := by
      calc
        ω' ^ diff.val * ω' ^ b.val
          = ω' ^ (diff.val + b.val) := by
              simpa using (pow_add ω' diff.val b.val).symm
        _ = ω' ^ ((diff.val + b.val) % 5) := by
              simpa using
                (pow_eq_pow_mod (a := ω') (n := 5) (m := diff.val + b.val) omega'_pow_five)
        _ = ω' ^ a.val := by simpa [hval]
    have hBase : ω' ^ a.val * (ω' ^ b.val)⁻¹ = ω' ^ diff.val := by
      have hb0 : ω' ^ b.val ≠ 0 := pow_ne_zero _ hω
      calc
        ω' ^ a.val * (ω' ^ b.val)⁻¹
          = (ω' ^ diff.val * ω' ^ b.val) * (ω' ^ b.val)⁻¹ := by simpa [hMul]
        _ = ω' ^ diff.val := by simp [mul_assoc, hb0]
    have h_integrand :
        ∀ ℓ : ZMod 5,
          (ω' ^ (ℓ.val * a.val)) * (ω' ^ (ℓ.val * b.val))⁻¹ =
          ω' ^ (diff.val * ℓ.val) := by
      intro ℓ
      calc
        (ω' ^ (ℓ.val * a.val)) * (ω' ^ (ℓ.val * b.val))⁻¹
          = ((ω' ^ a.val) ^ ℓ.val) * ((ω' ^ b.val) ^ ℓ.val)⁻¹ := by
              rw [pow_mul', pow_mul']
        _ = ((ω' ^ a.val) ^ ℓ.val) * (((ω' ^ b.val)⁻¹) ^ ℓ.val) := by
              rw [(inv_pow (ω' ^ b.val) ℓ.val).symm]
        _ = ((ω' ^ a.val) * (ω' ^ b.val)⁻¹) ^ ℓ.val := by
              simpa using (mul_pow (ω' ^ a.val) ((ω' ^ b.val)⁻¹) ℓ.val).symm
        _ = (ω' ^ diff.val) ^ ℓ.val := by simp [hBase]
        _ = ω' ^ (diff.val * ℓ.val) := by
              simpa using (pow_mul ω' diff.val ℓ.val).symm
    calc
      (∑ ℓ : ZMod 5, (ω' ^ (ℓ.val * a.val)) * (ω' ^ (ℓ.val * b.val))⁻¹)
        = ∑ ℓ : ZMod 5, ω' ^ (diff.val * ℓ.val) := by simp [h_integrand]
      _ = 0 := by simpa using (twisted_sum_zero' diff hd)
      _ = if a = b then 5 else 0 := by simp [hab]

/-! ## Section 4: Note on Removed Axiom

The axiom `char_sum_bounded` was previously stated here, claiming:
  ∃ C : ℝ, 0 < C ∧ ∀ k ≥ 1, ∀ ℓ ≠ 0,
    ‖∑ u ∈ S4 k, ω' ^ (ℓ.val * (killed_index k u).val)‖ ≤ C

This axiom is **FALSE**. The sum grows as 4 * 5^(k-1), which is unbounded.
The underlying issue: |S4 k| grows as ~4 * 5^k, and the killed_index values
do not cancel sufficiently. The transfer operator B4(ℓ)^n = (-1)^{n-1} B4(ℓ)
result is correct, but it bounds a DIFFERENT quantity (matrix entries of B4^n)
than the sum over all of S4(k) (which has 4*5^k elements at level k).

The theorems below (discrepancy_from_char_bound, good_ratio_lower) remain
correct: they take character sum bounds as hypotheses, not from this axiom.
They would apply IF a uniform bound existed, but it does not.
-/

/-! ## Section 5: Discrepancy Bound (F4) -/

/-- Discrepancy bound: if character sums over a Finset are bounded by C,
    then the count with any given value deviates from |S|/5 by at most 4C/5.

    Proof: Fourier inversion on Z/5Z gives the counting identity.
    The ℓ=0 term is |S|/5, the other 4 terms each bounded by C. -/
theorem discrepancy_from_char_bound {α : Type*} [DecidableEq α]
    (S : Finset α) (g : α → Fin 5) (a : Fin 5)
    (C : ℝ) (hC : C ≥ 0)
    (hbound : ∀ ℓ : ZMod 5, ℓ ≠ 0 →
      ‖(∑ x ∈ S, (ω' ^ (ℓ.val * (g x).val) : ℂ))‖ ≤ C) :
    |((S.filter (fun x => g x = a)).card : ℝ) - (S.card : ℝ) / 5| ≤ 4 * C / 5 := by
  classical
  -- ‖ω'‖ = 1 (primitive root on unit circle)
  have hprim : IsPrimitiveRoot ω' 5 := by
    simpa [ω'] using Complex.isPrimitiveRoot_exp 5 (by norm_num)
  have hω_norm : ‖ω'‖ = 1 := hprim.norm'_eq_one (by norm_num)
  -- Abbreviations
  let cnt := (S.filter (fun x => g x = a)).card
  let F : ZMod 5 → ℂ := fun ℓ =>
    (ω' ^ (ℓ.val * a.val))⁻¹ * ∑ x ∈ S, ω' ^ (ℓ.val * (g x).val)
  -- Step 1: Fourier counting identity: ∑_ℓ F(ℓ) = 5 * cnt
  have hfourier : ∑ ℓ : ZMod 5, F ℓ = 5 * (cnt : ℂ) := by
    -- char_ortho gives ∑_ℓ ω^{ℓb} (ω^{ℓa})⁻¹ = 5·δ(b,a)
    have hchar : ∀ b : Fin 5, (∑ ℓ : ZMod 5,
        (ω' ^ (ℓ.val * b.val)) * (ω' ^ (ℓ.val * a.val))⁻¹) =
        if b = a then 5 else 0 := fun b => char_ortho b a
    -- Swap and reorganize
    have h1 : ∑ ℓ : ZMod 5, F ℓ =
        ∑ x ∈ S, ∑ ℓ : ZMod 5, (ω' ^ (ℓ.val * (g x).val)) *
          (ω' ^ (ℓ.val * a.val))⁻¹ := by
      simp only [F, Finset.mul_sum]
      rw [Finset.sum_comm]
      congr 1; ext ℓ; congr 1; ext x; ring
    rw [h1]
    simp_rw [hchar]
    simp only [Finset.sum_ite, Finset.sum_const, nsmul_eq_mul, mul_comm]
    ring
  -- Step 2: F(0) = n (the ℓ=0 term)
  have hF0 : F 0 = (S.card : ℂ) := by
    simp [F, ZMod.val_zero]
  -- Step 3: Separate ℓ=0 from the sum
  -- F(0) + ∑_{ℓ≠0} F(ℓ) = 5 * cnt
  have hsep : ∑ ℓ ∈ (Finset.univ : Finset (ZMod 5)).erase 0, F ℓ =
      5 * (cnt : ℂ) - (S.card : ℂ) := by
    have h := Finset.add_sum_erase Finset.univ F (Finset.mem_univ (0 : ZMod 5))
    rw [hF0, hfourier] at h
    linear_combination h
  -- Step 4: Norm bound via triangle inequality
  have hnonzero_card : (Finset.univ : Finset (ZMod 5)).erase 0 =
      {(1 : ZMod 5), 2, 3, 4} := by decide
  have hcard4 : ((Finset.univ : Finset (ZMod 5)).erase 0).card = 4 := by
    rw [hnonzero_card]; decide
  -- Each |F(ℓ)| ≤ C for ℓ ≠ 0
  have hFbound : ∀ ℓ ∈ (Finset.univ : Finset (ZMod 5)).erase 0, ‖F ℓ‖ ≤ C := by
    intro ℓ hℓ
    have hℓ_ne : ℓ ≠ 0 := Finset.ne_of_mem_erase hℓ
    calc ‖F ℓ‖
        = ‖(ω' ^ (ℓ.val * a.val))⁻¹ * ∑ x ∈ S, ω' ^ (ℓ.val * (g x).val)‖ := rfl
      _ ≤ ‖(ω' ^ (ℓ.val * a.val))⁻¹‖ * ‖∑ x ∈ S, ω' ^ (ℓ.val * (g x).val)‖ :=
          norm_mul_le _ _
      _ = 1 * ‖∑ x ∈ S, ω' ^ (ℓ.val * (g x).val)‖ := by
          rw [norm_inv, norm_pow, hω_norm, one_pow, inv_one]
      _ = ‖∑ x ∈ S, ω' ^ (ℓ.val * (g x).val)‖ := one_mul _
      _ ≤ C := hbound ℓ hℓ_ne
  -- Triangle inequality: ‖∑_{ℓ≠0} F(ℓ)‖ ≤ 4C
  have hnorm_bound : ‖(5 : ℂ) * (cnt : ℂ) - (S.card : ℂ)‖ ≤ 4 * C := by
    rw [← hsep]
    calc ‖∑ ℓ ∈ (Finset.univ : Finset (ZMod 5)).erase 0, F ℓ‖
        ≤ ∑ ℓ ∈ (Finset.univ : Finset (ZMod 5)).erase 0, ‖F ℓ‖ := norm_sum_le _ _
      _ ≤ ∑ ℓ ∈ (Finset.univ : Finset (ZMod 5)).erase 0, C :=
          Finset.sum_le_sum hFbound
      _ = 4 * C := by rw [Finset.sum_const, hcard4, nsmul_eq_mul]; push_cast; ring
  -- Step 5: Convert complex norm to real absolute value
  have hreal : |(5 * (cnt : ℝ) - (S.card : ℝ))| ≤ 4 * C := by
    have : (5 : ℂ) * (cnt : ℂ) - (S.card : ℂ) =
        ((5 * (cnt : ℝ) - (S.card : ℝ) : ℝ) : ℂ) := by push_cast; ring
    rw [this] at hnorm_bound
    rwa [Complex.norm_real, Real.norm_eq_abs] at hnorm_bound
  -- Step 6: Divide by 5
  rw [show ((S.filter (fun x => g x = a)).card : ℝ) - (S.card : ℝ) / 5 =
      (5 * (cnt : ℝ) - (S.card : ℝ)) / 5 from by ring]
  rw [abs_div, show |(5 : ℝ)| = 5 from by norm_num]
  exact (div_le_div_iff_of_pos_right (by norm_num : (0 : ℝ) < 5)).mpr hreal

/-! ## Section 6: Good Ratio Bound (F6) -/

open Classical in
/-- The "good set": survivors whose child-0 also survives -/
noncomputable def good_set (k : ℕ) : Finset (ZMod (5^(k+1))) :=
  (S_all k).filter fun u => survives k (u * (m k)^(0 : ℕ))

/-- S4 killed-zero count: deviates from |S4|/5 by at most 4C/5 -/
theorem S4_killed_zero_count (k : ℕ) (hk : k ≥ 1)
    (C : ℝ) (hC : 0 < C)
    (hbound : ∀ ℓ : ZMod 5, ℓ ≠ 0 →
      ‖(∑ u ∈ S4 k, ω' ^ (ℓ.val * (killed_index k u).val) : ℂ)‖ ≤ C) :
    |(((S4 k).filter (fun u => killed_index k u = ⟨0, by omega⟩)).card : ℝ) -
     ((S4 k).card : ℝ) / 5| ≤ 4 * C / 5 := by
  exact discrepancy_from_char_bound (S4 k) (killed_index k) ⟨0, by omega⟩ C hC.le hbound

/-- Good ratio lower bound: |good_set| ≥ 4|S_all|/5 - 4C/5 -/
theorem good_ratio_lower (k : ℕ) (hk : k ≥ 1)
    (C : ℝ) (hC : 0 < C)
    (hbound : ∀ ℓ : ZMod 5, ℓ ≠ 0 →
      ‖(∑ u ∈ S4 k, ω' ^ (ℓ.val * (killed_index k u).val) : ℂ)‖ ≤ C) :
    ((good_set k).card : ℝ) ≥ 4 * (S_all k).card / 5 - 4 * C / 5 := by
  -- good_set k = S_all k (child-0 = u * m^0 = u trivially survives)
  have hgood : good_set k = S_all k := by
    ext u
    simp only [good_set, S_all, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨h, _⟩; exact h
    · intro h; refine ⟨h, ?_⟩
      show survives k (u * (m k) ^ (0 : ℕ))
      rw [pow_zero, mul_one]
      exact h
  rw [hgood]
  -- n ≥ 4n/5 - 4C/5 is equivalent to n/5 + 4C/5 ≥ 0
  have hn := Nat.cast_nonneg (α := ℝ) (S_all k).card
  linarith

/-! ## Section 7: Forced-Tail Bound (F7) -/

/-- Key computation: 4 × (91/100)^90 < 1.
    This shows forced-tail count < 1 for k ≥ 91. -/
theorem geometric_decay_91 : 4 * (91/100 : ℝ)^90 < 1 := by
  norm_num

/-- For k ≥ 91, no k-digit power of 2 is zeroless.
    OPEN PROBLEM: This axiom represents an unsolved mathematical question.

    The original proof attempt used forced-tail decay: at each digit level,
    the survival rate was claimed to be ≤ 91/100, giving survivor count
    ≤ 4*(91/100)^90 < 1 for k ≥ 91. This argument is FLAWED because the
    net growth factor per level is 5*(9/10) = 4.5 > 1. The survivor count
    GROWS exponentially rather than decaying.

    This barrier (the "4.5^k barrier") appears in every digit-by-digit
    formulation tested:
    - Forced-tail counting: 4*4.5^k survivors
    - Covering congruences: 4.5^k uncovered residues
    - SAT certificates: 4.5^k uncovered classes
    - Additive Fourier spectrum: permanent 1/9 obstruction

    The problem reduces to a shrinking-target question in dynamics:
    does the orbit n ↦ (2^n mod 5^k, {n·log₁₀(2)}) on a compact abelian
    group hit digit-cylinder targets of measure ~(9/10)^k only finitely
    often? The heuristic expected count beyond k=91 is ~0.0025 (< 1).
    But converting this to a proof requires exponentially strong
    equidistribution or a new shrinking-target theorem that circumvents
    the Tseng (2008) impossibility for general rotations.

    No remaining viable direction has been identified. The problem appears to
    require genuinely new mathematics. Specifically, it needs one of:
      (a) exponentially strong equidistribution for the coupled archimedean +
          non-archimedean system (n·log₁₀(2), 2^n mod 5^k),
      (b) normality-strength digit randomness for 2^n in base 10, or
      (c) a new shrinking-target theorem for digit-cylinder families.
      None currently known.

    Comprehensively KILLED directions (18 analyses, 9 prompt pairs):

    DIGIT-BY-DIGIT / COMBINATORIAL (6 analyses):
    - Forced-tail / digit-by-digit counting: 4.5^k barrier. Net growth
      factor 5*(9/10) = 4.5 > 1 per digit level. Confirmed 6 ways.
    - Multiplicative Fourier on (Z/5^k Z)*: density = 1.0 for all k.
      Every unit mod 5^k is zeroless-compatible. Constraint is invisible.
    - Similarly, density mod 2^k = 1.0 for all k (tested to k=25).
    - The constraint lives ONLY in the joint mod-10^k structure,
      where density = (9/10)^(k-1). It cannot be factored via CRT.
    - Additive Fourier on Z/10^k Z: max normalized coefficient ~1/9,
      permanent obstruction that does not decay with k.

    ALGEBRAIC NUMBER THEORY (6 analyses, prompts S1-S3):
    - S-unit / Subspace Theorem (S1): zeroless is a positive-entropy (9^k)
      condition that cannot be compressed to O(1) S-unit terms. Run-length
      compression (the only viable bridge) requires bounded constant-digit
      runs, which zeroless does not force. Confirmed by 2 analyses.
    - Senge-Straus / Stewart two-bases (S2): requires bounded sparsity in
      both bases. Zeroless is maximally non-sparse (k nonzero digits out of k).
      Complementation (10^k-1-N) doesn't create sparsity. v_2 "instant proof"
      fails because carries raise p-adic valuations arbitrarily.
    - Baker / Matveev linear forms in logarithms (S3): truncation identity
      2^n = 10^m * q + T_m yields a linear form, but q has height ~2^n.
      Matveev lower bound ~exp(-Cn*log(n)) is too weak to contradict the
      upper bound ~exp(-cn). 5-adic Baker also blocked: zeroless is
      avoidance (residue set), not closeness (small linear form).

    AUTOMATON / DYNAMICAL (6 analyses, prompts A1-A3):
    - Doubling automaton (A1): 2-state carry transducer with transition
      matrix [[4,4],[4,5]], eigenvalue ~8.53. Isomorphic to digit-by-digit
      counting; iterated composition blows up state space exponentially.
    - Finite computation bootstrap (A3): period T_k = 4*5^(k-1) too large
      to enumerate. Lift tree is supercritical (branching 4.5 > 1). Suffix
      depth reaches 115 at n=7931, confirming tree has long branches.
    - Borel-Cantelli / discrepancy (A2+A3): heuristic gives expected ~0.0025
      hits beyond k=91, but proving "0 hits" for a deterministic orbit requires
      discrepancy ~(9/50)^k. Standard bounds give ~5^(-k/2) at best.
      Tseng (2008) proves shrinking targets fail for rotations generally.

    ADVANCED METHODS (6 analyses, prompts F1-F3):
    - Furstenberg rigidity / joinings (F1): the coupled system T(x,u) =
      (x + log₁₀(2), 2u) on T × Z_5* is Kronecker (rank-1 rotation, zero
      entropy, no mixing). Rudolph/Host/EKL/Einsiedler-Fish require invariant
      measures with positive entropy under expanding higher-rank actions.
      The only joining is product (disjointness via eigenvalue mismatch:
      archimedean eigenvalues are infinite-order, 5-adic are roots of unity).
      But product equidistribution gives no shrinking-target control.
    - Additive combinatorics / exponential sums (F2): finiteness reduces to
      controlling incomplete sums Σ_{n≤N} e(h·2^n/5^k) with N ~ k ~ log(5^k).
      This is the "log-time regime." Korobov bounds give saving factor
      exp(-γ·log³(k)/k²) = 1-o(1), i.e., no cancellation. Bourgain-Chang
      needs sets of size q^δ; our N ~ log(q). Maynard's digit method gives
      lower bounds for dense sets, not upper bounds for sparse orbits.
      Green-Tao / nilsequences: dynamics is 1-step, so U^s norms add nothing
      beyond Fourier. Circle method / Wooley / decoupling: tuned to
      polynomial phases, not exponential sequences.
    - p-adic Strassmann / Weierstrass / Mahler (F3): the zeroless condition
      at level k is a union of ~4.5^k 5-adic balls (a clopen set). No
      nonzero analytic function can vanish on an open ball without vanishing
      identically. Any product encoding has Weierstrass degree ~4.5^k.
      Mahler series need coefficients to degree ~5^k. Iwasawa theory requires
      character/Galois-module structure; W_k is defined by digit cylinders,
      not by multiplicative characters.

    See GPT_PROMPTS.md, SUBSPACE_THEOREM_PROMPTS.md, AUTOMATON_PROMPTS.md,
    ADVANCED_PROMPTS.md for full prompt text and analysis. -/
axiom no_zeroless_k_ge_91 (k : ℕ) (hk : k ≥ 91) :
    ∀ n : ℕ, (Nat.digits 10 (2^n)).length = k → 0 ∈ Nat.digits 10 (2^n)

end

end Zeroless
