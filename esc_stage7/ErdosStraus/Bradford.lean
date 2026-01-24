import Mathlib
import ErdosStraus.Basic

namespace ErdosStraus

open scoped BigOperators

/--
Bradford Type II witness condition (rewritten to avoid explicit negatives):

`d ≡ -x (mod m)` is expressed as `(d + x) ≡ 0 (mod m)`.

This is the condition used in Stage 4/5: for `m = 4x - p`,
find `d ∣ x^2` with `(d+x) ≡ 0 (mod m)` and `d ≤ x`.
-/
def TypeIIWitness (p x d : ℕ) : Prop :=
  (d ∣ x^2) ∧ d ≤ x ∧ Nat.ModEq (m p x) (d + x) 0

/--
A core validity lemma for Bradford Type II.

It packages three things:
1. `y` and `z` (defined by Bradford) are natural numbers.
2. Under the congruence/divisibility hypotheses, the divisions are *exact*.
3. The resulting `(x,y,z)` satisfies the cross-multiplied Erdős–Straus equation.

The proof in Mathlib is mostly algebra (`ring`) plus two integrality steps:
- `m ∣ (x+d)` is immediate from the congruence.
- `m ∣ (x+x^2/d)` follows by multiplying the congruence by `x^2/d` and cancelling `x`
  using `Nat.Coprime x m`.

**Note:** In a final proof, `Nat.Coprime x m` is typically derived from
`hp : Nat.Prime p` and the Bradford range condition `x < p`.
-/
theorem bradford_typeII_valid
    (p x d : ℕ)
    (hp : Nat.Prime p)
    (hmpos : m p x > 0)
    (hx : x < p)
    (hw : TypeIIWitness p x d)
    (hcop : Nat.Coprime x (m p x)) :
    let y := bradfordY p x d
    let z := bradfordZ p x d
    y > 0 ∧ z > 0 ∧ ES p x y z := by
  classical
  -- Unpack witness
  rcases hw with ⟨hd, hle, hcong⟩
  -- Shorthands
  set m' : ℕ := m p x
  have hm0 : m' ≠ 0 := by exact Nat.ne_of_gt hmpos
  -- `m' ∣ (x+d)` from congruence
  have hmdvd_xd : m' ∣ (x + d) := by
    -- `Nat.ModEq m' (d+x) 0` means `(d+x) % m' = 0`
    -- hence `m' ∣ (d+x)`.
    have h : (d + x) % m' = 0 % m' := hcong
    simp at h
    rw [Nat.add_comm] at h
    exact Nat.dvd_of_mod_eq_zero h
  -- Exactness of `d ∣ x^2` gives `x^2 / d * d = x^2`
  have hx2_eq : (x^2 / d) * d = x^2 := by
    exact Nat.div_mul_cancel hd
  -- Show `m' ∣ (x + x^2/d)` via cancellation in `ZMod m'`
  -- (Proof structure from Aristotle, adapted to our naming)
  have hmdvd_xe : m' ∣ (x + x^2 / d) := by
    -- Set e = x^2/d, the complementary divisor
    set e : ℕ := x^2 / d with he_def
    have he : d * e = x^2 := Nat.mul_div_cancel' hd

    -- Multiply (d+x) ≡ 0 by e to get d*e + x*e ≡ 0
    have hmul : Nat.ModEq m' ((x + d) * e) 0 := by
      have h := hcong
      rw [Nat.add_comm] at h
      simpa [Nat.mul_zero] using (h.mul_right e)

    -- Since d*e = x^2, we have x*e + x^2 ≡ 0, i.e., x*(x+e) ≡ 0
    have hmul' : Nat.ModEq m' (x * (x + e)) 0 := by
      have hxde : (x + d) * e = x * (x + e) := by
        calc (x + d) * e = x*e + d*e := by ring
          _ = x*e + x^2 := by rw [he]
          _ = x*e + x*x := by ring
          _ = x*(e + x) := by ring
          _ = x*(x + e) := by ring
      simpa [hxde] using hmul

    -- Cancel x using coprimality to get (x+e) ≡ 0
    have hxplus : Nat.ModEq m' (x + e) 0 := by
      have hmul'' : Nat.ModEq m' (x*(x+e)) (x*0) := by
        simpa [Nat.mul_zero] using hmul'
      have hcancel := Nat.ModEq.cancel_left_of_coprime
        (by simpa [Nat.coprime_comm] using hcop) hmul''
      simpa [Nat.mul_zero] using hcancel

    -- Therefore m' ∣ (x + e)
    have : (x + e) % m' = 0 := by simpa [Nat.ModEq] using hxplus
    exact Nat.dvd_of_mod_eq_zero this
  -- Now show `y,z > 0` and the ES identity.
  -- Positivity: since `m' > 0`, `p > 0`, and the numerators are positive.
  have hp0 : p > 0 := hp.pos
  -- Need x > 0 for positivity arguments
  have hxpos : x > 0 := by
    by_contra hx0
    push_neg at hx0
    -- If x ≤ 0, then x = 0 (in ℕ)
    have hx_eq : x = 0 := Nat.eq_zero_of_le_zero hx0
    -- m' = m p x = 4*x - p = 0 - p = 0 in ℕ (since x = 0 and p > 0)
    have hm'_zero : m' = 0 := by
      show m p x = 0
      simp only [hx_eq, m]
      omega
    omega

  have hy_pos : bradfordY p x d > 0 := by
    -- y = p*(x+d)/m', and m' ∣ p*(x+d) since m' ∣ (x+d)
    unfold bradfordY
    have hdiv : m' ∣ p * (x + d) := by
      have h := dvd_mul_of_dvd_left hmdvd_xd p
      simp only [mul_comm] at h; exact h
    rcases hdiv with ⟨t, ht⟩
    have hnumpos : 0 < p * (x + d) := Nat.mul_pos hp0 (Nat.add_pos_left hxpos d)
    have ht0 : t ≠ 0 := by
      intro ht0
      rw [ht0, Nat.mul_zero] at ht
      exact Nat.ne_of_gt hnumpos ht
    have hy_eq : p * (x + d) / m' = t := by
      rw [ht, Nat.mul_div_cancel_left _ hmpos]
    rw [hy_eq]
    exact Nat.pos_of_ne_zero ht0

  have hz_pos : bradfordZ p x d > 0 := by
    -- z = p*(x+x^2/d)/m', and m' ∣ p*(x+x^2/d) since m' ∣ (x+x^2/d)
    unfold bradfordZ
    have hdiv : m' ∣ p * (x + x^2/d) := by
      have h := dvd_mul_of_dvd_left hmdvd_xe p
      simp only [mul_comm] at h; exact h
    rcases hdiv with ⟨t, ht⟩
    have he_pos : 0 < x^2 / d := by
      -- d ∣ x² and d ≤ x and x > 0 implies d > 0
      -- Since d ∣ x² and d ≤ x < x², we have x²/d ≥ x ≥ 1
      have hd0 : d > 0 := by
        by_contra hd0'
        push_neg at hd0'
        interval_cases d
        -- d = 0 contradicts d ∣ x² when x > 0
        simp [Nat.zero_dvd] at hd
        omega
      have hx2_pos : x^2 > 0 := Nat.pos_pow_of_pos 2 hxpos
      have hd_le_x2 : d ≤ x^2 := by
        calc d ≤ x := hle
          _ ≤ x * x := Nat.le_mul_self x
          _ = x^2 := (sq x).symm
      exact Nat.div_pos hd_le_x2 hd0
    have hnumpos : 0 < p * (x + x^2/d) := Nat.mul_pos hp0 (Nat.add_pos_left hxpos (x^2/d))
    have ht0 : t ≠ 0 := by
      intro ht0
      rw [ht0, Nat.mul_zero] at ht
      exact Nat.ne_of_gt hnumpos ht
    have hz_eq : p * (x + x^2/d) / m' = t := by
      rw [ht, Nat.mul_div_cancel_left _ hmpos]
    rw [hz_eq]
    exact Nat.pos_of_ne_zero ht0
  -- ES identity: purely algebraic once divisions are exact.
  have hES : ES p x (bradfordY p x d) (bradfordZ p x d) := by
    -- The key algebraic identity follows from the Bradford construction.
    -- With y = p(x+d)/m, z = p(x+e)/m, de = x², and m = 4x-p,
    -- the ES equation 4xyz = p(xy + xz + yz) reduces to a polynomial identity.
    --
    -- Proof: Work in ℚ where divisions are exact.
    -- 4/p = 1/x + 1/y + 1/z
    --     = 1/x + m/(p(x+d)) + m/(p(x+e))
    --
    -- Multiply through by p·x·(x+d)·(x+e):
    -- 4x(x+d)(x+e) = p(x+d)(x+e) + xm(x+e) + xm(x+d)
    --              = p(x+d)(x+e) + xm((x+d)+(x+e))
    --              = p(x+d)(x+e) + xm(2x+d+e)
    --
    -- Using m = 4x-p and (x+d)(x+e) = x² + x(d+e) + de = 2x² + x(d+e) (since de = x²):
    -- This is a pure polynomial identity.
    unfold ES bradfordY bradfordZ
    set e := x^2 / d with he_def
    have he : d * e = x^2 := Nat.mul_div_cancel' hd
    -- The divisions p*(x+d)/m' and p*(x+e)/m' are exact
    have hy_exact : p * (x + d) = m' * (p * (x + d) / m') := by
      have h := dvd_mul_of_dvd_left hmdvd_xd p
      rw [mul_comm] at h
      exact (Nat.mul_div_cancel' h).symm
    have hz_exact : p * (x + e) = m' * (p * (x + e) / m') := by
      have hdiv : m' ∣ (x + e) := by
        have : (x + e) % m' = 0 := by
          -- From earlier proof
          set e' := x^2 / d with he'_def
          have hmul : Nat.ModEq m' ((x + d) * e') 0 := by
            have h := hcong; rw [Nat.add_comm] at h
            simpa [Nat.mul_zero] using (h.mul_right e')
          have hmul' : Nat.ModEq m' (x * (x + e')) 0 := by
            have hxde : (x + d) * e' = x * (x + e') := by
              have he'' : d * e' = x^2 := Nat.mul_div_cancel' hd
              calc (x + d) * e' = x*e' + d*e' := by ring
                _ = x*e' + x^2 := by rw [he'']
                _ = x*(e' + x) := by ring
                _ = x*(x + e') := by ring
            simpa [hxde] using hmul
          have hxplus : Nat.ModEq m' (x + e') 0 := by
            have hmul'' : Nat.ModEq m' (x*(x+e')) (x*0) := by
              simpa [Nat.mul_zero] using hmul'
            have hcancel := Nat.ModEq.cancel_left_of_coprime
              (by simpa [Nat.coprime_comm] using hcop) hmul''
            simpa [Nat.mul_zero] using hcancel
          simpa [Nat.ModEq, he'_def, he_def] using hxplus
        exact Nat.dvd_of_mod_eq_zero this
      have h := dvd_mul_of_dvd_left hdiv p
      rw [mul_comm] at h
      exact (Nat.mul_div_cancel' h).symm
    -- The ES identity is now a consequence of the polynomial identity
    -- 4xyz = p(xy + xz + yz) when y = p(x+d)/m, z = p(x+e)/m, de = x², m = 4x-p
    --
    -- Strategy: Set y' = p*(x+d)/m' and z' = p*(x+e)/m'.
    -- Then m'*y' = p*(x+d) and m'*z' = p*(x+e).
    -- Multiply the ES equation by m'² and verify the polynomial identity.

    -- Define y' and z' for clarity
    set y' := p * (x + d) / m' with hy'_def
    set z' := p * (x + e) / m' with hz'_def

    -- The divisions are exact: m' * y' = p * (x + d) and m' * z' = p * (x + e)
    have hmy : m' * y' = p * (x + d) := by
      rw [hy'_def]
      have h := dvd_mul_of_dvd_left hmdvd_xd p
      rw [mul_comm] at h
      exact Nat.mul_div_cancel' h
    have hmz : m' * z' = p * (x + e) := by
      rw [hz'_def]
      have hdiv : m' ∣ (x + e) := hmdvd_xe
      have h := dvd_mul_of_dvd_left hdiv p
      rw [mul_comm] at h
      exact Nat.mul_div_cancel' h

    -- Now verify: 4 * x * y' * z' = p * (x * y' + x * z' + y' * z')
    -- Multiply both sides by m'² and use m = 4x - p, de = x².
    --
    -- After multiplication by m'² and simplification, both sides equal:
    -- 4 * p² * x * (x + d) * (x + e)
    --
    -- The polynomial identity (using de = x², m' = 4x - p) is:
    -- 4x(x+d)(x+e) = (4x-p)(x(2x+d+e)) + p(x+d)(x+e)
    --             = 4x²(2x+d+e) - px(2x+d+e) + p(2x² + x(d+e))  [using (x+d)(x+e) = 2x² + x(d+e)]
    --             = 8x³ + 4x²(d+e) - 2px² - px(d+e) + 2px² + px(d+e)
    --             = 8x³ + 4x²(d+e)
    -- And 4x(x+d)(x+e) = 4x(2x² + x(d+e)) = 8x³ + 4x²(d+e). ✓

    -- Key lemma: (x+d)(x+e) = 2x² + x(d+e) when de = x²
    have hprod : (x + d) * (x + e) = 2 * x^2 + x * (d + e) := by
      have hde : d * e = x^2 := he
      -- (x + d)(x + e) = x² + xd + xe + de = x² + x(d+e) + x² = 2x² + x(d+e)
      have h1 : (x + d) * (x + e) = x * x + x * e + d * x + d * e := by ring
      have h2 : x * x + x * e + d * x + d * e = x^2 + x * e + d * x + x^2 := by rw [hde, sq]
      have h3 : x^2 + x * e + d * x + x^2 = 2 * x^2 + x * (d + e) := by ring
      omega

    -- The ES equation in expanded form
    -- We need to show: 4 * x * y' * z' = p * (x * y' + x * z' + y' * z')

    -- Use the exactness to rewrite in terms of p, x, d, e, m'
    -- LHS = 4 * x * y' * z'
    -- RHS = p * (x * y' + x * z' + y' * z')

    -- Multiply both sides by m'² and verify they're equal
    have hm'_sq_pos : m'^2 > 0 := Nat.pos_pow_of_pos 2 hmpos

    -- LHS * m'² = 4 * x * (m' * y') * (m' * z') / m'² * m'² = 4 * x * p² * (x+d) * (x+e)
    -- RHS * m'² = p * (x * m' * y' * m' + x * m' * z' * m' + m' * y' * m' * z') / m'² * m'²
    --           = p * (x * p * (x+d) * m' + x * p * (x+e) * m' + p² * (x+d) * (x+e))

    -- Let's compute LHS * m'²
    have lhs_expanded : 4 * x * y' * z' * m'^2 = 4 * x * p^2 * (x + d) * (x + e) := by
      calc 4 * x * y' * z' * m'^2
        = 4 * x * y' * (z' * m') * m' := by ring
        _ = 4 * x * y' * (m' * z') * m' := by ring
        _ = 4 * x * y' * (p * (x + e)) * m' := by rw [hmz]
        _ = 4 * x * (y' * m') * p * (x + e) := by ring
        _ = 4 * x * (m' * y') * p * (x + e) := by ring
        _ = 4 * x * (p * (x + d)) * p * (x + e) := by rw [hmy]
        _ = 4 * x * p^2 * (x + d) * (x + e) := by ring

    -- Let's compute RHS * m'²
    have rhs_expanded : p * (x * y' + x * z' + y' * z') * m'^2 =
        p^2 * x * m' * (x + d) + p^2 * x * m' * (x + e) + p^3 * (x + d) * (x + e) := by
      calc p * (x * y' + x * z' + y' * z') * m'^2
        = p * x * y' * m'^2 + p * x * z' * m'^2 + p * y' * z' * m'^2 := by ring
        _ = p * x * (m' * y') * m' + p * x * (m' * z') * m' + p * (m' * y') * (m' * z') := by ring
        _ = p * x * (p * (x + d)) * m' + p * x * (p * (x + e)) * m' + p * (p * (x + d)) * (p * (x + e)) := by rw [hmy, hmz]
        _ = p^2 * x * m' * (x + d) + p^2 * x * m' * (x + e) + p^3 * (x + d) * (x + e) := by ring

    -- Now we need to show lhs_expanded = rhs_expanded after factoring
    -- i.e., 4 * x * p² * (x+d) * (x+e) = p² * x * m' * ((x+d) + (x+e)) + p³ * (x+d) * (x+e)
    --     = p² * (x * m' * (2x + d + e) + p * (x+d) * (x+e))

    -- Use m' = 4x - p (note: m' = m p x = 4*x - p)
    have hm'_eq : m' = 4 * x - p := by rfl

    -- The key polynomial identity (after dividing by p²):
    -- 4x(x+d)(x+e) = xm'(2x+d+e) + p(x+d)(x+e)
    -- Using m' = 4x - p and (x+d)(x+e) = 2x² + x(d+e):
    -- LHS = 4x(2x² + x(d+e)) = 8x³ + 4x²(d+e)
    -- RHS = x(4x-p)(2x+d+e) + p(2x² + x(d+e))
    --     = (4x² - px)(2x+d+e) + 2px² + px(d+e)
    --     = 8x³ + 4x²(d+e) - 2px² - px(d+e) + 2px² + px(d+e)
    --     = 8x³ + 4x²(d+e)

    -- This is getting complex. Let me try a more direct approach using omega/ring.
    -- The issue is we're in ℕ, not ℤ, so m' = 4x - p requires 4x > p.

    -- We have hx : x < p, which gives us constraints.
    -- Actually, we need p < 4x (from hmpos : m p x > 0, i.e., 4x - p > 0)

    have hp_lt_4x : p < 4 * x := by
      -- m' = m p x = 4*x - p, and m' > 0 implies 4*x > p
      have hm'_def : m' = 4 * x - p := rfl
      omega

    -- Now the polynomial identity can be verified
    suffices h : 4 * x * p^2 * (x + d) * (x + e) =
        p^2 * x * m' * (x + d) + p^2 * x * m' * (x + e) + p^3 * (x + d) * (x + e) by
      -- From lhs_expanded and rhs_expanded, combined with h:
      -- 4 * x * y' * z' * m'^2 = 4 * x * p^2 * (x + d) * (x + e) = RHS = p * (...) * m'^2
      have heq : 4 * x * y' * z' * m'^2 = p * (x * y' + x * z' + y' * z') * m'^2 := by
        calc 4 * x * y' * z' * m'^2 = 4 * x * p^2 * (x + d) * (x + e) := lhs_expanded
          _ = p^2 * x * m' * (x + d) + p^2 * x * m' * (x + e) + p^3 * (x + d) * (x + e) := h
          _ = p * (x * y' + x * z' + y' * z') * m'^2 := rhs_expanded.symm
      exact Nat.eq_of_mul_eq_mul_right hm'_sq_pos heq

    -- Prove the polynomial identity
    -- 4xp²(x+d)(x+e) = p²xm'(x+d) + p²xm'(x+e) + p³(x+d)(x+e)
    --                = p²xm'((x+d)+(x+e)) + p³(x+d)(x+e)
    --                = p²(xm'(2x+d+e) + p(x+d)(x+e))

    -- Factor out and use m' = 4x - p
    calc 4 * x * p^2 * (x + d) * (x + e)
      = p^2 * (4 * x * ((x + d) * (x + e))) := by ring
      _ = p^2 * (4 * x * (2 * x^2 + x * (d + e))) := by rw [hprod]
      _ = p^2 * (8 * x^3 + 4 * x^2 * (d + e)) := by ring
      _ = p^2 * (x * (4 * x - p) * (2 * x + d + e) + p * (2 * x^2 + x * (d + e))) := by
          -- This is the key: 8x³ + 4x²(d+e) = x(4x-p)(2x+d+e) + p(2x² + x(d+e))
          -- Expand RHS: x(4x-p)(2x+d+e) + p(2x² + x(d+e))
          --   = (4x² - px)(2x + d + e) + 2px² + px(d+e)
          --   = 8x³ + 4x²d + 4x²e - 2px² - pxd - pxe + 2px² + pxd + pxe
          --   = 8x³ + 4x²(d+e)
          have hpoly : 8 * x^3 + 4 * x^2 * (d + e) =
              x * (4 * x - p) * (2 * x + d + e) + p * (2 * x^2 + x * (d + e)) := by
            -- Need to be careful with ℕ subtraction
            have h4x_ge_p : 4 * x ≥ p := Nat.le_of_lt hp_lt_4x
            -- Cast to ℤ where ring works, then use Nat.cast_injective
            have h_int : ((8 * x^3 + 4 * x^2 * (d + e) : ℕ) : ℤ) =
                ((x * (4 * x - p) * (2 * x + d + e) + p * (2 * x^2 + x * (d + e)) : ℕ) : ℤ) := by
              -- Expand the Nat subtraction to Int subtraction
              have h4xp : ((4 * x - p : ℕ) : ℤ) = (4 * x : ℤ) - (p : ℤ) := Int.ofNat_sub h4x_ge_p
              simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_pow, h4xp]
              ring
            exact Nat.cast_injective h_int
          exact congrArg (p^2 * ·) hpoly
      _ = p^2 * (x * m' * (2 * x + d + e) + p * (x + d) * (x + e)) := by
          rw [hm'_eq, ← hprod]; ring
      _ = p^2 * x * m' * (x + d) + p^2 * x * m' * (x + e) + p^3 * (x + d) * (x + e) := by ring
  -- Finish
  exact ⟨hy_pos, hz_pos, hES⟩

end ErdosStraus
