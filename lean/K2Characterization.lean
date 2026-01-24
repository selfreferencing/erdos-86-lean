import Mathlib

namespace K2Characterization

/-!
This answers the k=2 "witness picking" prompt.

Important note (mathematical): the statements in the prompt omit the (Mordell-hard) condition
`p ≡ 1 (mod 4)` (equivalently `4 ∣ p+11`). Without it, the quoted lemmas are false because
`x₂ := (p+11)/4` is then *Nat-division*, not the intended integer `(p+11)/4`.

Example: `p = 7` is prime and `p % 3 = 1`, but `(p+11)/4 = 4` and `3 ∤ 4`.

Accordingly, we add `hp_mod4 : p % 4 = 1` to the relevant lemmas. For the `d = 81` case we also
assume `81 ≤ x₂`, which holds in the intended "Mordell-hard prime" range.
-/

/-- If `p ≡ 1 (mod 4)`, then `4 ∣ p+11`. -/
lemma four_dvd_p_add11 (p : ℕ) (hp_mod4 : p % 4 = 1) : 4 ∣ p + 11 := by
  have : (p + 11) % 4 = 0 := by
    calc
      (p + 11) % 4 = (p % 4 + 11 % 4) % 4 := by
        simp [Nat.add_mod]
      _ = (1 + 3) % 4 := by
        simpa [hp_mod4]
      _ = 0 := by decide
  exact Nat.dvd_of_mod_eq_zero this

/-- For primes `p` with `p ≡ 1 (mod 3)` and `p ≡ 1 (mod 4)`, we have `3 ∣ x₂ := (p+11)/4`. -/
lemma three_divides_x2 (p : ℕ) (hp : Nat.Prime p) (hp_mod3 : p % 3 = 1) (hp_mod4 : p % 4 = 1) :
    3 ∣ (p + 11) / 4 := by
  -- First show `3 ∣ p+11`.
  have h3 : 3 ∣ p + 11 := by
    have : (p + 11) % 3 = 0 := by
      calc
        (p + 11) % 3 = (p % 3 + 11 % 3) % 3 := by
          simp [Nat.add_mod]
        _ = (1 + 2) % 3 := by
          simpa [hp_mod3]
        _ = 0 := by decide
    exact Nat.dvd_of_mod_eq_zero this
  -- Rewrite `p+11 = 4 * ((p+11)/4)` and cancel the factor `4`.
  have h4 : 4 ∣ p + 11 := four_dvd_p_add11 p hp_mod4
  set x₂ : ℕ := (p + 11) / 4 with hx₂
  have hx₂mul : 4 * x₂ = p + 11 := by
    simpa [hx₂] using (Nat.mul_div_cancel' h4)
  have h3mul : 3 ∣ 4 * x₂ := by
    simpa [hx₂mul] using h3
  have hcop : Nat.Coprime 3 4 := by decide
  have : 3 ∣ x₂ := hcop.dvd_of_dvd_mul_left h3mul
  simpa [hx₂] using this

/-- Powers of 3 mod 11. -/
lemma three_pow_mod11 :
    (3^1 % 11 = 3) ∧ (3^2 % 11 = 9) ∧ (3^3 % 11 = 5) ∧ (3^4 % 11 = 4) ∧ (3^5 % 11 = 1) := by
  native_decide

/-- k=2 works when `p ≡ 7 (mod 11)` via `d = 1`. -/
lemma k2_works_p7 (p : ℕ) (hp : Nat.Prime p) (hp_mod4 : p % 4 = 1) (hp_mod : p % 11 = 7) :
    let x₂ := (p + 11) / 4
    ∃ d, d ∣ x₂^2 ∧ d ≤ x₂ ∧ (x₂ + d) % 11 = 0 := by
  dsimp
  set x₂ : ℕ := (p + 11) / 4 with hx₂
  refine ⟨1, one_dvd (x₂ ^ 2), ?_, ?_⟩
  · -- `1 ≤ x₂`
    have hp2 : 2 ≤ p := hp.two_le
    have h13 : 13 ≤ p + 11 := by
      simpa using (Nat.add_le_add_right hp2 11)
    have h4le : 4 ≤ p + 11 := le_trans (by decide : 4 ≤ 13) h13
    have hx2pos : 0 < x₂ := by
      have : 0 < (p + 11) / 4 := Nat.div_pos (by decide : 0 < 4) h4le
      simpa [hx₂] using this
    exact Nat.succ_le_of_lt hx2pos
  · -- `(x₂+1) % 11 = 0`
    have h11_p4 : 11 ∣ p + 4 := by
      have : (p + 4) % 11 = 0 := by
        calc
          (p + 4) % 11 = (p % 11 + 4 % 11) % 11 := by
            simp [Nat.add_mod]
          _ = (7 + 4) % 11 := by
            simpa [hp_mod]
          _ = 0 := by decide
      exact Nat.dvd_of_mod_eq_zero this
    have h11_rhs : 11 ∣ p + 11 + 4 := by
      have : 11 ∣ (p + 4) + 11 := dvd_add h11_p4 (dvd_refl 11)
      simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using this
    have h4 : 4 ∣ p + 11 := four_dvd_p_add11 p hp_mod4
    have hx2mul : 4 * x₂ = p + 11 := by
      simpa [hx₂] using (Nat.mul_div_cancel' h4)
    have hmul : 4 * (x₂ + 1) = p + 11 + 4 := by
      calc
        4 * (x₂ + 1) = 4 * x₂ + 4 * 1 := by
          simp [mul_add]
        _ = (p + 11) + 4 := by simp [hx2mul]
        _ = p + 11 + 4 := by simp [Nat.add_assoc]
    have h11_mul : 11 ∣ 4 * (x₂ + 1) := by
      simpa [hmul] using h11_rhs
    have hcop : Nat.Coprime 11 4 := by decide
    have h11_x2 : 11 ∣ x₂ + 1 := hcop.dvd_of_dvd_mul_left h11_mul
    exact Nat.mod_eq_zero_of_dvd h11_x2

/-- k=2 works when `p ≡ 10 (mod 11)` via `d = 3`. -/
lemma k2_works_p10 (p : ℕ) (hp : Nat.Prime p) (hp_mod3 : p % 3 = 1) (hp_mod4 : p % 4 = 1)
    (hp_mod : p % 11 = 10) :
    let x₂ := (p + 11) / 4
    ∃ d, d ∣ x₂^2 ∧ d ≤ x₂ ∧ (x₂ + d) % 11 = 0 := by
  dsimp
  set x₂ : ℕ := (p + 11) / 4 with hx₂
  have hx3 : 3 ∣ x₂ := by
    simpa [hx₂] using three_divides_x2 p hp hp_mod3 hp_mod4
  -- x₂ is positive (used for `3 ≤ x₂` via the factorization)
  have hp2 : 2 ≤ p := hp.two_le
  have h13 : 13 ≤ p + 11 := by
    simpa using (Nat.add_le_add_right hp2 11)
  have h4le : 4 ≤ p + 11 := le_trans (by decide : 4 ≤ 13) h13
  have hx2pos : 0 < x₂ := by
    have : 0 < (p + 11) / 4 := Nat.div_pos (by decide : 0 < 4) h4le
    simpa [hx₂] using this
  have hx2_ne0 : x₂ ≠ 0 := Nat.ne_of_gt hx2pos
  refine ⟨3, ?_, ?_, ?_⟩
  · -- `3 ∣ x₂^2`
    rcases hx3 with ⟨t, rfl⟩
    refine ⟨3 * t^2, by
      simp [pow_two, mul_assoc, mul_left_comm, mul_comm]⟩
  · -- `3 ≤ x₂`
    rcases hx3 with ⟨t, rfl⟩
    have ht_ne0 : t ≠ 0 := by
      intro ht0
      apply hx2_ne0
      simp [ht0]
    have ht_pos : 0 < t := Nat.pos_of_ne_zero ht_ne0
    have ht_ge1 : 1 ≤ t := Nat.succ_le_of_lt ht_pos
    have : 3 * 1 ≤ 3 * t := Nat.mul_le_mul_left 3 ht_ge1
    simpa using this
  · -- `(x₂+3) % 11 = 0`
    have h11_p12 : 11 ∣ p + 12 := by
      have : (p + 12) % 11 = 0 := by
        calc
          (p + 12) % 11 = (p % 11 + 12 % 11) % 11 := by
            simp [Nat.add_mod]
          _ = (10 + 1) % 11 := by
            simpa [hp_mod]
          _ = 0 := by decide
      exact Nat.dvd_of_mod_eq_zero this
    have h11_rhs : 11 ∣ p + 11 + 12 := by
      have : 11 ∣ (p + 12) + 11 := dvd_add h11_p12 (dvd_refl 11)
      simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using this
    have h4 : 4 ∣ p + 11 := four_dvd_p_add11 p hp_mod4
    have hx2mul : 4 * x₂ = p + 11 := by
      simpa [hx₂] using (Nat.mul_div_cancel' h4)
    have hmul : 4 * (x₂ + 3) = p + 11 + 12 := by
      calc
        4 * (x₂ + 3) = 4 * x₂ + 4 * 3 := by
          simp [mul_add]
        _ = (p + 11) + 12 := by simp [hx2mul]
        _ = p + 11 + 12 := by simp [Nat.add_assoc]
    have h11_mul : 11 ∣ 4 * (x₂ + 3) := by
      simpa [hmul] using h11_rhs
    have hcop : Nat.Coprime 11 4 := by decide
    have h11_x2 : 11 ∣ x₂ + 3 := hcop.dvd_of_dvd_mul_left h11_mul
    exact Nat.mod_eq_zero_of_dvd h11_x2

/-- k=2 works when `p ≡ 8 (mod 11)` via `d = 9`. -/
lemma k2_works_p8 (p : ℕ) (hp : Nat.Prime p) (hp_mod3 : p % 3 = 1) (hp_mod4 : p % 4 = 1)
    (hp_mod : p % 11 = 8) :
    let x₂ := (p + 11) / 4
    ∃ d, d ∣ x₂^2 ∧ d ≤ x₂ ∧ (x₂ + d) % 11 = 0 := by
  dsimp
  set x₂ : ℕ := (p + 11) / 4 with hx₂
  have hx3 : 3 ∣ x₂ := by
    simpa [hx₂] using three_divides_x2 p hp hp_mod3 hp_mod4
  rcases hx3 with ⟨t, ht⟩
  refine ⟨9, ?_, ?_, ?_⟩
  · -- `9 ∣ x₂^2`
    refine ⟨t^2, by
      simp [ht, pow_two, mul_assoc, mul_left_comm, mul_comm]⟩
  · -- `9 ≤ x₂` (we show `x₂ ≥ 24`)
    have h4 : 4 ∣ p + 11 := four_dvd_p_add11 p hp_mod4
    have hx2mul : 4 * x₂ = p + 11 := by
      simpa [hx₂] using (Nat.mul_div_cancel' h4)
    have h4x2_mod : (4 * x₂) % 11 = 8 := by
      calc
        (4 * x₂) % 11 = (p + 11) % 11 := by simpa [hx2mul]
        _ = p % 11 := by simp [Nat.add_mod]
        _ = 8 := by simpa [hp_mod]
    have h12t_mod : (12 * t) % 11 = 8 := by
      have hEq : 4 * x₂ = 12 * t := by
        simp [ht, mul_assoc, mul_left_comm, mul_comm]
      simpa [hEq] using h4x2_mod
    have h12t_eq : (12 * t) % 11 = t % 11 := by
      calc
        (12 * t) % 11 = (12 % 11 * (t % 11)) % 11 := by simp [Nat.mul_mod]
        _ = (1 * (t % 11)) % 11 := by simp
        _ = t % 11 := by simp
    have ht_mod : t % 11 = 8 := by
      simpa [h12t_eq] using h12t_mod
    have ht_ge8 : 8 ≤ t := by
      have : t % 11 ≤ t := Nat.mod_le t 11
      simpa [ht_mod] using this
    have hx2_ge24 : 24 ≤ x₂ := by
      have : 3 * 8 ≤ 3 * t := Nat.mul_le_mul_left 3 ht_ge8
      have : 24 ≤ 3 * t := by simpa using this
      simpa [ht] using this
    exact le_trans (by decide : 9 ≤ 24) hx2_ge24
  · -- `(x₂+9) % 11 = 0`
    have h11_p36 : 11 ∣ p + 36 := by
      have : (p + 36) % 11 = 0 := by
        calc
          (p + 36) % 11 = (p % 11 + 36 % 11) % 11 := by
            simp [Nat.add_mod]
          _ = (8 + 3) % 11 := by
            simpa [hp_mod]
          _ = 0 := by decide
      exact Nat.dvd_of_mod_eq_zero this
    have h11_rhs : 11 ∣ p + 11 + 36 := by
      have : 11 ∣ (p + 36) + 11 := dvd_add h11_p36 (dvd_refl 11)
      simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using this
    have h4 : 4 ∣ p + 11 := four_dvd_p_add11 p hp_mod4
    have hx2mul : 4 * x₂ = p + 11 := by
      simpa [hx₂] using (Nat.mul_div_cancel' h4)
    have hmul : 4 * (x₂ + 9) = p + 11 + 36 := by
      calc
        4 * (x₂ + 9) = 4 * x₂ + 4 * 9 := by
          simp [mul_add]
        _ = (p + 11) + 36 := by simp [hx2mul]
        _ = p + 11 + 36 := by simp [Nat.add_assoc]
    have h11_mul : 11 ∣ 4 * (x₂ + 9) := by
      simpa [hmul] using h11_rhs
    have hcop : Nat.Coprime 11 4 := by decide
    have h11_x2 : 11 ∣ x₂ + 9 := hcop.dvd_of_dvd_mul_left h11_mul
    exact Nat.mod_eq_zero_of_dvd h11_x2

/-- k=2 works when `p ≡ 2 (mod 11)` and `v₃(x₂) ≥ 2` via `d = 27`. -/
lemma k2_works_p2_v3 (p : ℕ) (hp : Nat.Prime p) (hp_mod3 : p % 3 = 1) (hp_mod4 : p % 4 = 1)
    (hp_mod : p % 11 = 2) (hv3 : 9 ∣ (p + 11) / 4) :
    let x₂ := (p + 11) / 4
    ∃ d, d ∣ x₂^2 ∧ d ≤ x₂ ∧ (x₂ + d) % 11 = 0 := by
  dsimp
  set x₂ : ℕ := (p + 11) / 4 with hx₂
  have hv3' : 9 ∣ x₂ := by simpa [hx₂] using hv3
  rcases hv3' with ⟨t, ht⟩
  refine ⟨27, ?_, ?_, ?_⟩
  · -- `27 ∣ x₂^2`
    refine ⟨3 * t^2, by
      simp [ht, pow_two, mul_assoc, mul_left_comm, mul_comm]⟩
  · -- `27 ≤ x₂` (we show `x₂ ≥ 72`)
    have h4 : 4 ∣ p + 11 := four_dvd_p_add11 p hp_mod4
    have hx2mul : 4 * x₂ = p + 11 := by
      simpa [hx₂] using (Nat.mul_div_cancel' h4)
    have h4x2_mod : (4 * x₂) % 11 = 2 := by
      calc
        (4 * x₂) % 11 = (p + 11) % 11 := by simpa [hx2mul]
        _ = p % 11 := by simp [Nat.add_mod]
        _ = 2 := by simpa [hp_mod]
    have h36t_mod : (36 * t) % 11 = 2 := by
      have hEq : 4 * x₂ = 36 * t := by
        simp [ht, mul_assoc, mul_left_comm, mul_comm]
      simpa [hEq] using h4x2_mod
    have h144t_mod : (144 * t) % 11 = 8 := by
      have : (4 * (36 * t)) % 11 = 8 := by
        calc
          (4 * (36 * t)) % 11 = (4 % 11 * ((36 * t) % 11)) % 11 := by simp [Nat.mul_mod]
          _ = (4 * 2) % 11 := by simpa [h36t_mod]
          _ = 8 := by decide
      have hEq : 144 * t = 4 * (36 * t) := by
        simp [mul_assoc, mul_left_comm, mul_comm]
      simpa [hEq] using this
    have h144t_eq : (144 * t) % 11 = t % 11 := by
      calc
        (144 * t) % 11 = (144 % 11 * (t % 11)) % 11 := by simp [Nat.mul_mod]
        _ = (1 * (t % 11)) % 11 := by simp
        _ = t % 11 := by simp
    have ht_mod : t % 11 = 8 := by
      simpa [h144t_eq] using h144t_mod
    have ht_ge8 : 8 ≤ t := by
      have : t % 11 ≤ t := Nat.mod_le t 11
      simpa [ht_mod] using this
    have hx2_ge72 : 72 ≤ x₂ := by
      have : 9 * 8 ≤ 9 * t := Nat.mul_le_mul_left 9 ht_ge8
      have : 72 ≤ 9 * t := by simpa using this
      simpa [ht] using this
    exact le_trans (by decide : 27 ≤ 72) hx2_ge72
  · -- `(x₂+27) % 11 = 0`
    have h11_p108 : 11 ∣ p + 108 := by
      have : (p + 108) % 11 = 0 := by
        calc
          (p + 108) % 11 = (p % 11 + 108 % 11) % 11 := by
            simp [Nat.add_mod]
          _ = (2 + 9) % 11 := by
            simpa [hp_mod]
          _ = 0 := by decide
      exact Nat.dvd_of_mod_eq_zero this
    have h11_rhs : 11 ∣ p + 11 + 108 := by
      have : 11 ∣ (p + 108) + 11 := dvd_add h11_p108 (dvd_refl 11)
      simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using this
    have h4 : 4 ∣ p + 11 := four_dvd_p_add11 p hp_mod4
    have hx2mul : 4 * x₂ = p + 11 := by
      simpa [hx₂] using (Nat.mul_div_cancel' h4)
    have hmul : 4 * (x₂ + 27) = p + 11 + 108 := by
      calc
        4 * (x₂ + 27) = 4 * x₂ + 4 * 27 := by
          simp [mul_add]
        _ = (p + 11) + 108 := by simp [hx2mul]
        _ = p + 11 + 108 := by simp [Nat.add_assoc]
    have h11_mul : 11 ∣ 4 * (x₂ + 27) := by
      simpa [hmul] using h11_rhs
    have hcop : Nat.Coprime 11 4 := by decide
    have h11_x2 : 11 ∣ x₂ + 27 := hcop.dvd_of_dvd_mul_left h11_mul
    exact Nat.mod_eq_zero_of_dvd h11_x2

/-- k=2 works when `p ≡ 6 (mod 11)` and `v₃(x₂) ≥ 2` via `d = 81`,
    assuming `x₂ ≥ 81` (true in the Mordell-hard range). -/
lemma k2_works_p6_v3 (p : ℕ) (hp : Nat.Prime p) (hp_mod3 : p % 3 = 1) (hp_mod4 : p % 4 = 1)
    (hp_mod : p % 11 = 6) (hv3 : 9 ∣ (p + 11) / 4) (hx2_ge : 81 ≤ (p + 11) / 4) :
    let x₂ := (p + 11) / 4
    ∃ d, d ∣ x₂^2 ∧ d ≤ x₂ ∧ (x₂ + d) % 11 = 0 := by
  dsimp
  set x₂ : ℕ := (p + 11) / 4 with hx₂
  have hv3' : 9 ∣ x₂ := by simpa [hx₂] using hv3
  rcases hv3' with ⟨t, ht⟩
  have h81le : 81 ≤ x₂ := by
    simpa [hx₂] using hx2_ge
  refine ⟨81, ?_, h81le, ?_⟩
  · -- `81 ∣ x₂^2`
    refine ⟨t^2, by
      simp [ht, pow_two, mul_assoc, mul_left_comm, mul_comm]⟩
  · -- `(x₂+81) % 11 = 0`
    have h11_p324 : 11 ∣ p + 324 := by
      have : (p + 324) % 11 = 0 := by
        calc
          (p + 324) % 11 = (p % 11 + 324 % 11) % 11 := by
            simp [Nat.add_mod]
          _ = (6 + 5) % 11 := by
            simpa [hp_mod]
          _ = 0 := by decide
      exact Nat.dvd_of_mod_eq_zero this
    have h11_rhs : 11 ∣ p + 11 + 324 := by
      have : 11 ∣ (p + 324) + 11 := dvd_add h11_p324 (dvd_refl 11)
      simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using this
    have h4 : 4 ∣ p + 11 := four_dvd_p_add11 p hp_mod4
    have hx2mul : 4 * x₂ = p + 11 := by
      simpa [hx₂] using (Nat.mul_div_cancel' h4)
    have hmul : 4 * (x₂ + 81) = p + 11 + 324 := by
      calc
        4 * (x₂ + 81) = 4 * x₂ + 4 * 81 := by
          simp [mul_add]
        _ = (p + 11) + 324 := by simp [hx2mul]
        _ = p + 11 + 324 := by simp [Nat.add_assoc]
    have h11_mul : 11 ∣ 4 * (x₂ + 81) := by
      simpa [hmul] using h11_rhs
    have hcop : Nat.Coprime 11 4 := by decide
    have h11_x2 : 11 ∣ x₂ + 81 := hcop.dvd_of_dvd_mul_left h11_mul
    exact Nat.mod_eq_zero_of_dvd h11_x2

end K2Characterization
