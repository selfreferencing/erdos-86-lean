import Mathlib

/-- The Mordell-hard residue classes mod 840. -/
def MordellHardClasses : Finset ℕ := {1, 121, 169, 289, 361, 529}

/-- A natural number `p` is Mordell-hard iff `p mod 840` lies in `MordellHardClasses`. -/
def isMordellHard (p : ℕ) : Prop := p % 840 ∈ MordellHardClasses

/-- Compute `x₅ = (p + 23) / 4` modulo 210, given `p mod 840`. -/
def x5_mod210 (p_mod840 : ℕ) : ℕ := ((p_mod840 + 23) / 4) % 210

/-- The six `x₅ (mod 210)` values for the six Mordell-hard residue classes. -/
lemma mordellHard_x5_classes :
    x5_mod210 1 = 6 ∧
    x5_mod210 121 = 36 ∧
    x5_mod210 169 = 48 ∧
    x5_mod210 289 = 78 ∧
    x5_mod210 361 = 96 ∧
    x5_mod210 529 = 138 := by
  native_decide

/-- `x₅ (mod 210)` set for Mordell-hard primes (computed from the six classes). -/
def MordellHard_x5_residues : Finset ℕ := {6, 36, 48, 78, 96, 138}

/-- `x₅ (mod 210)` depends only on `p (mod 840)` since `840 = 4 * 210`. -/
lemma x5_mod210_depends_on_mod840 (p : ℕ) :
    ((p + 23) / 4) % 210 = x5_mod210 (p % 840) := by
  unfold x5_mod210
  have hp : p = p % 840 + 840 * (p / 840) := (Nat.mod_add_div p 840).symm
  calc
    ((p + 23) / 4) % 210
        = (((p % 840 + 840 * (p / 840)) + 23) / 4) % 210 := by
            simpa [hp]
    _ = (((p % 840 + 23) + 840 * (p / 840)) / 4) % 210 := by
            have hnum :
                (p % 840 + 840 * (p / 840)) + 23 = (p % 840 + 23) + 840 * (p / 840) := by
              ac_rfl
            simpa [hnum]
    _ = (((p % 840 + 23) + 4 * (210 * (p / 840))) / 4) % 210 := by
            have h840 : (840 : ℕ) = 4 * 210 := by native_decide
            simp [h840, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
    _ = (((p % 840 + 23) / 4 + 210 * (p / 840)) % 210) := by
            -- (a + 4*c) / 4 = a/4 + c
            simp [Nat.add_mul_div_left, Nat.mul_assoc]
    _ = ((p % 840 + 23) / 4) % 210 := by
            -- (t + 210*k) % 210 = t % 210
            calc
              (((p % 840 + 23) / 4 + 210 * (p / 840)) % 210)
                  =
                  ((((p % 840 + 23) / 4) % 210 + (210 * (p / 840)) % 210) % 210) := by
                    simpa [Nat.add_mod]
              _ = (((p % 840 + 23) / 4) % 210 + 0) % 210 := by
                    simp
              _ = ((p % 840 + 23) / 4) % 210 := by
                    simp

/-- If `r` is one of the Mordell-hard classes, then `x₅ (mod 210)` is one of the six residues. -/
lemma x5_mod210_mem_residues_of_mem_classes {r : ℕ} (hr : r ∈ MordellHardClasses) :
    x5_mod210 r ∈ MordellHard_x5_residues := by
  have hr' :
      r = 1 ∨ r = 121 ∨ r = 169 ∨ r = 289 ∨ r = 361 ∨ r = 529 := by
    simpa [MordellHardClasses] using hr
  rcases hr' with rfl | rfl | rfl | rfl | rfl | rfl <;> native_decide

/-- For Mordell-hard `p`, `x₅ (mod 210)` lies in the restricted residue set. -/
lemma mordellHard_x5_in_residues (p : ℕ) (hp : isMordellHard p) :
    ((p + 23) / 4) % 210 ∈ MordellHard_x5_residues := by
  have h : x5_mod210 (p % 840) ∈ MordellHard_x5_residues :=
    x5_mod210_mem_residues_of_mem_classes (r := p % 840) hp
  simpa [x5_mod210_depends_on_mod840 (p := p)] using h

/-- All residues in `MordellHard_x5_residues` are divisible by 3. -/
lemma three_dvd_of_mem_MordellHard_x5_residues {r : ℕ} (hr : r ∈ MordellHard_x5_residues) :
    3 ∣ r := by
  have hr' :
      r = 6 ∨ r = 36 ∨ r = 48 ∨ r = 78 ∨ r = 96 ∨ r = 138 := by
    simpa [MordellHard_x5_residues] using hr
  rcases hr' with rfl | rfl | rfl | rfl | rfl | rfl <;> native_decide

/-- 3 divides `x₅` for all Mordell-hard `p` (since `210` is a multiple of `3` and all residues are). -/
lemma three_divides_x5_mordellHard (p : ℕ) (hp : isMordellHard p) :
    3 ∣ (p + 23) / 4 := by
  let x : ℕ := (p + 23) / 4
  have hxres : x % 210 ∈ MordellHard_x5_residues := by
    simpa [x] using mordellHard_x5_in_residues p hp
  have hxmod3 : 3 ∣ x % 210 :=
    three_dvd_of_mem_MordellHard_x5_residues hxres
  have h210 : 3 ∣ (210 : ℕ) := by native_decide
  have hxmul : 3 ∣ x / 210 * 210 := by
    exact dvd_mul_of_dvd_right h210 (x / 210)
  have hsum : 3 ∣ x / 210 * 210 + x % 210 := by
    exact dvd_add hxmul hxmod3
  have hx : 3 ∣ x := by
    -- x / 210 * 210 + x % 210 = x
    simpa [Nat.div_add_mod x 210] using hsum
  simpa [x] using hx

/-- Divisibility by 2 for each residue (useful for case splits). -/
lemma x5_divisibility_by_2 :
    2 ∣ 6 ∧ 2 ∣ 36 ∧ 2 ∣ 48 ∧ 2 ∣ 78 ∧ 2 ∣ 96 ∧ 2 ∣ 138 := by
  native_decide

/-- Divisibility by 3 for each residue (useful for case splits). -/
lemma x5_divisibility_by_3 :
    3 ∣ 6 ∧ 3 ∣ 36 ∧ 3 ∣ 48 ∧ 3 ∣ 78 ∧ 3 ∣ 96 ∧ 3 ∣ 138 := by
  native_decide

/-- For each Mordell-hard residue class, record which small primes divide `x₅`. -/
structure X5DivisibilityData where
  p_mod840 : ℕ
  x5_mod210 : ℕ
  div_by_2 : Bool
  div_by_3 : Bool
  div_by_5 : Bool
  div_by_7 : Bool

/-- A hand-written table matching the six Mordell-hard cases. -/
def mordellHardDivisibilityTable : List X5DivisibilityData := [
  ⟨1,   6,   true, true, false, false⟩,
  ⟨121, 36,  true, true, false, false⟩,
  ⟨169, 48,  true, true, false, false⟩,
  ⟨289, 78,  true, true, false, false⟩,
  ⟨361, 96,  true, true, false, false⟩,
  ⟨529, 138, true, true, false, false⟩
]
