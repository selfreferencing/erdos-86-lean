# Lean 4 Task: Define `killed_index`, `S4`, `S5` and prove basic properties

## Environment
- **Lean**: `leanprover/lean4:v4.24.0`
- **Mathlib**: commit `f897ebcf72cd16f89ab4577d0c826cd14afaafc7`

## Task

Define the killed-index function for 4-child survivors and the survivor subsets S4, S5. Prove that killed_index correctly identifies the dead child and is unique. Return only the Lean 4 code.

## What to prove

```lean
import Mathlib

namespace Zeroless

open scoped BigOperators

/-- top_digit: the coefficient of 5^k in the 5-adic expansion -/
def top_digit (k : ℕ) (u : ZMod (5^(k+1))) : Fin 5 :=
  ⟨u.val / 5^k, by
    have hu : u.val < 5^k * 5 := by
      simpa [pow_succ] using (u.val_lt : u.val < (5 : ℕ)^(k+1))
    exact Nat.div_lt_of_lt_mul hu⟩

/-- survives: top digit is nonzero -/
def survives (k : ℕ) (u : ZMod (5^(k+1))) : Prop :=
  (top_digit k u).val ≠ 0

/-- m k: the multiplier 2^{T_k} mod 5^{k+1} -/
noncomputable def m (k : ℕ) : ZMod (5^(k+1)) :=
  (2 : ZMod (5^(k+1)))^(4 * 5^(k-1))

/-- 4-child survivors -/
def S4 (k : ℕ) : Finset (ZMod (5^(k+1))) :=
  Finset.univ.filter fun u =>
    (top_digit k u).val ≠ 0 ∧ u.val % 5^k % 5 ≠ 0

/-- 5-child survivors -/
def S5 (k : ℕ) : Finset (ZMod (5^(k+1))) :=
  Finset.univ.filter fun u =>
    (top_digit k u).val ≠ 0 ∧ u.val % 5^k % 5 = 0

/-- All survivors -/
def S_all (k : ℕ) : Finset (ZMod (5^(k+1))) :=
  Finset.univ.filter fun u => (top_digit k u).val ≠ 0

/-- S4 and S5 are disjoint -/
theorem S4_S5_disjoint (k : ℕ) : Disjoint (S4 k) (S5 k) := by
  sorry

/-- S4 ∪ S5 = S_all -/
theorem S4_union_S5 (k : ℕ) : S4 k ∪ S5 k = S_all k := by
  sorry

/-- Killed index: for a 4-child survivor u, this is the unique j ∈ Fin 5
    such that u * m^j has top digit = 0.
    Formula: j0 = -(hi) / (step * 3) in ZMod 5,
    where hi = u.val / 5^k, step = (u.val % 5^k) % 5. -/
def killed_index (k : ℕ) (u : ZMod (5^(k+1))) : Fin 5 :=
  let hi : ℕ := u.val / 5^k
  let lo_mod5 : ℕ := u.val % 5^k % 5
  let step5 : ZMod 5 := ((lo_mod5 : ℕ) : ZMod 5) * (3 : ZMod 5)
  let hi5 : ZMod 5 := (hi : ZMod 5)
  let j0z : ZMod 5 := (-hi5) * step5⁻¹
  ⟨j0z.val, j0z.val_lt⟩

/-- killed_index identifies a dead child: u * m^{killed_index} does NOT survive -/
theorem killed_index_kills (k : ℕ) (hk : k ≥ 1) (u : ZMod (5^(k+1)))
    (hu : u ∈ S4 k) :
    ¬survives k (u * (m k)^(killed_index k u).val) := by
  sorry

/-- killed_index is the UNIQUE dead child -/
theorem killed_index_unique (k : ℕ) (hk : k ≥ 1) (u : ZMod (5^(k+1)))
    (hu : u ∈ S4 k) (j : Fin 5) (hj : ¬survives k (u * (m k)^j.val)) :
    j = killed_index k u := by
  sorry

end Zeroless
```

## Mathematical content

From the proof of `four_or_five_children` in FiveAdic_Extended.lean:

1. **S4 vs S5**: A survivor u has step = (u.val % 5^k) % 5. If step = 0, all 5 children survive (S5). If step ≠ 0, exactly 4 children survive (S4).

2. **killed_index**: For u ∈ S4, the "digit map" is
   digit(j) = (hi : ZMod 5) + step5 * (j : ZMod 5)
   where hi = u.val / 5^k and step5 = ((u.val % 5^k) % 5 : ZMod 5) * 3.
   The unique root is j0 = (-hi) / step5 = (-hi) * step5⁻¹ in ZMod 5.

3. **Correctness**: From `product_zmod_eq` and the division/casting chain in
   FiveAdic_Extended.lean, u * m^j has top digit = (hi + lo * j * 3) % 5.
   Setting this to 0 gives j = killed_index.

## Proof strategies

### S4_S5_disjoint

```lean
theorem S4_S5_disjoint (k : ℕ) : Disjoint (S4 k) (S5 k) := by
  simp only [S4, S5, Finset.disjoint_filter]
  intro u _ ⟨_, hne⟩ ⟨_, heq⟩
  exact hne heq
```

### S4_union_S5

```lean
theorem S4_union_S5 (k : ℕ) : S4 k ∪ S5 k = S_all k := by
  ext u
  simp only [S4, S5, S_all, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
  · intro h
    by_cases hstep : u.val % 5^k % 5 = 0
    · right; exact ⟨h, hstep⟩
    · left; exact ⟨h, hstep⟩
```

### killed_index_kills

This follows the same argument as `hj0_zero` in `four_or_five_children`:
The digit at j0 is `(hi : ZMod 5) + step5 * (j0 : ZMod 5) = hi + step5 * ((-hi) * step5⁻¹) = hi + (-hi) = 0`.

Then the chain from `product_zmod_eq` through `val_of_small_nat` and `nat_add_mul_div` shows the top digit is 0, hence ¬survives.

```lean
theorem killed_index_kills (k : ℕ) (hk : k ≥ 1) (u : ZMod (5^(k+1)))
    (hu : u ∈ S4 k) :
    ¬survives k (u * (m k)^(killed_index k u).val) := by
  -- Extract properties from hu
  simp only [S4, Finset.mem_filter, Finset.mem_univ, true_and] at hu
  obtain ⟨hhi_ne, hstep_ne⟩ := hu
  -- Set up notation
  set hi := u.val / 5^k
  set lo_mod5 := u.val % 5^k % 5
  set step5 : ZMod 5 := ((lo_mod5 : ℕ) : ZMod 5) * 3
  set hi5 : ZMod 5 := (hi : ZMod 5)
  set j0 := killed_index k u
  -- The digit at j0 is 0
  -- This requires the product_zmod_eq chain (import from FiveAdic_Extended)
  sorry
```

### killed_index_unique

Same argument as `hj0_unique` in `four_or_five_children`: if digit(j) = 0 and step5 ≠ 0, then step5 * j = -hi, so j = (-hi) * step5⁻¹ = j0.

## API pitfalls

1. **`ZMod 5` has decidable equality**: `instance : DecidableEq (ZMod 5)` exists.
2. **`ZMod.inv`**: `(x : ZMod p)⁻¹` is computable for prime `p` (Mathlib provides this).
3. **`Finset.disjoint_filter`**: Useful for proving S4 and S5 are disjoint.
4. **Import chain**: This file should import FiveAdic_Extended.lean for `product_zmod_eq`, `val_of_small_nat`, `nat_add_mul_div`, and `four_or_five_children`.
5. **The proofs of `killed_index_kills` and `killed_index_unique`** essentially re-extract parts of the `four_or_five_children` proof. If possible, factor them out of that proof rather than re-proving.

## Constraints
- Must compile with Lean 4.24.0 + specified Mathlib
- Return all definitions and theorems
- May use results from FiveAdic_Extended.lean
