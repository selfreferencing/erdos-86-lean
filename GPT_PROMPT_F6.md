# Lean 4 Task: Prove `good_ratio_bound` (good ratio ≈ 9/10)

## Environment
- **Lean**: `leanprover/lean4:v4.24.0`
- **Mathlib**: commit `f897ebcf72cd16f89ab4577d0c826cd14afaafc7`

## Task

Prove that the "good ratio" (fraction of survivors whose child-0 survives) is approximately 9/10, with explicit error bound. Return only the Lean 4 code.

## What to prove

```lean
import Mathlib

namespace Zeroless

-- Assume all definitions from Fourier_Proven.lean are available:
-- S4, S5, S_all, killed_index, good_set, survives, m, top_digit

-- Assumed results:
-- S5_subset_good : S5 k ⊆ good_set k  (all 5-child parents have child-0 surviving)
-- char_sum_bounded : character sum ≤ 25  (the single axiom)
-- discrepancy_from_char_bound : discrepancy ≤ 4C/5

/-- Among 4-child survivors, the count with killed_index = 0
    deviates from |S4|/5 by at most 20. -/
theorem S4_killed_zero_count (k : ℕ) (hk : k ≥ 1) :
    |((S4 k).filter (fun u => killed_index k u = ⟨0, by omega⟩)).card -
     (S4 k).card / 5| ≤ (20 : ℝ) := by
  sorry

/-- Child-0 survives for a 4-child parent iff killed_index ≠ 0 -/
theorem child0_survives_iff_killed_ne_zero (k : ℕ) (hk : k ≥ 1)
    (u : ZMod (5^(k+1))) (hu : u ∈ S4 k) :
    survives k (u * (m k)^0) ↔ killed_index k u ≠ ⟨0, by omega⟩ := by
  sorry

/-- The good set decomposes into S5 contribution + S4 contribution -/
theorem good_set_decomp (k : ℕ) (hk : k ≥ 1) :
    (good_set k).card =
      (S5 k).card +
      ((S4 k).filter (fun u => killed_index k u ≠ ⟨0, by omega⟩)).card := by
  sorry

/-- Main bound: |good_set| is approximately 9/10 of |S_all|.
    good_set = S5 + (S4 minus those with killed_index = 0)
    ≈ S5 + S4 - S4/5
    = S5 + 4·S4/5
    = S5 + 4(S_all - S5)/5
    = S5/5 + 4·S_all/5
    And S5/S_all ≈ 1/2 (from the tree dynamics), so good/S_all ≈ 1/10 + 4/5 = 9/10.

    But we don't assume S5/S_all = 1/2 exactly. Instead we bound:
    good = S5 + (4·S4/5 ± 20)
         = S5 + 4(S_all - S5)/5 ± 20
         = 4·S_all/5 + S5/5 ± 20
    So good/S_all = 4/5 + S5/(5·S_all) ± 20/S_all -/
theorem good_ratio_lower (k : ℕ) (hk : k ≥ 1) :
    ((good_set k).card : ℝ) ≥ 4 * (S_all k).card / 5 - 20 := by
  sorry

theorem good_ratio_upper (k : ℕ) (hk : k ≥ 1) :
    ((good_set k).card : ℝ) ≤ (S_all k).card - (S4 k).card / 5 + 20 := by
  sorry

end Zeroless
```

## Mathematical content

The "good set" consists of survivors u such that child-0 (= u * m^0 = u) also survives at the next digit position. This decomposes as:

- **5-child survivors (S5)**: ALL children survive, including child-0. So S5 ⊆ good_set.
- **4-child survivors (S4)**: Child-0 survives iff killed_index(u) ≠ 0.
  By the discrepancy bound: |{u ∈ S4 : killed_index = 0}| ≈ |S4|/5 (within ±20).

Therefore:
good_set = S5 + {u ∈ S4 : killed ≠ 0}
         = |S5| + |S4| - |{u ∈ S4 : killed = 0}|
         ≈ |S5| + |S4| - |S4|/5
         = |S5| + 4|S4|/5

Since S_all = S4 ∪ S5 (disjoint), |S4| = |S_all| - |S5|:
good ≈ |S5| + 4(|S_all| - |S5|)/5 = 4|S_all|/5 + |S5|/5

The lower bound: good ≥ 4|S_all|/5 - 20 (dropping the positive S5/5 term).
The upper bound: good ≤ |S_all| - |S4|/5 + 20 (using |{killed=0}| ≥ |S4|/5 - 20).

## Proof strategies

### S4_killed_zero_count

This is a direct application of `discrepancy_from_char_bound` with:
- S = S4 k
- g = killed_index k
- a = ⟨0, ...⟩
- C = 25 (from char_sum_bounded axiom)

```lean
theorem S4_killed_zero_count (k : ℕ) (hk : k ≥ 1) :
    |((S4 k).filter (fun u => killed_index k u = ⟨0, by omega⟩)).card -
     (S4 k).card / 5| ≤ (20 : ℝ) := by
  have h := discrepancy_from_char_bound (S4 k) (killed_index k) ⟨0, by omega⟩ 25 (by norm_num)
    (fun ℓ hℓ => char_sum_bounded k hk ℓ hℓ)
  linarith  -- 4 * 25 / 5 = 20
```

### child0_survives_iff_killed_ne_zero

```lean
theorem child0_survives_iff_killed_ne_zero ... := by
  constructor
  · intro hsurv heq
    -- If killed_index = 0, then child-0 does NOT survive (by killed_index_kills)
    have := killed_index_kills k hk u hu
    rw [heq] at this
    simp at this  -- m^0 = 1, u * 1 = u
    -- But hsurv says it does survive: contradiction
    exact this hsurv
  · intro hne
    -- If killed_index ≠ 0, then child-0 DOES survive
    -- (the only dead child is killed_index)
    by_contra h
    have := killed_index_unique k hk u hu ⟨0, by omega⟩ h
    exact hne this
```

### good_set_decomp

```lean
theorem good_set_decomp ... := by
  -- good_set k = S5 k ∪ {u ∈ S4 k : killed ≠ 0}
  -- These are disjoint (S4 and S5 are disjoint)
  -- Use Finset.card_union_eq_card_add_card for disjoint sets
  sorry
```

### good_ratio_lower

```lean
theorem good_ratio_lower ... := by
  -- good = S5 + (S4 - {killed=0})
  -- = S5 + S4 - {killed=0}
  -- ≥ S5 + S4 - (S4/5 + 20)  (by S4_killed_zero_count)
  -- = S5 + 4·S4/5 - 20
  -- ≥ 4·S4/5 - 20  (since S5 ≥ 0)
  -- = 4(S_all - S5)/5 - 20
  -- ≥ 4·S_all/5 - 4·S_all/5 - 20  (since S5 ≤ S_all)
  -- Hmm, need: S5 + 4·S4/5 ≥ 4·S_all/5
  -- S5 + 4(S_all-S5)/5 = S5 + 4·S_all/5 - 4·S5/5 = S5/5 + 4·S_all/5 ≥ 4·S_all/5
  rw [good_set_decomp k hk]
  have hcount := S4_killed_zero_count k hk
  -- |{killed=0}| ≤ S4/5 + 20
  -- So S4 - {killed=0} ≥ S4 - S4/5 - 20 = 4·S4/5 - 20
  -- good = S5 + 4·S4/5 - 20 ≥ S5/5 + 4·S_all/5 - 20 ≥ 4·S_all/5 - 20
  sorry -- real arithmetic from hcount
```

## API pitfalls

1. **`Fin.mk 0 (by omega)`**: Creates the element `⟨0, _⟩ : Fin 5`. The `by omega` proves `0 < 5`.
2. **`(m k)^0 = 1`**: By `pow_zero`. So `u * (m k)^0 = u * 1 = u`. Use `simp [pow_zero, mul_one]`.
3. **Casting**: `((n : ℕ) : ℝ)` for real-valued bounds. Need `Nat.cast_le`, `Nat.cast_add`, etc.
4. **`abs_le`**: `|a - b| ≤ c ↔ b - c ≤ a ∧ a ≤ b + c` for real-valued bounds.
5. **Disjoint union**: `Finset.card_union_eq` for `Disjoint A B → (A ∪ B).card = A.card + B.card`.
6. **`linarith`**: Should handle the real arithmetic once the key inequalities are established.

## Constraints
- Must compile with Lean 4.24.0 + specified Mathlib
- Return all theorems with proofs
- May assume results from F4 (discrepancy_from_char_bound) and F5 (killed_index properties)
- May use the axiom char_sum_bounded
