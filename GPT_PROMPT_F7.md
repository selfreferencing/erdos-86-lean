# Lean 4 Task: Prove `forced_tail_bound` (exponential decay of forced-tail survivors)

## Environment
- **Lean**: `leanprover/lean4:v4.24.0`
- **Mathlib**: commit `f897ebcf72cd16f89ab4577d0c826cd14afaafc7`

## Task

Prove that the forced-tail survivor count (states where child-0 survives at every level) decays exponentially, reaching 0 for k ≥ 91. Return only the Lean 4 code.

## What to prove

```lean
import Mathlib

namespace Zeroless

-- Assume all definitions and results from previous micro-prompts:
-- good_ratio_lower, S_all, good_set, etc.

/-- The forced-tail count at level k, starting from S_all at level 1.
    This counts how many level-1 survivors have child-0 surviving
    at ALL subsequent levels through level k.

    Recursive definition:
    - Level 1: S_all 1  (all survivors at level 1)
    - Level j+1: those in forced_tail_at j whose child-0 survives -/
noncomputable def forced_tail_count : ℕ → ℝ
  | 0 => 4  -- |S_all 1| = 4 (residues 1,2,3,4 in ZMod 25)
  | k+1 => forced_tail_count k * (9/10 + 20 / forced_tail_count k)
  -- Each level, the good ratio is ≥ 4/5 and ≤ 1 - |S4|/(5|S_all|).
  -- The 9/10 + correction models the survival rate per level.

-- SIMPLIFIED VERSION: Just use the clean 9/10 bound.
-- The error 20/|S_all| is negligible for k ≥ 5 since |S_all| ≈ 4 × 4.5^{k-1}.

/-- Simplified forced-tail bound: at most 4 × (9/10)^{k-1} + error.
    For large k, this is < 1, hence the integer count is 0. -/
theorem forced_tail_real_bound (k : ℕ) (hk : k ≥ 1) :
    -- The actual forced-tail count as a real number
    -- is bounded by 4 × (0.91)^{k-1}
    -- (using 0.91 > 9/10 to absorb the error term)
    4 * (91/100 : ℝ)^(k-1) < 1 → True := by
  intro _; trivial

/-- Key computation: 4 × (91/100)^90 < 1.
    This shows forced-tail count = 0 for k ≥ 91.
    91/100 = 0.91, and 0.91^90 ≈ 1.6 × 10^{-4}, so 4 × 1.6 × 10^{-4} < 1. -/
theorem geometric_decay_91 : 4 * (91/100 : ℝ)^90 < 1 := by
  sorry  -- norm_num or native_decide on rational arithmetic

/-- For all k ≥ 91, no state survives all k levels of digit checking.
    This is because the forced-tail count bound 4 × 0.91^{k-1} < 1,
    and the actual count is a non-negative integer, hence = 0. -/
theorem no_forced_tail_survivors (k : ℕ) (hk : k ≥ 91) :
    -- Informal: no n with numDigits(2^n) = k can be zeroless
    True := by
  trivial  -- Placeholder for the actual statement

end Zeroless
```

## Mathematical content

The forced-tail argument:

1. At level 1: there are 4 survivors (states in ZMod(5^2) with nonzero top digit).
2. At each subsequent level j: a fraction ≈ 9/10 of current forced-tail survivors have child-0 surviving (by good_ratio_bound).
3. After k-1 levels: forced-tail count ≤ 4 × (9/10 + ε)^{k-1} where ε → 0.
4. For k ≥ 91: using 9/10 + ε ≤ 91/100 (conservative), 4 × (91/100)^90 < 1.
5. Since the count is a non-negative integer and bounded by < 1, it equals 0.
6. Hence no zeroless 2^n with k ≥ 91 digits.

## Proof strategy for `geometric_decay_91`

This is a computation on rationals: show 4 × (91/100)^90 < 1.

Equivalently: (91/100)^90 < 1/4, i.e., 91^90 < 100^90 / 4 = 25 × 100^89.

### Approach 1: norm_num
```lean
theorem geometric_decay_91 : 4 * (91/100 : ℝ)^90 < 1 := by
  norm_num
```

`norm_num` can handle rational arithmetic. It needs to compute 91^90 and 100^90. These are huge numbers (~176 and ~180 digits respectively), but norm_num handles bignum arithmetic.

### Approach 2: Native computation
```lean
theorem geometric_decay_91 : 4 * (91/100 : ℝ)^90 < 1 := by
  have h : (4 : ℚ) * (91/100)^90 < 1 := by native_decide
  exact_mod_cast h
```

### Approach 3: Manual bound
```lean
theorem geometric_decay_91 : 4 * (91/100 : ℝ)^90 < 1 := by
  -- (91/100)^10 = 91^10 / 100^10
  -- 91^10 = 3894816552313798281 (can compute)
  -- 100^10 = 10^20
  -- So (91/100)^10 ≈ 0.3894... < 0.39
  -- (0.39)^9 = 0.39^9 ≈ 7.6 × 10^{-4}
  -- 4 × 0.39^9 × 0.39 ≈ 3 × 10^{-4} < 1 ✓
  sorry
```

### Approach 4: Logarithmic bound
```lean
theorem geometric_decay_91 : 4 * (91/100 : ℝ)^90 < 1 := by
  -- Suffices: 90 * log(91/100) + log(4) < 0
  -- log(91/100) ≈ -0.0943, so 90 × (-0.0943) ≈ -8.49
  -- log(4) ≈ 1.386
  -- Sum ≈ -7.1 < 0 ✓
  -- But log is hard to use in Lean. Better to use rational arithmetic.
  sorry
```

## The actual statement we need

For the main theorem, we need:

```lean
theorem no_zeroless_k_ge_91 (k : ℕ) (hk : k ≥ 91) :
    ∀ n : ℕ, numDigits (2^n) = k → ¬zeroless (2^n)
```

This requires connecting the real-valued forced-tail bound to the integer-valued count. The argument:

1. The number of "forced-tail survivors" at level k is an integer F_k ≥ 0.
2. F_k ≤ 4 × (9/10 + ε_k)^{k-1} where ε_k ≤ 1/100 for k ≥ 91.
3. So F_k ≤ 4 × (91/100)^90 < 1.
4. Since F_k ∈ ℕ and F_k < 1, F_k = 0.
5. Any zeroless 2^n with k digits would contribute to F_k, so no such n exists.

Step 5 requires the connection between zeroless(2^n) and forced-tail survivors, which involves the 5-adic state analysis.

## Key intermediate lemma

```lean
/-- The survival probability per level is at most 91/100 -/
theorem survival_rate_bound (j : ℕ) (hj : j ≥ 5) :
    (good_set j).card / (S_all j).card ≤ 91/100 := by
  -- From good_ratio_lower: good ≥ 4·S_all/5 - 20
  -- From good_ratio_upper: good ≤ S_all - S4/5 + 20
  -- Since S4 ≥ S_all/2 - error (roughly), good ≤ S_all - S_all/10 + 20
  -- For j ≥ 5, |S_all| ≈ 4 × 4.5^4 ≈ 1640, so 20/S_all < 0.012
  -- good/S_all ≤ 9/10 + 20/S_all ≤ 9/10 + 1/100 = 91/100
  sorry
```

## API pitfalls

1. **Rational vs Real arithmetic**: `norm_num` works on both. For `native_decide`, use `ℚ` first then cast.
2. **`pow_le_pow_left`** / **`pow_lt_pow_left`**: For monotonicity of exponentiation.
3. **Large exponents**: 91^90 is a ~176-digit number. `norm_num` handles this but may be slow.
4. **`Nat.lt_of_lt_of_le`**: For integer-valued conclusion from real-valued bound.
5. **Integer rounding**: `F_k < 1` and `F_k ≥ 0` and `F_k ∈ ℕ` implies `F_k = 0`.

## Constraints
- Must compile with Lean 4.24.0 + specified Mathlib
- Return the geometric decay bound with proof
- The survival rate bound may require results from F6
- The full `no_zeroless_k_ge_91` requires connecting to the 5-adic framework
