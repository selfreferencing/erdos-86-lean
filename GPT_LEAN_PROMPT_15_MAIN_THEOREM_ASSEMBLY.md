# TASK: Assemble the Main Theorem k10_covers_hard10 in Lean 4

## Context

You have been provided with Lean 4 code for the following components:
- GCD coupling lemma: gcd(r+a, r+b) | |a-b|
- Complement trick: d ≡ -x (mod m) ⟹ d' = x²/d also ≡ -x (mod m), and min(d, d') ≤ x
- k=0 characterization: works ⟺ x_0 has prime factor ≡ 2 (mod 3)
- k=1 characterization: works ⟺ x_1 has NQR prime factor mod 7
- k=2 characterization: unconditional cases + v_3 conditions
- Small prime breakers: 3|x_7, 3|x_19, 5|x_14, 7|x_5
- A·A framework: witness ⟺ -x_k ∈ A_k · A_k
- Mod 210 case split: 6 Mordell-hard residue classes

## The Main Theorem

```lean
theorem k10_covers_hard10 (p : ℕ) (hp : Nat.Prime p) (h10 : Hard10 p) :
    ∃ k ∈ K10, TypeII_witness k p := by
  sorry
```

Where:
- `Hard10 p` := `MordellHard p ∧ ¬TypeII_k0 p ∧ ¬TypeII_k1 p ∧ ¬TypeII_k2 p`
- `K10` := `{5, 7, 9, 11, 14, 17, 19, 23, 26, 29}`
- `TypeII_witness k p` := `∃ d, d ∣ x_k² ∧ d ≤ x_k ∧ d ≡ -x_k [MOD m_k]`

## Proof Strategy

### Step 1: Extract Negative Conditions from Hard10

```lean
-- From ¬TypeII_k0 p, extract: ∀ q | x_0, q ≢ 2 (mod 3)
-- This means all prime factors of x_0 are ≡ 1 (mod 3)

-- From ¬TypeII_k1 p, extract: ∀ q | x_1, (q/7) = +1
-- This means all prime factors of x_1 are in {1, 2, 4} mod 7

-- From ¬TypeII_k2 p, extract specific conditions on x_2
```

### Step 2: Derive Positive Implications

The key insight: if k=0,1,2 all fail, this severely constrains p and x_k.

```lean
-- Lemma: Hard10 p → 7 | x_5
-- Proof: From MordellHard, p ≡ 1 (mod 840), so r ≡ 1 (mod 210)
--        x_5 = r + 5 ≡ 6 (mod 210), hence 7 | x_5

-- Lemma: 7 | x_5 → TypeII_witness 5 p (for Hard10 primes)
-- Proof: 7 is a primitive root mod 23, so ⟨7⟩ = (ℤ/23ℤ)*
--        Therefore -x_5 mod 23 is always in A_5 · A_5
```

### Step 3: Case Split on Mod 210

```lean
-- Split into 6 cases based on r mod 210
-- For each case, identify which k ∈ K10 has a guaranteed witness

lemma case_r_mod_210_eq_1 (p : ℕ) (hp : Nat.Prime p) (h10 : Hard10 p)
    (hr : (p + 3) / 4 % 210 = 1) : TypeII_witness 5 p := by
  -- x_5 = r + 5 ≡ 6 (mod 210)
  -- 6 = 2 × 3, so x_5 has small factors
  -- Check: 2 or 3 generates full group mod 23?
  -- ord_23(2) = 11, ord_23(3) = 11
  -- Together they generate full group
  sorry

-- Similar for other 5 cases
```

### Step 4: The Cascade Argument

```lean
-- For each residue class, prove by cascade:
-- Either k=5 works (64% of cases), or
-- k=5 fails → k=7 works (21% of remainder), or
-- k=5,7 fail → k=9 works, etc.

-- Key: the conditions for k_i failure IMPLY k_j success for j > i
```

## YOUR TASK

Write Lean 4 code that:

1. **Imports all component lemmas** (assume they're in namespace `ErdosStraus`)

2. **States and proves the main theorem** using the component lemmas

3. **Handles all 6 mod 210 cases** with explicit case analysis

4. **Uses the cascade structure** where appropriate

## Template

```lean
import Mathlib
import ErdosStraus.Basic
import ErdosStraus.GCDCoupling
import ErdosStraus.ComplementTrick
import ErdosStraus.SmallKCharacterizations
import ErdosStraus.SmallPrimeBreakers
import ErdosStraus.AAFramework
import ErdosStraus.Mod210Setup

namespace ErdosStraus

/-- Main theorem: K10 covers all Hard10 primes -/
theorem k10_covers_hard10 (p : ℕ) (hp : Nat.Prime p) (h10 : Hard10 p) :
    ∃ k ∈ K10, TypeII_witness k p := by
  -- Step 1: Get the residue class
  obtain ⟨r, hr_def, hr_class⟩ := hard10_residue_class p hp h10

  -- Step 2: Case split on r mod 210
  rcases hr_class with h1 | h31 | h43 | h73 | h91 | h133

  -- Case 1: r ≡ 1 (mod 210)
  · exact ⟨5, by decide, witness_k5_case1 p hp h10 h1⟩

  -- Case 2: r ≡ 31 (mod 210)
  · exact ⟨5, by decide, witness_k5_case2 p hp h10 h31⟩

  -- ... (remaining cases)

  sorry

end ErdosStraus
```

## Deliverables

1. Complete Lean 4 proof of `k10_covers_hard10`
2. Helper lemmas for each of the 6 mod 210 cases
3. Documentation of which k ∈ K10 is used for each case
4. Any additional helper lemmas needed to bridge the components

## Note on Decidability

Some of the case analysis may require computational verification. If so:
- Use `native_decide` or `decide` for small finite checks
- For larger checks, use `norm_num` or explicit calculation lemmas
- Document any assumptions that require external verification
