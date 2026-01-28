# GPT Prompt: Fill `exists_good_A_and_divisor` in Lean 4

## Task

Fill the single `sorry` in the theorem `exists_good_A_and_divisor` in
`ErdosStraus/ED2/ExistsGoodDivisor.lean`. This is the last mathematical
sorry blocking the Erdős-Straus conjecture formalization for primes
p ≡ 1 (mod 4).

## The theorem to prove

```lean
theorem exists_good_A_and_divisor (p : ℕ) (hp : Nat.Prime p) (hp4 : p % 4 = 1) :
    ∃ A d : ℕ,
      (p + 3) / 4 ≤ A ∧
      A ≤ (3 * p - 3) / 4 ∧
      0 < d ∧
      d ∣ A ^ 2 ∧
      (4 * A - p) ∣ (d + A) := by
  sorry
```

In words: for every prime p ≡ 1 (mod 4), there exist natural numbers A and d
such that:
1. A is in the window [(p+3)/4, (3p-3)/4]
2. d > 0
3. d divides A²
4. Setting δ = 4A - p, we have δ | (d + A)

Condition 4 is equivalent to: d ≡ -A (mod δ).

## Mathematical context

### What this theorem is used for

Once proved, `exists_good_A_and_divisor` feeds into the already-proven chain:
- `divisor_gives_type2`: converts (A, d) into a Type II Egyptian fraction solution
- `ed2_from_good_divisor`: combines with `divisor_gives_type2` to produce
  `∃ offset b c, offset % 4 = 3 ∧ b > 0 ∧ c > 0 ∧ (p + offset)(b + c) = 4·offset·b·c`

The downstream code is fully proven. Only this sorry remains.

### Available Mathlib lemma: Fermat's two-square theorem

```lean
-- In Mathlib.NumberTheory.SumTwoSquares
-- NOTE: Uses [Fact p.Prime] typeclass, NOT (hp : Nat.Prime p)
-- You must write: haveI : Fact (Nat.Prime p) := ⟨hp⟩
theorem Nat.Prime.sq_add_sq {p : ℕ} [Fact p.Prime] (hp : p % 4 ≠ 3) :
    ∃ a b : ℕ, a ^ 2 + b ^ 2 = p
```

Since p ≡ 1 (mod 4) implies p % 4 = 1 ≠ 3, this applies. It gives
natural numbers a, b ≥ 0 with a² + b² = p. Since p ≥ 5, both a, b ≥ 1.

To import: add `import Mathlib.NumberTheory.SumTwoSquares` to the file.

### Available theorem: Thue's lemma (already proven in ThueLemma.lean)

```lean
-- In ErdosStraus.ED2.ThueLemma
theorem thue_lemma
    {p : ℕ} (hp : Nat.Prime p) {r : ZMod p} (hr : r ≠ 0) :
    ∃ x y : ℤ,
      0 < x ^ 2 + y ^ 2 ∧
      x ^ 2 + y ^ 2 ≤ (2 * (p - 1) : ℤ) ∧
      (p : ℤ) ∣ (y - (r.val : ℤ) * x)
```

### Available: square root of -1 mod p

```lean
-- In Mathlib.NumberTheory.LegendreSymbol.Basic
-- Needs [Fact p.Prime] typeclass
theorem ZMod.exists_sq_eq_neg_one_iff :
    IsSquare (-1 : ZMod p) ↔ p % 4 ≠ 3
```

`IsSquare (-1 : ZMod p)` means `∃ r : ZMod p, r ^ 2 = -1` (or equivalently
`∃ r, r * r = -1` depending on how `IsSquare` unfolds).

### Mathematical sketch: from Fermat two-square to (A, d)

Given p prime with p ≡ 1 (mod 4), Fermat gives p = a² + b² with a, b > 0.

The challenge is constructing A in the window [(p+3)/4, (3p-3)/4] and d | A²
with (4A - p) | (d + A). Setting δ = 4A - p:

**Why the simplest approach fails:** Setting A = (p+3)/4 gives δ = 3. This
works when A has a divisor ≡ -A (mod 3), which fails when A ≡ 1 (mod 3) and
all prime factors of A are ≡ 1 (mod 3). This happens for p ≡ 1 (mod 12).

**Known working constructions (from the computational certificate):**
- p ≡ 5 (mod 8): α = (p+3)/8, d' = 1, b' = 1, c' = 2
  → A = (p+3)/4, δ = 3, d = (p+3)/8
- p ≡ 2 (mod 3): α = 1, d' = 1, b' = (p+1)/3, c' = 1
  → A = (p+1)/3, δ = (p+4)/3, d = ((p+1)/3)²
- p ≡ 1 (mod 24): requires case analysis (the hard case)

**Possible proof strategy using Fermat two-square:**

With p = a² + b², you might construct A and d from a and b. Some candidates
to explore:
- A related to ab, a², b², or linear combinations
- d constructed from the factorization structure
- δ chosen to have a known relationship with a, b

The proof likely needs to split into cases based on residues of a, b modulo
small numbers, using the Fermat decomposition to ensure the divisibility
conditions hold.

**Alternative strategy: use Thue's lemma directly (not via Fermat).**

Choose r ∈ ZMod p strategically (not necessarily √(-1)). Thue gives x, y
with p | (y - r·x) and 0 < x² + y² ≤ 2(p-1). The construction of A
from x, y might be more direct.

## Lean 4.27 / Mathlib API notes (CRITICAL)

These are real errors we hit when building this project. Pay attention:

1. **`Nat.Prime` vs `[Fact p.Prime]`:** The file uses `(hp : Nat.Prime p)`.
   Mathlib's `Nat.Prime.sq_add_sq` uses `[Fact p.Prime]`. Bridge with:
   ```lean
   haveI : Fact (Nat.Prime p) := ⟨hp⟩
   ```

2. **`sq` rewriting direction:** `sq` rewrites `a ^ 2` to `a * a`. Use
   `rw [sq]` to go from `a ^ 2` to `a * a`, and `rw [← sq]` for the reverse.

3. **`obtain` and equation direction:** `obtain ⟨e, he⟩ := (hdvd : d ∣ n)`
   produces `he : n = d * e` (note: n on the LEFT). If you need `d * e = n`,
   use `he.symm`.

4. **`omega` doesn't unfold definitions.** If you need omega to work with a
   definition, `simp only [defName]` first.

5. **`exact_mod_cast` is directional.** If the goal is `(↑a : ℤ) = (↑b : ℤ)`
   and you have `h : a = b` in ℕ, use `exact_mod_cast h`. If `h` has the
   equation backwards, use `exact_mod_cast h.symm`.

6. **`Nat.dvd_sub` (not `Nat.dvd_sub'`).** The old name was deprecated.

7. **`push_neg` is very useful** for negating complex goals.

8. **`nlinarith` handles nonlinear arithmetic** (products, squares) better
   than `linarith` or `omega`. Use `nlinarith only [h1, h2, ...]` with
   explicit hypotheses for best results.

9. **`positivity` closes goals of the form `0 < expr` or `0 ≤ expr`.**

10. **`norm_cast` and `push_cast`** handle ℕ ↔ ℤ coercion goals.

11. **Working with `ZMod`:** Key lemmas:
    - `ZMod.val_natCast (n a : ℕ) : (a : ZMod n).val = a % n`
    - `ZMod.intCast_zmod_eq_zero_iff_dvd (a : ℤ) (b : ℕ) : (a : ZMod b) = 0 ↔ (b : ℤ) ∣ a`

12. **`import Mathlib.Tactic`** is already in the file and provides `linarith`,
    `nlinarith`, `omega`, `positivity`, `norm_cast`, `push_cast`, `ring`, etc.

## File structure

The proof goes in `ErdosStraus/ED2/ExistsGoodDivisor.lean`. Current imports:
```lean
import Mathlib.Tactic
import ErdosStraus.ED2.Phase3
```

You may add additional imports (e.g., `import Mathlib.NumberTheory.SumTwoSquares`
or `import ErdosStraus.ED2.ThueLemma`).

The file is in `namespace ED2`.

## Working proof examples from this codebase

These proofs COMPILE on Lean 4.27 + current Mathlib. Use them as style guides.

### Example 1: coprime_A_delta (from this file)

```lean
theorem coprime_A_delta (p A : ℕ) (hp : Nat.Prime p)
    (hA_pos : 0 < A) (hA_lt : A < p) (hA_win : p < 4 * A) :
    Nat.Coprime A (4 * A - p) := by
  have h_coprime : Nat.gcd A p = 1 := by
    apply Nat.Coprime.symm
    exact hp.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt hA_pos hA_lt)
  have h_div_p : ∀ d, d ∣ A → d ∣ (4 * A - p) → d ∣ p := by
    intros d hdA hd4A_minus_p
    have hd4A : d ∣ 4 * A := hdA.mul_left _
    have := Nat.dvd_sub hd4A hd4A_minus_p
    rwa [Nat.sub_sub_self (by linarith)] at this
  refine' Nat.coprime_of_dvd' _
  exact fun k hk hkA hk' => h_coprime ▸ Nat.dvd_gcd hkA (h_div_p k hkA hk') |>
    fun h => by have := Nat.le_of_dvd (by linarith) h; interval_cases k <;> trivial
```

### Example 2: complementary_divisor_cong (from this file)

```lean
theorem complementary_divisor_cong (A d e δ : ℕ)
    (hde : d * e = A * A)
    (hmod : δ ∣ (d + A))
    (hcop : Nat.Coprime A δ) :
    δ ∣ (e + A) := by
  have h_cong : A * (e + A) ≡ 0 [MOD δ] := by
    have h_cong : (-A : ℤ) * e ≡ A * A [ZMOD δ] := by
      rw [Int.modEq_iff_dvd]
      obtain ⟨k, hk⟩ := hmod; use k * e; nlinarith
    have h_rearrange : A * (e + A) ≡ 0 [ZMOD δ] := by
      convert h_cong.neg.add_right (A * A) using 1 <;> ring
    exact Int.natCast_modEq_iff.mp h_rearrange
  exact hcop.symm.dvd_of_dvd_mul_left <| Nat.dvd_of_mod_eq_zero h_cong
```

### Example 3: Thue's lemma cardinality bound (from ThueLemma.lean)

```lean
  have hcard : Fintype.card (ZMod p) < Fintype.card (S × S) := by
    have h_p_le_m2_plus_2m : p ≤ m ^ 2 + 2 * m := by
      have h_p_le_m2_plus_2m_plus_1 : p ≤ m ^ 2 + 2 * m + 1 := by
        linarith [Nat.sub_add_cancel hp.pos, Nat.lt_succ_sqrt (p - 1)]
      rcases h_p_le_m2_plus_2m_plus_1.eq_or_lt with h | h
      · exact absurd ⟨m + 1, by linarith⟩ hp.not_isSquare
      · omega
    have h_p_lt_m_plus_1_sq : p < (m + 1) ^ 2 := by linarith
    convert h_p_lt_m_plus_1_sq using 1
    · exact ZMod.card p
    · norm_num [sq]; rw [Fintype.card_fin]
```

## What NOT to do

1. **Do NOT use `sorry`** in the output. The whole point is to eliminate the sorry.
2. **Do NOT use `native_decide` or `decide`** for this theorem — it quantifies
   over all primes, not a finite set.
3. **Do NOT modify other theorems** in the file. Only fill the sorry at line 57.
4. **Do NOT use deprecated API names** like `Nat.dvd_sub'`, `Fin.val_fin_lt`, etc.
5. **Do NOT use `simp_all +decide [...]`** as a catch-all — it often either does
   too much or too little on Lean 4.27.

## Deliverable

Provide the complete proof term that replaces `sorry` on line 57. The proof
should:
- Start after `by` (tactic mode)
- Use only imports available in the file (plus any new ones you specify)
- Compile on Lean 4 (leanprover--lean4---v4.27.0-rc1) with current Mathlib
- Handle ALL primes p ≡ 1 (mod 4), including the hard case p ≡ 1 (mod 24)

If you need helper lemmas, define them BEFORE the theorem in the same file
(inside `namespace ED2`).

## Secondary goal (if feasible)

After filling `exists_good_A_and_divisor`, the downstream chain works but
there is still a separate sorry at `ed2_dyachenko_params_exist` in Phase3.lean.
The TopLevel.lean file calls `ed2_dyachenko_params_exist`, not
`ed2_from_good_divisor`.

To eliminate ALL sorrys, one option is to modify `ed2_large_params` in
TopLevel.lean to call through `ed2_from_good_divisor` instead. This would
require changing its output type from `∃ α d' b' c' : ℕ, ...` (Dyachenko
format) to `∃ offset b c : ℕ, offset % 4 = 3 ∧ ...` (Type II format).

If you can propose the TopLevel.lean restructuring too, that would close
everything. But the primary goal is filling `exists_good_A_and_divisor`.
