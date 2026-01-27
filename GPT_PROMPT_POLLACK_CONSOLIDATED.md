# Consolidated Prompt: Formalize pollack_bound

## Context

You are GPT 5.2 working in Lean 4 + Mathlib (January 2026). The ESC (Erdős-Straus Conjecture) formalization has one remaining axiom:

```lean
axiom pollack_bound (p : ℕ) (hp : Nat.Prime p) (hp_mod : p % 4 = 1) (hp_ge : p ≥ 5) :
    ∃ q : ℕ, Nat.Prime q ∧ q % 4 = 3 ∧ q ≤ (p + 1) / 2
```

## Critical Insight

**This axiom is trivially provable with witness q = 3.**

For any p ≥ 5:
- `Nat.Prime 3` ✓
- `3 % 4 = 3` ✓
- `3 ≤ (p + 1) / 2` ✓ (since p ≥ 5 implies (p+1)/2 ≥ 3)

**Validation:** The axiom does NOT encode a quadratic nonresidue condition. Proof: for p = 13, q = 3 is the only candidate (prime, ≡ 3 mod 4, ≤ 7), but 3 is a QR mod 13 (since 4² ≡ 3 mod 13). If QNR were required, the axiom would be false. The QNR property is derived elsewhere via quadratic reciprocity.

## Task

Produce a **single self-contained Lean 4 file** that:
1. Proves `pollack_bound` as a theorem (exact same signature as the axiom)
2. Compiles without errors
3. Uses no `sorry`
4. Can be dropped into the ESC project as a replacement

## Proof Strategy

```lean
theorem pollack_bound (p : ℕ) (hp : Nat.Prime p) (hp_mod : p % 4 = 1) (hp_ge : p ≥ 5) :
    ∃ q : ℕ, Nat.Prime q ∧ q % 4 = 3 ∧ q ≤ (p + 1) / 2 := by
  refine ⟨3, ?_, ?_, ?_⟩
  · -- Nat.Prime 3
    exact Nat.prime_three  -- or: decide
  · -- 3 % 4 = 3
    native_decide  -- or: rfl / decide
  · -- 3 ≤ (p + 1) / 2
    -- From hp_ge : 5 ≤ p, derive 6 ≤ p + 1, then 3 ≤ (p + 1) / 2
    [YOUR PROOF HERE]
```

**For the inequality `3 ≤ (p + 1) / 2`, use ONE of these approaches:**

**Option A (recommended):** Use `omega`
```lean
omega
```

**Option B:** Use `Nat.le_div_iff_mul_le`
```lean
rw [Nat.le_div_iff_mul_le (by norm_num : 0 < 2)]
-- Now prove 3 * 2 ≤ p + 1, i.e., 6 ≤ p + 1
linarith
```

**Option C:** Use monotonicity
```lean
have h6 : 6 ≤ p + 1 := by linarith
calc 3 = 6 / 2 := by norm_num
     _ ≤ (p + 1) / 2 := Nat.div_le_div_right h6
```

**Option D:** Direct calculation
```lean
have h : 6 ≤ p + 1 := Nat.add_le_add_right hp_ge 1
exact Nat.div_le_div_right h ▸ (by norm_num : 3 ≤ 6 / 2)
```

## Constraints

- Lean 4 + current Mathlib
- No `sorry`
- Hypotheses `hp` and `hp_mod` may be unused (that's fine)
- Keep imports minimal: `import Mathlib` or `import Mathlib.Data.Nat.Prime` + `import Mathlib.Tactic`

## Output Format

Provide the complete Lean file in a single code block:

```lean
import Mathlib

theorem pollack_bound (p : ℕ) (hp : Nat.Prime p) (hp_mod : p % 4 = 1) (hp_ge : p ≥ 5) :
    ∃ q : ℕ, Nat.Prime q ∧ q % 4 = 3 ∧ q ≤ (p + 1) / 2 := by
  refine ⟨3, ?_, ?_, ?_⟩
  · exact Nat.prime_three
  · native_decide
  · omega  -- or your preferred approach
```

## Verification Checklist

After producing the code:

1. `lake env lean PollackBound.lean` compiles
2. `#check pollack_bound` shows the correct type
3. No `sorry` in the file
4. The signature matches the axiom exactly

## Integration Step (for human)

Once verified, in `esc_complete_aristotle.lean`:
1. Delete/comment the `axiom pollack_bound ...` line
2. Paste the theorem proof in its place (or import the new file)
3. Run `lake build`
4. Run `#print axioms esc_all_primes` to confirm `pollack_bound` no longer appears

---

**Now produce the complete Lean file.**
