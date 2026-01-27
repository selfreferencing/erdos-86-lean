# Lean 4 Task: Prove `mod_cast_eq_digit` (the ZMod 5 coefficient equality)

## Environment
- **Lean**: `leanprover/lean4:v4.24.0`
- **Mathlib**: commit `f897ebcf72cd16f89ab4577d0c826cd14afaafc7`

## Task

Prove that `((hi + lo * j * 3) % 5 : ZMod 5) = (hi : ZMod 5) + ((lo % 5 : ℕ) : ZMod 5) * (3 : ZMod 5) * (j : ZMod 5)`. This shows that the natural number mod-5 reduction equals the `digit` function used in the theorem. Return only the Lean 4 code.

## What to prove

```lean
import Mathlib

lemma mod_cast_eq_digit (hi lo j : ℕ) :
    ((hi + lo * j * 3) % 5 : ℕ) = (hi : ZMod 5) + ((lo % 5 : ℕ) : ZMod 5) * (3 : ZMod 5) * (j : ZMod 5) := by
  sorry
```

Wait -- the LHS is `ℕ` and the RHS is `ZMod 5`. Let me fix the types. Both sides should be in `ZMod 5`:

```lean
import Mathlib

lemma mod_cast_eq_digit (hi lo j : ℕ) :
    (((hi + lo * j * 3) % 5 : ℕ) : ZMod 5) =
      (hi : ZMod 5) + ((lo % 5 : ℕ) : ZMod 5) * (3 : ZMod 5) * (j : ZMod 5) := by
  sorry
```

## Mathematical content

In `ZMod 5`, casting `n % 5` is the same as casting `n` (since `ZMod.natCast_mod`). So:
- LHS: `((hi + lo * j * 3) % 5 : ZMod 5) = (hi + lo * j * 3 : ZMod 5)`
- RHS: `(hi : ZMod 5) + ((lo % 5) : ZMod 5) * 3 * (j : ZMod 5) = (hi : ZMod 5) + (lo : ZMod 5) * 3 * (j : ZMod 5)`

And `(hi + lo * j * 3 : ZMod 5) = (hi : ZMod 5) + (lo : ZMod 5) * (j : ZMod 5) * (3 : ZMod 5)` by `push_cast` and `ring`.

So LHS = `(hi : ZMod 5) + (lo : ZMod 5) * (j : ZMod 5) * (3 : ZMod 5)` and RHS = `(hi : ZMod 5) + (lo : ZMod 5) * (3 : ZMod 5) * (j : ZMod 5)`. These are equal by commutativity (`ring`).

## Step-by-step proof strategy

1. Simplify `((n % 5 : ℕ) : ZMod 5) = (n : ZMod 5)` on both sides using `ZMod.natCast_mod` or `Nat.cast_mod_cast`.
2. Push casts through arithmetic: `(a + b : ZMod 5) = (a : ZMod 5) + (b : ZMod 5)`, `(a * b : ZMod 5) = (a : ZMod 5) * (b : ZMod 5)`.
3. Close with `ring`.

## Useful Mathlib lemmas

- `ZMod.natCast_self_eq_zero` : `((n : ℕ) : ZMod n) = 0`
- `Nat.cast_mod_cast` or `ZMod.natCast_mod` : `((a % n : ℕ) : ZMod n) = (a : ZMod n)` -- this might be called `ZMod.natCast_mod` or obtainable via `CharP.cast_eq_zero_iff`.
- Actually the key fact is: in `ZMod n`, `((a % n : ℕ) : ZMod n) = ((a : ℕ) : ZMod n)`. This follows from: `(a : ZMod n) = (a % n + n * (a / n) : ZMod n) = (a % n : ZMod n) + (n * (a/n) : ZMod n) = (a % n : ZMod n) + 0 = (a % n : ZMod n)`, since `(n : ZMod n) = 0`.
- `Nat.cast_add` : `↑(a + b) = ↑a + ↑b`
- `Nat.cast_mul` : `↑(a * b) = ↑a * ↑b`
- `push_cast` tactic: pushes casts through arithmetic
- `ring` : for rearranging commutative ring expressions

## Recommended proof

The cleanest approach:

```lean
lemma mod_cast_eq_digit (hi lo j : ℕ) :
    (((hi + lo * j * 3) % 5 : ℕ) : ZMod 5) =
      (hi : ZMod 5) + ((lo % 5 : ℕ) : ZMod 5) * (3 : ZMod 5) * (j : ZMod 5) := by
  have hlhs : (((hi + lo * j * 3) % 5 : ℕ) : ZMod 5) = ((hi + lo * j * 3 : ℕ) : ZMod 5) := by
    rw [Nat.cast_mod_cast]  -- or: simp [ZMod.natCast_mod]
  have hrhs : ((lo % 5 : ℕ) : ZMod 5) = ((lo : ℕ) : ZMod 5) := by
    rw [Nat.cast_mod_cast]  -- or: simp [ZMod.natCast_mod]
  rw [hlhs, hrhs]
  push_cast
  ring
```

If `Nat.cast_mod_cast` doesn't exist under that name, try these alternatives:

**Alternative 1** using `ZMod.natCast_zmod_eq_zero_iff_dvd`:
```lean
  -- ((a % n : ℕ) : ZMod n) = (a : ZMod n)
  -- Proof: (a : ZMod n) = (a % n + n * (a / n) : ZMod n) = (a % n : ZMod n) since (n : ZMod n) = 0
  have key : ∀ (a : ℕ), ((a % 5 : ℕ) : ZMod 5) = ((a : ℕ) : ZMod 5) := by
    intro a
    conv_rhs => rw [← Nat.mod_add_div a 5]
    push_cast
    simp [ZMod.natCast_self_eq_zero]
  rw [key, key lo]
  push_cast
  ring
```

**Alternative 2** using `CharP.cast_eq_zero`:
```lean
  -- In ZMod 5, (5 : ZMod 5) = 0, so casting mod 5 is same as casting directly
  have hmod : ∀ (a : ℕ), ((a % 5 : ℕ) : ZMod 5) = (a : ZMod 5) := by
    intro a
    have h5 : (5 : ZMod 5) = 0 := by decide
    rw [show a = a % 5 + 5 * (a / 5) from (Nat.mod_add_div a 5).symm]
    push_cast
    rw [h5]
    ring
  rw [hmod, hmod lo]
  push_cast
  ring
```

**Alternative 3** most direct:
```lean
  simp only [Nat.cast_mod_cast, Nat.cast_add, Nat.cast_mul]
  ring
```

Or even:
```lean
  push_cast
  ring
```

(The `push_cast` tactic is quite powerful and might handle the `% 5` reduction automatically since it knows about `ZMod 5`.)

## The name `Nat.cast_mod_cast`

This lemma might be called different things in different Mathlib versions. Search for:
- `ZMod.natCast_mod`
- `Nat.cast_mod_cast`
- `ZMod.natCast_val`
- Or it might need to be derived from `Nat.mod_add_div` + `ZMod.natCast_self_eq_zero`

If no direct lemma exists, the "Alternative 1" approach (deriving it from `Nat.mod_add_div` and `ZMod.natCast_self_eq_zero`) is the most robust.

## API pitfalls

1. **Types matter**: The LHS must be in `ZMod 5`, not `ℕ`. Make sure both sides have the same type.
2. **`push_cast`** pushes `Nat.cast` through `+`, `*`, etc. It might also handle `%` in `ZMod` context, but this is less certain.
3. **`ring`** works after casts are pushed through.
4. **`decide`** can prove `(5 : ZMod 5) = 0` since it's a concrete computation.
5. **Do NOT use `linarith` or `omega` on `ZMod`** -- these work on `ℕ` and `ℤ` only.
6. **`ZMod.natCast_self_eq_zero`**: `((n : ℕ) : ZMod n) = 0`. This is the key fact that makes `% n` irrelevant when casting to `ZMod n`.

## Constraints
- Must compile with Lean 4.24.0 + specified Mathlib
- Return the complete lemma with proof
