# Lean 4 Task: Prove `top_digit_product` (the val computation)

## Environment
- **Lean**: `leanprover/lean4:v4.24.0`
- **Mathlib**: commit `f897ebcf72cd16f89ab4577d0c826cd14afaafc7`

## Task

Prove the key lemma that computes the top digit of `u * (m k)^j` in terms of natural number arithmetic. This is the hardest lemma in the proof. Return only the Lean 4 code.

## Definitions (from the project)

```lean
import Mathlib

namespace Zeroless

def T (k : ℕ) : ℕ := 4 * 5^(k-1)

noncomputable def m (k : ℕ) : ZMod (5^(k+1)) :=
  (2 : ZMod (5^(k+1)))^(T k)

def top_digit (k : ℕ) (u : ZMod (5^(k+1))) : Fin 5 :=
  ⟨u.val / 5^k, by
    have hu : u.val < 5^k * 5 := by
      simpa [pow_succ] using (u.val_lt : u.val < (5 : ℕ)^(k+1))
    exact Nat.div_lt_of_lt_mul hu⟩

def survives (k : ℕ) (u : ZMod (5^(k+1))) : Prop :=
  (top_digit k u).val ≠ 0
```

## Available proved lemmas (use as axioms)

```lean
axiom s_eq_three (k : ℕ) (hk : k ≥ 1) :
    (m k : ZMod (5^(k+1))) = 1 + 3 * 5^k

-- From Lemma B:
axiom m_pow_eq (k : ℕ) (hk : k ≥ 1) (j : ℕ) :
    (m k : ZMod (5^(k+1)))^j = 1 + (j : ZMod (5^(k+1))) * 3 * (5^k : ZMod (5^(k+1)))
```

## What to prove

The goal is the `hdigit_iff` sorry: for `j : Fin 5`, show that

```
survives k (u * (m k)^j.val)  ↔  digit j ≠ 0
```

where `digit j = (hi : ZMod 5) + ((lo % 5 : ℕ) : ZMod 5) * 3 * (j.val : ZMod 5)` and `hi = u.val / 5^k`, `lo = u.val % 5^k`.

Here is the full context within the theorem:

```lean
open Classical in
theorem four_or_five_children (k : ℕ) (hk : k ≥ 1) (u : ZMod (5^(k+1)))
    (hu : survives k u) :
    ... := by
  classical
  let q : ℕ := 5^k
  let N : ℕ := 5^(k+1)
  let hi : ℕ := u.val / q
  let lo : ℕ := u.val % q
  -- (hhi_lt5 : hi < 5) and (hhi_ne0 : hi ≠ 0) are available
  let digit : Fin 5 → ZMod 5 :=
    fun j => (hi : ZMod 5) + ((lo % 5 : ℕ) : ZMod 5) * (3 : ZMod 5) * (j.val : ZMod 5)
  let P : Fin 5 → Prop := fun j => survives k (u * (m k)^j.val)

  have hdigit_iff (j : Fin 5) : P j ↔ digit j ≠ 0 := by
    sorry  -- THIS IS WHAT YOU FILL IN
```

## Step-by-step mathematical proof

Let `q = 5^k`, `N = 5^(k+1) = 5q`, `hi = u.val / q`, `lo = u.val % q`.

**Step 1**: By `m_pow_eq`, `(m k)^j = 1 + j*3*q` in `ZMod N`.

**Step 2**: So `u * (m k)^j = u * (1 + j*3*q) = u + u*j*3*q` in `ZMod N`.

**Step 3**: We need to compute `(u + u*j*3*q).val / q`. This is the top digit.

Since `u.val = lo + hi*q` (by `Nat.div_add_mod`):
- `u * j * 3 * q` as a natural number involves `(lo + hi*q) * j * 3 * q`
- `= lo*j*3*q + hi*j*3*q^2`
- The `q^2` term vanishes mod N (since `q^2 = 5^(2k)` and `N = 5^(k+1)` divides `5^(2k)` when `k ≥ 1`)
- So `u * (m k)^j ≡ lo + hi*q + lo*j*3*q (mod N)`
- `= lo + (hi + lo*j*3)*q (mod N)`

**Step 4**: Define `b = (hi + lo * j.val * 3) % 5`. Then:
- `u * (m k)^j` has value `(lo + b*q) % N` in `ZMod N` (since `lo < q` and `b < 5`, we have `lo + b*q < 5q = N`)
- So `.val / q = b`

**Step 5**: `b ≠ 0 ↔ (b : ZMod 5) ≠ 0` (since `b < 5`).

**Step 6**: `(b : ZMod 5) = digit j` because:
- `b = (hi + lo * j.val * 3) % 5`
- In `ZMod 5`: `(b : ZMod 5) = (hi : ZMod 5) + (lo : ZMod 5) * 3 * (j.val : ZMod 5)`
- And `(lo : ZMod 5) = ((lo % 5 : ℕ) : ZMod 5)` since `Nat.cast` to `ZMod 5` reduces mod 5.

## CRITICAL: Recommended proof structure

Rather than computing `.val` of the product directly (which is extremely fiddly), work in `ZMod N` as long as possible:

```lean
  have hdigit_iff (j : Fin 5) : P j ↔ digit j ≠ 0 := by
    -- Step 1: Unfold P to a statement about top_digit
    -- P j ↔ (top_digit k (u * (m k)^j.val)).val ≠ 0
    -- ↔ (u * (m k)^j.val).val / q ≠ 0
    unfold_let P
    simp only [survives, top_digit]

    -- Step 2: Compute u * (m k)^j in ZMod N
    -- Use m_pow_eq to get (m k)^j = 1 + j*3*q
    have hmpow := m_pow_eq k hk j.val
    -- So u * (m k)^j = u + u * (j*3*q)

    -- Step 3: Show u = (lo : ZMod N) + (hi : ZMod N) * (q : ZMod N)
    have hudecomp : (u : ZMod (5^(k+1))) =
        (lo : ZMod (5^(k+1))) + (hi : ZMod (5^(k+1))) * (q : ZMod (5^(k+1))) := by
      -- From u.val = lo + hi * q (Nat.div_add_mod)
      ...

    -- Step 4: Define b and show the product has value lo + b*q
    let b : ℕ := (hi + lo * j.val * 3) % 5
    -- Show: (u * (m k)^j.val).val = lo + b * q
    ...

    -- Step 5: Therefore .val / q = b
    -- Use: (lo + b*q) / q = b  (since lo < q)
    ...

    -- Step 6: b ≠ 0 ↔ digit j ≠ 0
    ...
```

## KEY ALTERNATIVE: The "suffices" approach

You might find it cleaner to reduce the whole thing to a single `suffices`:

```lean
  have hdigit_iff (j : Fin 5) : P j ↔ digit j ≠ 0 := by
    -- Reduce to: (u * (m k)^j.val).val / q ≠ 0 ↔ digit j ≠ 0
    -- Which is: b ≠ 0 ↔ digit j ≠ 0 (where b = top digit as Nat)
    -- Which is: (b : ZMod 5) ≠ 0 ↔ digit j ≠ 0 (since b < 5)
    -- Which is: digit j ≠ 0 ↔ digit j ≠ 0  (by showing (b : ZMod 5) = digit j)
    suffices h : ((u * (m k)^j.val).val / q : ZMod 5) = digit j by
      simp only [P, survives, top_digit]
      constructor
      · intro hne
        rwa [← h]
        -- need: (top_digit value : ZMod 5) ≠ 0 from top_digit value ≠ 0
        ...
      · ...
```

## API pitfalls to AVOID

1. **`Nat.div_add_mod` gives `b * (a / b) + a % b = a`** (note the order!). Use `Nat.div_add_mod'` for `a = b * (a / b) + a % b`. Or rearrange manually.

2. **`ZMod.val_natCast`**: `((n : ℕ) : ZMod m).val = n % m`. Essential for going between ℕ and ZMod.

3. **`ZMod.natCast_zmod_eq_zero_iff_dvd`**: `((x : ℕ) : ZMod n) = 0 ↔ n ∣ x`.

4. **`linarith`/`omega` do NOT work on ZMod**. Use `ring`, `linear_combination`, or explicit rewrites.

5. **To show `u = (u.val : ZMod N)`**: Use `ZMod.natCast_zmod_eq_iff_dvd` or the fact that casting `u.val` back gives `u` (this is `ZMod.natCast_val` or similar).

6. **To show `(lo + b*q) < N`**: Use `lo < q` (from `Nat.mod_lt`) and `b < 5` (from `Nat.mod_lt`), so `lo + b*q < q + 4*q = 5*q = N`. Use `omega` or `calc`.

7. **To show `(x : ZMod N).val = x` when `x < N`**: Use `ZMod.val_natCast` which gives `.val = x % N`, then `Nat.mod_eq_of_lt`.

8. **`(5 : ℕ)^k * 5 = 5^(k+1)`**: Use `pow_succ` or `pow_succ'`. Be careful: in recent Mathlib, `pow_succ` might give `a^(n+1) = a^n * a` or `a * a^n` depending on the version.

9. **Showing `q^2` vanishes in `ZMod N`**: `(q : ZMod N)^2 = ((5^k)^2 : ZMod N) = (5^(2k) : ZMod N) = 0` because `N = 5^(k+1)` divides `5^(2k)` when `k ≥ 1`.

10. **For the decomposition `u = lo + hi * q`**: The cleanest approach might be:
    ```lean
    have : u.val = q * hi + lo := (Nat.div_add_mod u.val q).symm
    have : (u.val : ZMod N) = u := ZMod.natCast_zmod_eq_zero_iff_dvd ... -- or use val/cast roundtrip
    ```

## Constraints
- Must compile with Lean 4.24.0 + the specified Mathlib commit
- Return the complete proof of `hdigit_iff` (replacing the sorry), plus any auxiliary lemmas needed above the theorem
- All the `let` bindings (`q`, `N`, `hi`, `lo`, `digit`, `P`) and `have` hypotheses (`hhi_lt5`, `hhi_ne0`, `hk`, `hu`) are in scope
- `m_pow_eq` and `s_eq_three` are available

end Zeroless
