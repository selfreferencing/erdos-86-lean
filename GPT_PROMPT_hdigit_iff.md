# Focused Lean 4 Task: Prove `hdigit_iff` in `four_or_five_children`

## Environment
- **Lean**: `leanprover/lean4:v4.24.0`
- **Mathlib**: commit `f897ebcf72cd16f89ab4577d0c826cd14afaafc7`
- **File**: `Zeroless/FiveAdic_Extended.lean`

## What to produce

Replace the single `sorry` at line 136 with a complete proof. The sorry is inside the theorem `four_or_five_children`. Everything else in the file compiles. You must return **only** the replacement proof term for the sorry (the body of `hdigit_iff`), plus any auxiliary lemmas you need inserted above the theorem.

## The sorry in context

Here is the theorem header and the sorry:

```lean
open Classical in
theorem four_or_five_children (k : ℕ) (hk : k ≥ 1) (u : ZMod (5^(k+1)))
    (hu : survives k u) :
    (Finset.filter (fun j : Fin 5 => survives k (u * (m k)^j.val)) Finset.univ).card ∈ ({4, 5} : Set ℕ) := by
  classical

  let q : ℕ := 5^k
  let N : ℕ := 5^(k+1)
  let hi : ℕ := u.val / q
  let lo : ℕ := u.val % q

  have hhi_lt5 : hi < 5 := by
    simpa [top_digit, q, hi] using (top_digit k u).isLt

  have hhi_ne0 : hi ≠ 0 := by
    simpa [survives, top_digit, q, hi] using hu

  let digit : Fin 5 → ZMod 5 :=
    fun j => (hi : ZMod 5) + ((lo % 5 : ℕ) : ZMod 5) * (3 : ZMod 5) * (j.val : ZMod 5)

  let P : Fin 5 → Prop := fun j => survives k (u * (m k)^j.val)

  -- *** THIS IS THE SORRY TO FILL ***
  have hdigit_iff (j : Fin 5) : P j ↔ digit j ≠ 0 := by
    sorry
```

## Definitions you need

All definitions are in the same file:

```lean
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

## Available proved theorem

```lean
theorem s_eq_three (k : ℕ) (hk : k ≥ 1) :
    (m k : ZMod (5^(k+1))) = 1 + 3 * 5^k
```

This is fully proved in the file (by Aristotle, via induction on k with binomial expansion).

## Mathematical content of `hdigit_iff`

We need:
```
survives k (u * (m k)^j) ↔ (hi : ZMod 5) + ((lo % 5 : ℕ) : ZMod 5) * 3 * (j : ZMod 5) ≠ 0
```

**Step-by-step math:**

1. **Power of m**: By `s_eq_three`, `m k = 1 + 3 * 5^k` in `ZMod (5^(k+1))`.

2. **Nilpotency of `3 * 5^k`**: In `ZMod (5^(k+1))`, we have `(3 * 5^k)^2 = 9 * 5^(2k)`. Since `k ≥ 1` implies `2k ≥ k+1`, we get `5^(k+1) | 9 * 5^(2k)`, so `(3 * 5^k)^2 = 0`.

3. **Binomial expansion**: Since the square is zero, `(1 + 3*5^k)^j = 1 + j * 3 * 5^k`. This uses the helper lemma `one_add_pow_of_sq_zero` (defined in `FiveAdic.lean` but **not imported** in this file). You may need to inline this or provide it as an auxiliary lemma.

4. **Product**: `u * (m k)^j = u * (1 + j*3*5^k) = u + u * j * 3 * 5^k`.

5. **Value computation**: Let `q = 5^k`, `N = 5*q = 5^(k+1)`.
   - `u.val = lo + hi * q` where `lo = u.val % q`, `hi = u.val / q`, `lo < q`, `hi < 5`.
   - `u * j * 3 * q` has value `(lo + hi*q) * j * 3 * q mod N`.
   - `hi * q * j * 3 * q = hi * j * 3 * q^2 = hi * j * 3 * 5^(2k)`. Since `5^(k+1) | 5^(2k)` (because `2k ≥ k+1`), this term vanishes mod N.
   - So `u * (m k)^j ≡ lo + hi*q + lo*j*3*q (mod N)`.
   - `= lo + (hi + lo*j*3)*q (mod N)`.

6. **Top digit extraction**: Dividing `(lo + (hi + lo*j*3)*q) mod N` by `q`:
   - Since `lo < q`, this equals `(hi + lo*j*3) mod 5` (the quotient after dividing by q in a number < 5q).
   - So `top_digit k (u * (m k)^j) = (hi + lo*j*3) mod 5`.

7. **Connection to ZMod 5**: `(hi + lo*j*3) mod 5 ≠ 0` is equivalent to `(hi : ZMod 5) + (lo : ZMod 5) * 3 * (j : ZMod 5) ≠ 0`. And `(lo : ZMod 5) = ((lo % 5 : ℕ) : ZMod 5)` since casting to ZMod reduces mod 5.

## Proof strategy for Lean

The proof involves `.val` computations on `ZMod` which are notoriously fiddly. Here is a recommended approach:

### Approach A: Work entirely in ZMod, reduce to Nat at the end

1. Show `(3 * (5^k : ZMod (5^(k+1))))^2 = 0`:
   ```lean
   have hsq : (3 * (5^k : ZMod (5^(k+1)))) ^ 2 = 0 := by
     rw [show (2 : ℕ) = 2 from rfl]  -- or just simplify
     simp only [mul_pow, pow_two]
     -- 9 * 5^(2k) is divisible by 5^(k+1) when k ≥ 1
     -- Use ZMod.natCast_zmod_eq_zero_iff_dvd or similar
   ```

2. Derive `(m k)^j.val = 1 + j.val * 3 * 5^k` using binomial-with-nilpotent:
   ```lean
   have hmpow : (m k : ZMod (5^(k+1)))^j.val = 1 + (j.val : ZMod (5^(k+1))) * (3 * 5^k) := by
     rw [s_eq_three k hk]
     -- apply one_add_pow_of_sq_zero or prove inline
   ```

3. Compute `(u * (m k)^j).val / 5^k` using Nat arithmetic:
   - Show `(u * (m k)^j).val = (lo + (hi + lo * j.val * 3) * q) % N`
   - Then `(... % N) / q = (hi + lo * j.val * 3) % 5`

4. Connect `(hi + lo * j.val * 3) % 5 ≠ 0` to `digit j ≠ 0` in ZMod 5.

### Approach B: Direct `.val` computation (more mechanical)

Work at the Nat level throughout:
1. Use `ZMod.val_mul`, `ZMod.val_add`, `ZMod.val_one`, `ZMod.val_natCast`
2. Careful: `ZMod.val_mul` gives `(a * b).val = (a.val * b.val) % n` only for `ZMod n`
3. Careful: `ZMod.val_add` gives `(a + b).val = (a.val + b.val) % n`

### Approach C: Sufficiency proof (simplest)

Instead of computing `.val` directly, show the equivalence through ZMod cast:
1. The key observation: `survives k x ↔ ¬((5^k : ℕ) ∣ x.val)` ... no, that's not quite right. `survives k x ↔ x.val / 5^k ≠ 0 ↔ x.val ≥ 5^k` ... no, that's not right either since hi could be 0 even for large values.

Actually, `survives k x = ((x.val / 5^k) ≠ 0)`, which is `¬(x.val / 5^k = 0)`, which is `¬(x.val < 5^k)` ... no, `a / b = 0 ↔ a < b` for `b > 0`, so `survives k x ↔ ¬(x.val < 5^k) ↔ x.val ≥ 5^k`. Hmm, but that loses information about which digit it is.

The cleanest approach is probably:
1. Show the `.val` of `u * (m k)^j` equals `(lo + (hi + lo * j * 3) % 5 * q) % N` (or similar normalized form)
2. Then `.val / q` equals `(hi + lo * j * 3) % 5`
3. Connect to ZMod 5

## CRITICAL: Mathlib API pitfalls to AVOID

These caused 30+ errors in the previous attempt:

1. **`Nat.mod_add_div` vs `Nat.div_add_mod`**: The identity `a = a % b + b * (a / b)` is `Nat.mod_add_div`. The swapped version `a = b * (a / b) + a % b` is `Nat.div_add_mod'`. Do NOT confuse them.

2. **`ZMod.val_eq_zero` does NOT exist as `.mp`**: Use `ZMod.natCast_zmod_eq_zero_iff_dvd` instead. The pattern:
   ```lean
   have : 5 ∣ x := (ZMod.natCast_zmod_eq_zero_iff_dvd x 5).mp h
   ```

3. **`linarith` does NOT work on `ZMod`**: Use `linear_combination` or `ring` instead for ZMod equalities. `omega` also doesn't work on ZMod.

4. **`field_simp` often fails on `ZMod`**: Use explicit `mul_inv_cancel₀`/`inv_mul_cancel₀` instead.

5. **`ZMod.val_mul` gives `(a * b).val = (a.val * b.val) % n`**: This is the correct form. Don't assume `.val` distributes over `*` without the mod.

6. **`ZMod.val_add` gives `(a + b).val = (a.val + b.val) % n`**: Same caveat.

7. **`ZMod.val_natCast` gives `(n : ZMod m).val = n % m`**: This is essential for going between ℕ and ZMod.

8. **For `(3 : ZMod 5) ≠ 0`**: The proof that worked:
   ```lean
   intro h
   have : 5 ∣ (3 : ℕ) := by
     have := (ZMod.natCast_zmod_eq_zero_iff_dvd 3 5).mp
     exact this (by exact_mod_cast h)
   omega
   ```
   Simple `decide`/`native_decide`/`norm_num` all FAIL for this goal when inside a proof with free variables.

9. **`Nat.div_add_mod' (u.val) (5^k)`** gives `u.val = 5^k * (u.val / 5^k) + u.val % 5^k`.

10. **Casting naturals to `ZMod n`**: Use `(x : ZMod n)` or `(x : ℕ) : ZMod n`. The cast `↑x` means `Nat.cast x`.

## Auxiliary lemma you may want to add

If you need `one_add_pow_of_sq_zero`, add it above the theorem:

```lean
/-- If a^2 = 0 in a commutative semiring, then (1+a)^n = 1 + n*a -/
private lemma one_add_pow_of_sq_zero' {R : Type*} [CommSemiring R] (a : R) (ha : a^2 = 0) :
    ∀ n : ℕ, (1 + a)^n = 1 + (n : R) * a := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    have haa : a * a = 0 := by simpa [pow_two] using ha
    calc (1 + a) ^ (n + 1)
        = (1 + a)^n * (1 + a) := pow_succ (1 + a) n
      _ = (1 + (n : R) * a) * (1 + a) := by rw [ih]
      _ = 1 + (↑n * a + a) + ↑n * a * a := by ring
      _ = 1 + (↑n * a + a) := by rw [haa, mul_zero, add_zero]
      _ = 1 + (↑(n + 1) : R) * a := by push_cast; ring
```

This lemma compiles in current Mathlib (tested).

## The full file (for reference)

```lean
/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: f685d570-f951-49ad-afbc-64fef25230e5

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem s_eq_three (k : ℕ) (hk : k ≥ 1) :
    (m k : ZMod (5^(k+1))) = 1 + 3 * 5^k
-/

/-
  Zeroless/FiveAdic_Extended.lean
  Extended 5-adic Infrastructure with full four_or_five_children proof

  This file contains the complete proof of the "4-or-5 Children Theorem"
  which is the key combinatorial result for the survivor dynamics.
-/

import Mathlib

namespace Zeroless

open scoped BigOperators

/-! ## Basic Definitions (duplicated from FiveAdic.lean for standalone verification) -/

/-- Period for k trailing zeroless digits: T_k = 4 · 5^(k-1) -/
def T (k : ℕ) : ℕ := 4 * 5^(k-1)

/-- The 5-adic state: u_{k+1}(n) = 2^{n-k-1} mod 5^{k+1} -/
noncomputable def u (k : ℕ) (n : ℕ) : ZMod (5^(k+1)) :=
  (2 : ZMod (5^(k+1)))^(n-k-1)

/-- The multiplier: m_k = 2^{T_k} mod 5^{k+1} -/
noncomputable def m (k : ℕ) : ZMod (5^(k+1)) :=
  (2 : ZMod (5^(k+1)))^(T k)

/-- The top digit of u: the coefficient of 5^k in the 5-adic expansion -/
def top_digit (k : ℕ) (u : ZMod (5^(k+1))) : Fin 5 :=
  ⟨u.val / 5^k, by
    have hu : u.val < 5^k * 5 := by
      simpa [pow_succ] using (u.val_lt : u.val < (5 : ℕ)^(k+1))
    exact Nat.div_lt_of_lt_mul hu⟩

/-- A state u survives at level k if its top digit is nonzero -/
def survives (k : ℕ) (u : ZMod (5^(k+1))) : Prop :=
  (top_digit k u).val ≠ 0

/-- Specifically: s_k = 3 for all k (the expansion coefficient is constant) -/
theorem s_eq_three (k : ℕ) (hk : k ≥ 1) :
    (m k : ZMod (5^(k+1))) = 1 + 3 * 5^k := by
  -- [Aristotle's proof, ~30 lines, compiles clean]
  -- ... (omitted for brevity, it's in the file)
  sorry -- placeholder in this prompt; full proof is in the actual file

/-! ## The 4-or-5 Children Theorem (Full Proof) -/

open Classical in
theorem four_or_five_children (k : ℕ) (hk : k ≥ 1) (u : ZMod (5^(k+1)))
    (hu : survives k u) :
    (Finset.filter (fun j : Fin 5 => survives k (u * (m k)^j.val)) Finset.univ).card ∈ ({4, 5} : Set ℕ) := by
  classical

  let q : ℕ := 5^k
  let N : ℕ := 5^(k+1)
  let hi : ℕ := u.val / q
  let lo : ℕ := u.val % q

  have hhi_lt5 : hi < 5 := by
    simpa [top_digit, q, hi] using (top_digit k u).isLt

  have hhi_ne0 : hi ≠ 0 := by
    simpa [survives, top_digit, q, hi] using hu

  let digit : Fin 5 → ZMod 5 :=
    fun j => (hi : ZMod 5) + ((lo % 5 : ℕ) : ZMod 5) * (3 : ZMod 5) * (j.val : ZMod 5)

  let P : Fin 5 → Prop := fun j => survives k (u * (m k)^j.val)

  -- *** THIS IS THE SORRY TO FILL: ***
  have hdigit_iff (j : Fin 5) : P j ↔ digit j ≠ 0 := by
    sorry

  -- Everything below this point COMPILES CLEAN.
  -- (case split on lo%5 = 0 vs ≠ 0, counting argument, etc.)
```

## What to return

Return the complete proof of `hdigit_iff`, along with any auxiliary lemmas that should be inserted above `four_or_five_children`. Format as a Lean 4 code block.

**Important constraints:**
- Must compile with Lean 4.24.0 + the specified Mathlib commit
- Must use `classical` (already in scope from the enclosing `by classical`)
- The proof will be inserted at line 136 replacing `sorry`
- All the `let` bindings (`q`, `N`, `hi`, `lo`, `digit`, `P`) and `have` hypotheses (`hhi_lt5`, `hhi_ne0`, `hk`, `hu`) are in scope
- `s_eq_three k hk : (m k : ZMod (5^(k+1))) = 1 + 3 * 5^k` is available

## Hint on proof structure

A clean proof might look like:

```lean
have hdigit_iff (j : Fin 5) : P j ↔ digit j ≠ 0 := by
  -- Step 1: (3 * 5^k)^2 = 0 in ZMod (5^(k+1))
  have hsq_zero : ((3 : ZMod (5^(k+1))) * (5^k : ZMod (5^(k+1))))^2 = 0 := by
    ...

  -- Step 2: (m k)^j = 1 + j * 3 * 5^k
  have hmpow : (m k : ZMod (5^(k+1)))^j.val = 1 + (j.val : ZMod (5^(k+1))) * (3 * (5^k : ZMod (5^(k+1)))) := by
    rw [s_eq_three k hk]
    exact one_add_pow_of_sq_zero' _ hsq_zero j.val

  -- Step 3: u * (m k)^j = u + u * j * 3 * 5^k
  have hprod : u * (m k : ZMod (5^(k+1)))^j.val =
      u + u * ((j.val : ZMod (5^(k+1))) * (3 * 5^k)) := by
    rw [hmpow]; ring

  -- Step 4: Compute (u * (m k)^j).val / 5^k
  -- This is the hard Nat arithmetic part.
  -- Show it equals (hi + lo * j.val * 3) % 5
  ...

  -- Step 5: Connect (hi + lo * j.val * 3) % 5 ≠ 0 to digit j ≠ 0 in ZMod 5
  ...
```

The hardest part is Step 4: computing `.val` of a `ZMod` expression and extracting the top digit. You need:
- `ZMod.val_add` : `(a + b).val = (a.val + b.val) % n`
- `ZMod.val_mul` : `(a * b).val = (a.val * b.val) % n`
- `ZMod.val_one` : `(1 : ZMod n).val = 1` (when `n > 1`)
- `ZMod.val_natCast` : `(↑x : ZMod n).val = x % n`
- `Nat.div_add_mod'` : `a = b * (a / b) + a % b`

For Step 4, you may want to avoid computing `.val` of the full expression directly. Instead, consider:
- Working with the decomposition `u.val = lo + hi * q`
- Showing `(u + u * (j * 3 * q)).val = (lo + (hi + lo * j * 3) % 5 * q)` using modular arithmetic
- Then showing `(lo + c * q) / q = c` when `lo < q` and `c < 5`

Alternatively, you could cast everything to `ZMod 5` using the natural ring map `ZMod (5^(k+1)) → ZMod 5` and show the top digit computation factors through this map.
