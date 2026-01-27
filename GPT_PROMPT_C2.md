# Lean 4 Task: Prove `product_zmod_eq` (ring computation in ZMod N)

## Environment
- **Lean**: `leanprover/lean4:v4.24.0`
- **Mathlib**: commit `f897ebcf72cd16f89ab4577d0c826cd14afaafc7`

## Task

Show that `u * (m k)^j` equals `lo + b * q` in `ZMod (5^(k+1))`, where `b = (hi + lo * j * 3) % 5`. This is a ring computation that uses nilpotency of `q` and vanishing of `5*q`. Return only the Lean 4 code.

## Definitions

```lean
import Mathlib

namespace Zeroless

def T (k : ℕ) : ℕ := 4 * 5^(k-1)
noncomputable def m (k : ℕ) : ZMod (5^(k+1)) := (2 : ZMod (5^(k+1)))^(T k)
```

## Available axioms (all proved elsewhere in the project)

```lean
axiom s_eq_three (k : ℕ) (hk : k ≥ 1) :
    (m k : ZMod (5^(k+1))) = 1 + 3 * 5^k

axiom m_pow_eq (k : ℕ) (hk : k ≥ 1) (j : ℕ) :
    (m k : ZMod (5^(k+1)))^j = 1 + (j : ZMod (5^(k+1))) * 3 * (5^k : ZMod (5^(k+1)))

axiom five_q_zero (k : ℕ) :
    (5 : ZMod (5^(k+1))) * (5^k : ZMod (5^(k+1))) = 0

axiom q_sq_zero (k : ℕ) (hk : k ≥ 1) :
    (5^k : ZMod (5^(k+1))) * (5^k : ZMod (5^(k+1))) = 0
```

## What to prove

```lean
lemma product_zmod_eq (k : ℕ) (hk : k ≥ 1) (u : ZMod (5^(k+1))) (j : ℕ) :
    let q := 5^k
    let hi := u.val / q
    let lo := u.val % q
    let b := (hi + lo * j * 3) % 5
    u * (m k : ZMod (5^(k+1)))^j =
      (lo : ZMod (5^(k+1))) + (b : ZMod (5^(k+1))) * (q : ZMod (5^(k+1))) := by
  sorry

end Zeroless
```

## Step-by-step proof outline

Let `q = 5^k`, `N = 5^(k+1)`, `hi = u.val / q`, `lo = u.val % q`, `a = hi + lo * j * 3`, `b = a % 5`.

### Step 1: Expand `(m k)^j`
By `m_pow_eq`: `(m k)^j = 1 + (j : ZMod N) * 3 * (q : ZMod N)`.

### Step 2: Multiply by `u`
`u * (m k)^j = u + u * ((j : ZMod N) * 3 * (q : ZMod N))` (by `ring` after rewriting).

### Step 3: Decompose `u`
From `Nat.div_add_mod`: `u.val = q * hi + lo`, so casting to ZMod N:
`u = (lo : ZMod N) + (hi : ZMod N) * (q : ZMod N)`

To cast `u` to its value, use the fact that for any `x : ZMod n`, `(x.val : ZMod n) = x`. The cleanest way:
```lean
have huval : (u.val : ZMod (5^(k+1))) = u := ZMod.natCast_zmod_val u
```
Then rewrite using `u.val = q * hi + lo` (from `Nat.div_add_mod`).

### Step 4: Kill `q^2` terms
Substituting `u = lo + hi*q`:
`u * j * 3 * q = (lo + hi*q) * j * 3 * q = lo*j*3*q + hi*j*3*q*q`

By `q_sq_zero`: `q * q = 0`, so the second term vanishes. Result:
`u * (m k)^j = lo + hi*q + lo*j*3*q = lo + (hi + lo*j*3)*q = lo + a*q`

### Step 5: Reduce coefficient mod 5
`a * q = ((a/5)*5 + b) * q = (a/5)*5*q + b*q`

By `five_q_zero`: `5 * q = 0`, so `(a/5)*5*q = (a/5)*(5*q) = 0`. Result:
`u * (m k)^j = lo + b*q`

### Key Lean tactics for each step

**Step 3** (decompose u):
```lean
have huval : (u.val : ZMod (5^(k+1))) = u := ZMod.natCast_zmod_val u
have hdiv : u.val = q * hi + lo := (Nat.div_add_mod u.val q).symm
-- Then: u = (q * hi + lo : ZMod N) = (lo : ZMod N) + (hi : ZMod N) * (q : ZMod N)
```

**Step 4** (kill q^2):
```lean
have hqq : (q : ZMod (5^(k+1))) * (q : ZMod (5^(k+1))) = 0 := q_sq_zero k hk
-- Use: simp [hqq] or rewrite and use ring
```

**Step 5** (reduce mod 5):
```lean
have h5q : (5 : ZMod (5^(k+1))) * (q : ZMod (5^(k+1))) = 0 := five_q_zero k
have hadecomp : a = (a / 5) * 5 + b := (Nat.div_add_mod a 5).symm
-- Cast to ZMod N, multiply by q, use h5q to kill the (a/5)*5*q term
```

## API pitfalls
1. **`ZMod.natCast_zmod_val`**: `(u.val : ZMod n) = u` — this is the key lemma for expressing `u` in terms of its `.val`.
2. **`Nat.div_add_mod`**: gives `b * (a / b) + a % b = a`. Note the order! Use `.symm` to get `a = b * (a / b) + a % b`.
3. **`Nat.cast_mul`**: `↑(a * b) = ↑a * ↑b` for pushing casts through multiplication.
4. **`Nat.cast_add`**: `↑(a + b) = ↑a + ↑b` for pushing casts through addition.
5. **`ring`**: works for rearranging ZMod expressions (it's a commutative ring).
6. **Do NOT use `linarith` or `omega` on ZMod** — use `ring` or `linear_combination`.

## Constraints
- Must compile with Lean 4.24.0 + specified Mathlib
- Return the complete lemma with proof
