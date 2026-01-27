# Prompt: Close 2 Remaining Sorries in Dyachenko.lean

## Context

You are GPT 5.2 working in Lean 4 + Mathlib (January 2026). The file `Dyachenko_aristotle.lean` formalizes Dyachenko's Type III existence theorem for the Erdős-Straus Conjecture. Aristotle (automated prover) got most of it, but **2 sorries remain**.

## The File Structure

```lean
namespace Dyachenko

-- g(P, α) = gcd(P, α² + 1)
def g (P : ℕ) (α : ℤ) : ℕ := Nat.gcd P (Int.natAbs (α^2 + 1))

-- The lattice L(P, α) = { (u,v) ∈ ℤ² : g(P,α) | αu + v }
def Lattice (P : ℕ) (α : ℤ) : AddSubgroup (ℤ × ℤ) where ...

-- type3_x p offset = (p + offset) / 4
def type3_x (p : ℕ) (offset : ℕ) : ℕ := (p + offset) / 4
```

## Sorry 1: `decode_lattice_point_to_type3` (Line 419)

```lean
lemma decode_lattice_point_to_type3 (p : ℕ) (hp : Nat.Prime p)
    (hp_mod : p % 4 = 1) (hp_ge : p ≥ 5)
    (u v : ℤ) (hu_pos : 1 ≤ u) (hv_pos : 1 ≤ v)
    (hu_bound : u ≤ 1 + (p + 3) / 4) (hv_bound : v ≤ 1 + (p + 3) / 4) :
    ∃ offset c : ℕ,
      offset % 4 = 3 ∧
      c > 0 ∧
      (4 * c - 1) * offset > p ∧
      ((4 * c - 1) * offset - p) ∣ (4 * type3_x p offset * c * p) := by
  -- The decoding follows Dyachenko's ED2 construction:
  -- b = 4u - 1, c = 4v - 1
  -- δ = ((4u-1)(4v-1) - 1) / (4p)
  -- A = bc/δ
  -- offset = 4A - p
  -- The divisibility condition follows from ED2_identity.
  sorry
```

### What this lemma needs to do:

Given integers u, v with 1 ≤ u, v ≤ 1 + (p+3)/4, construct:
- `offset : ℕ` with `offset % 4 = 3`
- `c : ℕ` with `c > 0`
- Such that `(4*c - 1) * offset > p`
- And the divisibility condition holds

### Dyachenko's ED2 Construction (from the paper):

For u, v ≥ 1:
1. Let b = 4u - 1, c = 4v - 1 (both ≡ 3 mod 4)
2. δ = (bc - 1) / (4p) (this is an integer when (u,v) ∈ L(p,α))
3. A = b·c / δ
4. offset = 4A - p

The key identity: when these are derived from a lattice point, the divisibility condition is automatically satisfied.

### Suggested Approach:

**Option A (Direct construction):**
```lean
-- Use explicit witnesses
use (4 * u.toNat - 1 - p)  -- or similar formula for offset
use (4 * v.toNat - 1)      -- c = 4v - 1
-- Then prove the four conditions
```

**Option B (Existential from bounds):**
Since u, v are bounded and positive, the construction is guaranteed to produce valid parameters. Use the bounds to establish each condition.

**Option C (Classical + choice):**
```lean
classical
-- Use nonconstructive existence from the paper's argument
```

---

## Sorry 2: `boxSize ≥ d` (Line 457)

```lean
-- In dyachenko_type3_existence:
let d := g p α
let boxSize := (p + 3) / 4

have hbox_ge : boxSize ≥ d := by
  -- This requires showing g(p,α) ≤ (p+3)/4
  -- Since g(p,α) | p and p is prime, g(p,α) ∈ {1, p}
  -- If g(p,α) = p, we need p ≤ (p+3)/4, false for p ≥ 5
  -- So we need g(p,α) = 1 or careful case analysis
  sorry
```

### What this needs:

Prove `(p + 3) / 4 ≥ g p α` where:
- `g p α = Nat.gcd p (Int.natAbs (α^2 + 1))`
- `p` is prime with `p % 4 = 1` and `p ≥ 5`

### Key Insight:

Since `g p α` divides `p` (by definition of gcd) and `p` is prime:
- `g p α ∈ {1, p}`

**Case g p α = 1:**
- Need `(p + 3) / 4 ≥ 1`, true for all p ≥ 1

**Case g p α = p:**
- Need `(p + 3) / 4 ≥ p`
- This means `p + 3 ≥ 4p`, i.e., `3 ≥ 3p`, i.e., `p ≤ 1`
- But `p ≥ 5`, contradiction!
- So this case is impossible

### Suggested Proof:

```lean
have hbox_ge : boxSize ≥ d := by
  unfold_let d boxSize
  -- g p α divides p
  have hdvd : g p α ∣ p := Nat.gcd_dvd_left p _
  -- Since p is prime, g p α ∈ {1, p}
  cases Nat.eq_one_or_self_of_prime_of_dvd hp (g p α) hdvd with
  | inl h1 =>
    -- g p α = 1
    simp [h1]
    -- (p + 3) / 4 ≥ 1 for p ≥ 5
    omega
  | inr hp_eq =>
    -- g p α = p, derive contradiction
    exfalso
    -- If g p α = p, then p | α² + 1
    -- But we chose α such that this leads to a unit, contradiction
    -- Actually simpler: (p+3)/4 < p for p ≥ 5
    have : (p + 3) / 4 < p := by omega
    -- But we'd need (p+3)/4 ≥ p, contradiction
    sorry -- may need more context about α
```

**Alternative (if α choice guarantees g = 1):**

The lemma `exists_alpha_unit` chooses α such that `α + 1` is a unit in `ZMod (g p α)`. This might force `g p α = 1`. Check if there's a lemma establishing this.

---

## Task

Provide Lean code to fill both sorries. For each:

1. Show the complete proof (no `sorry`)
2. Use only definitions/lemmas already in the file or Mathlib
3. Keep proofs robust (prefer `omega`, `decide`, `simp` over fragile chains)

## Output Format

```lean
-- Sorry 1: decode_lattice_point_to_type3
lemma decode_lattice_point_to_type3 (p : ℕ) (hp : Nat.Prime p)
    (hp_mod : p % 4 = 1) (hp_ge : p ≥ 5)
    (u v : ℤ) (hu_pos : 1 ≤ u) (hv_pos : 1 ≤ v)
    (hu_bound : u ≤ 1 + (p + 3) / 4) (hv_bound : v ≤ 1 + (p + 3) / 4) :
    ∃ offset c : ℕ,
      offset % 4 = 3 ∧
      c > 0 ∧
      (4 * c - 1) * offset > p ∧
      ((4 * c - 1) * offset - p) ∣ (4 * type3_x p offset * c * p) := by
  [YOUR PROOF]

-- Sorry 2: hbox_ge in dyachenko_type3_existence
have hbox_ge : boxSize ≥ d := by
  [YOUR PROOF]
```

## Verification

After filling, the entire file should compile with `lake env lean Dyachenko_aristotle.lean`.
