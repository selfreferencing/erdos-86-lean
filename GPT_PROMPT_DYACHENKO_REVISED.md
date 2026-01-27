# Revised Prompt: Close Dyachenko Sorries (With Structural Fix)

## Critical Discovery

Previous attempts revealed that `decode_lattice_point_to_type3` is **misstated**. The lemma takes arbitrary bounded integers u, v, but Dyachenko's ED2 construction only works when (u,v) is a **lattice point** in L(p,α).

Without lattice membership, the divisibility condition cannot be proved because δ = (bc-1)/(4p) is not guaranteed to be an integer.

## The Fix

**Option A (Recommended):** Remove the problematic lemma and inline the construction in `dyachenko_type3_existence`, using the lattice point directly from `rectangle_hits_diagonal_lattice`.

**Option B:** Add lattice membership as a hypothesis to `decode_lattice_point_to_type3`.

---

## Context

File: `Dyachenko_aristotle.lean`
- Formalizes Dyachenko's Type III existence theorem
- 2 sorries remain
- Aristotle proved most infrastructure

Key definitions:
```lean
def g (P : ℕ) (α : ℤ) : ℕ := Nat.gcd P (Int.natAbs (α^2 + 1))

def Lattice (P : ℕ) (α : ℤ) : AddSubgroup (ℤ × ℤ) where
  carrier := { v | (g P α : ℤ) ∣ linForm α v }
  -- linForm α v = α * v.1 + v.2

def type3_x (p : ℕ) (offset : ℕ) : ℕ := (p + offset) / 4
```

---

## Sorry 1: The Decode Lemma (NEEDS RESTRUCTURING)

### Current (Broken) Statement:
```lean
lemma decode_lattice_point_to_type3 (p : ℕ) (hp : Nat.Prime p)
    (hp_mod : p % 4 = 1) (hp_ge : p ≥ 5)
    (u v : ℤ) (hu_pos : 1 ≤ u) (hv_pos : 1 ≤ v)
    (hu_bound : u ≤ 1 + (p + 3) / 4) (hv_bound : v ≤ 1 + (p + 3) / 4) :
    ∃ offset c : ℕ, ...
```

**Problem:** No lattice membership. The ED2 construction requires (u,v) ∈ L(p,α).

### Recommended Fix: Delete this lemma and inline in main theorem

The main theorem `dyachenko_type3_existence` already obtains a lattice point:

```lean
obtain ⟨pt, hptL, hx0, hx1, hy0, hy1⟩ :=
  rectangle_hits_diagonal_lattice (Lattice p α) d hcyc ...
```

Here `hptL` is the proof that `pt ∈ Lattice p α`. Use this directly.

### The ED2 Construction (for reference)

Given (u, v) ∈ L(p,α) with 1 ≤ u, v ≤ (p+3)/4:

1. b := 4u - 1, c := 4v - 1 (both ≡ 3 mod 4)
2. Since (u,v) ∈ L(p,α), we have g | αu + v
3. δ := (bc - 1) / (4p) is an integer (this is the key step requiring lattice membership)
4. A := b·c / δ
5. offset := 4A - p (satisfies offset ≡ 3 mod 4)
6. The divisibility condition follows from the ED2 identity

### Suggested Replacement

Delete `decode_lattice_point_to_type3` and replace the final line of `dyachenko_type3_existence` with direct construction:

```lean
theorem dyachenko_type3_existence (p : ℕ) (hp : Nat.Prime p)
    (hp_mod : p % 4 = 1) (hp_ge : p ≥ 5) :
    ∃ offset c : ℕ,
      offset % 4 = 3 ∧
      c > 0 ∧
      (4 * c - 1) * offset > p ∧
      ((4 * c - 1) * offset - p) ∣ (4 * type3_x p offset * c * p) := by
  classical

  -- Steps 1-4 remain the same (obtain α, build Fintype, get cyclic structure)
  obtain ⟨α, hunit⟩ := exists_alpha_unit p hp hp_mod hp_ge
  -- ... existing code ...

  obtain ⟨pt, hptL, hx0, hx1, hy0, hy1⟩ :=
    rectangle_hits_diagonal_lattice (Lattice p α) d hcyc
      (x₀ := 1) (y₀ := 1) (w := boxSize) (h := boxSize)
      hbox_ge hbox_ge

  -- Now construct Type III parameters directly from pt
  let u := pt.1
  let v := pt.2
  let b := 4 * u - 1
  let c_val := 4 * v - 1

  -- Use lattice membership hptL to show δ is an integer
  have hmem : (g p α : ℤ) ∣ linForm α pt := hptL

  -- The rest follows from ED2 algebraic identity
  -- Key: (bc - 1) / (4p) is an integer because of lattice membership

  use (4 * (b * c_val / ((b * c_val - 1) / (4 * p))) - p).toNat
  use c_val.toNat
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- offset % 4 = 3
    sorry  -- arithmetic from construction
  · -- c > 0
    sorry  -- from v ≥ 1
  · -- (4c - 1) * offset > p
    sorry  -- from bounds
  · -- divisibility
    sorry  -- ED2 identity
```

---

## Sorry 2: boxSize ≥ d (EASY)

```lean
let d := g p α
let boxSize := (p + 3) / 4

have hbox_ge : boxSize ≥ d := by
  sorry
```

### Proof Strategy

Since g(p,α) divides p and p is prime:
- g(p,α) ∈ {1, p}

**Case g = 1:** (p+3)/4 ≥ 1 ✓ (trivial for p ≥ 5)

**Case g = p:** Need (p+3)/4 ≥ p, i.e., p+3 ≥ 4p, i.e., 3 ≥ 3p. But p ≥ 5, contradiction!

So g(p,α) = 1, and the bound is trivial.

### Proof Code

```lean
have hbox_ge : boxSize ≥ d := by
  unfold_let d boxSize
  have hdvd : g p α ∣ p := Nat.gcd_dvd_left p _
  rcases Nat.eq_one_or_self_of_prime_of_dvd hp (g p α) hdvd with h1 | hp_eq
  · -- g p α = 1
    simp only [h1]
    have : (p + 3) / 4 ≥ 1 := by omega
    exact this
  · -- g p α = p, contradiction
    exfalso
    -- If g = p, then (p+3)/4 ≥ p needed, but (p+3)/4 < p for p ≥ 5
    have hlt : (p + 3) / 4 < p := by omega
    -- But we'd need boxSize ≥ d = p
    rw [hp_eq] at hlt
    -- hlt : boxSize < p, but we need boxSize ≥ p, contradiction
    omega
```

---

## Task

### Part 1: Fix Sorry 2 (Easy)

Provide the complete proof for `hbox_ge : boxSize ≥ d`.

### Part 2: Restructure Sorry 1

Either:

**Option A (Preferred):** Delete `decode_lattice_point_to_type3` and show how to complete `dyachenko_type3_existence` by inlining the ED2 construction using the lattice point and its membership proof.

**Option B:** Add the missing hypothesis `(hmem : (↑(g p α) : ℤ) ∣ linForm α (u, v))` to `decode_lattice_point_to_type3` and prove it.

For the ED2 construction, you may use `sorry` for pure arithmetic steps (offset % 4 = 3, c > 0, bound) but must show the structure of how lattice membership enables the divisibility proof.

---

## Output Format

```lean
-- SORRY 2 FIX (complete, no sorry)
have hbox_ge : boxSize ≥ d := by
  [YOUR COMPLETE PROOF]

-- SORRY 1 FIX (restructured)
-- Either show the inlined construction in dyachenko_type3_existence
-- Or show the corrected decode_lattice_point_to_type3 with membership hypothesis
```

---

## Key Insight

The divisibility condition `((4c-1)*offset - p) ∣ (4 * type3_x p offset * c * p)` is NOT true for arbitrary u, v. It's only true when (u,v) comes from the lattice L(p,α), because:

1. Lattice membership means g | αu + v
2. This makes δ = (bc-1)/(4p) an integer
3. The ED2 identity then algebraically guarantees divisibility

Without lattice membership, there's no formula that works for all bounded u, v (as the 36-minute computational search confirmed).
