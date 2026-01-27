# ED2 Lean 4 Proof Plan for Axiom Elimination

## Date: Session in progress
## Source: GPT Pro responses (2 instances)

---

## Executive Summary

**Goal**: Replace `dyachenko_type3_existence` axiom with a theorem using ED2 lattice machinery.

**Complexity Estimates**:
- Window lemma (Prop 9.25): ~150-300 lines
- Normalization/inverse-test: ~300-800 lines
- Bridge to type3_works: ~100-300 lines
- **Total: ~600-1500 lines**

**Key Reference**: Dyachenko 2025 preprint arXiv:2511.07465

---

## 1. Core Mathematical Objects

### 1.1 The ED2 Kernel Lattice (2D)

```lean
/-- The ED2 kernel lattice: L = {(u,v) : u*b' + v*c' ≡ 0 [ZMOD g]}. -/
def ED2KernelLattice (g : ℕ) (b' c' : ℤ) : AddSubgroup (ℤ × ℤ) := ...

/-- α := gcd(g, b'+c') -/
def ed2Alpha (g : ℕ) (b' c' : ℤ) : ℕ := Nat.gcd g (Int.natAbs (b' + c'))

/-- d' := g/α (diagonal step) -/
def ed2Step (g : ℕ) (b' c' : ℤ) : ℕ := g / ed2Alpha g b' c'
```

### 1.2 The ED2 Window Lemma (Prop 9.25)

```lean
/-- Axis-parallel rectangle [x0, x0+H) × [y0, y0+W). -/
def rect (x0 y0 : ℤ) (H W : ℕ) : Set (ℤ × ℤ) :=
  {p | p.1 ∈ Set.Ico x0 (x0 + (H : ℤ)) ∧ p.2 ∈ Set.Ico y0 (y0 + (W : ℤ))}

/-- ED2 window lemma = Proposition 9.25 ("hitting the box"). -/
theorem ed2_window_lemma
  {g : ℕ} (hg : 0 < g) {b' c' : ℤ}
  (hb : Nat.Coprime g (Int.natAbs b')) (hc : Nat.Coprime g (Int.natAbs c')) :
  ∀ {x0 y0 : ℤ} {H W : ℕ},
    ed2Step g b' c' ≤ H →
    ed2Step g b' c' ≤ W →
    ∃ p : ℤ × ℤ, p ∈ ED2KernelLattice g b' c' ∧ p ∈ rect x0 y0 H W := ...
```

### 1.3 ED2 Parameters Structure

```lean
/-- ED2-admissible parameters for prime p: corresponds to 4/p = 1/A + 1/(b*p) + 1/(c*p). -/
structure ED2Params (p : ℕ) where
  δ b c A : ℕ
  -- core Diophantine identity:
  ed2_id : (A : ℤ) * (4*b*c - b - c) = (p : ℤ) * (b*c)
  -- positivity
  hb : b > 0
  hc : c > 0
  hA : A > 0
```

### 1.4 Type III in ℤ (recommended)

```lean
def type3Z_works (p offset c : ℤ) : Prop :=
  offset ≡ 3 [ZMOD 4] ∧
  0 < c ∧
  let d : ℤ := (4*c - 1) * offset - p
  0 < d ∧
  d ∣ (p + offset) * c * p
```

---

## 2. Required Imports

**Minimal set (NO GeometryOfNumbers needed)**:

```lean
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Int.Interval
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.QuotientGroup
import Mathlib.GroupTheory.Index
```

**Optional (for cleaner interval handling)**:
```lean
import Mathlib.Algebra.Order.ToIntervalMod
```

---

## 3. Bridge Lemmas

### Bridge 1: Type II Equation → Type III

The key algebraic identity:
```
(p+offset)(b+c) = 4*offset*b*c
```

implies `type3Z_works p offset b`.

```lean
theorem typeIIeq_to_type3Z
  (p offset b c : ℤ)
  (hoff : offset ≡ 3 [ZMOD 4])
  (hp : 0 < p) (ho : 0 < offset) (hb : 0 < b) (hc : 0 < c)
  (h : (p + offset) * (b + c) = 4 * offset * b * c) :
  type3Z_works p offset b := ...
```

### Bridge 2: ED2Params → type3_works

```lean
theorem type3_of_ed2 (p : ℕ) (params : ED2Params p) :
  ∃ offset c : ℕ, type3_works p offset c := ...
```

---

## 4. Implementation Order (9 Steps)

1. **Switch to ℤ early** for lattice arguments
   - Add `type3_works_int` versions if needed

2. **Implement kernel lattice** `L` as `AddSubgroup (ℤ×ℤ)` via hom to `ZMod g`
   - Prove membership iff `Int.ModEq` form

3. **Prove three geometry-free lemmas**:
   - `kernel_structure` (v1, v2 in lattice; define α, d')
   - `existsUnique_modEq_in_Ico` (Lemma 9.23, via `Int.existsUnique_equiv`)
   - `ed2_window_lemma` (Prop 9.25)

4. **Define ED2Params structure**, prove `ed2_exists`

5. **Prove bridge**: `type3_of_ed2 : ED2Params p → ∃ offset c, type3_works p offset c`

6. **Replace the axiom**:
```lean
theorem dyachenko_type3_existence_theorem
  (p : ℕ) (hp : Nat.Prime p) (hp1 : p % 4 = 1) :
  ∃ offset c, type3_works p offset c := by
    rcases ed2_exists p hp hp1 with ⟨params, hparams⟩
    exact type3_of_ed2 p params
```

---

## 5. File Structure

```
ESC/Certificates/Type3Z.lean
  - type3Z_works
  - equivalence lemmas Nat ↔ Int

ESC/ED2/WindowLattice.lean
  - ED2KernelLattice
  - ed2Alpha, ed2Step
  - v1_mem, v2_mem
  - exists_unique_Ico_modEq (using toIcoMod)
  - ed2_window_lemma (Prop 9.25)

ESC/ED2/Bridge.lean
  - typeIIeq_to_type3Z (pure algebra)
  - typeIIrepr_to_typeIIeq

ESC/ED2/Existence.lean
  - ED2Params structure
  - ed2_exists theorem
  - dyachenko_type3_existence_theorem (replaces axiom)
```

---

## 6. Key Lemmas to Prove

### Lemma 9.22: Kernel structure + two vectors in L

1. `v1 = (c', -b') ∈ L` (trivial: c'*b' + (-b')*c' = 0)
2. `v2 = (d', d') ∈ L` where d' = g / gcd(g, b'+c')

### Lemma 9.23: Unique representative in interval

Use Mathlib's `toIcoMod`:
```lean
theorem exists_unique_Ico_modEq
  (d : ℤ) (hd : 0 < d) (x0 u0 : ℤ) :
  ∃! u : ℤ, u ∈ Set.Ico x0 (x0 + d) ∧ u ≡ u0 [ZMOD d] := ...
```

### Proposition 9.25: Hit the rectangle

- Pick p0 := (c', -b') from v1_mem
- Let d := ed2Step g b' c'
- Build u* in Ico x0 (x0 + d) congruent to p0.1 mod d
- Define p := p0 + m•(d,d)
- Show p.1 = u* and p.2 ∈ appropriate interval
- Lift from d×d square to H×W rectangle

---

## 7. Index/Covolume Argument

For kernel lattice L ⊂ ℤ²:
- Define φ : ℤ² → ZMod g by (u,v) ↦ u*b' + v*c'
- L = ker(φ)
- If gcd(b',g) = 1, then φ is surjective
- Therefore ℤ²/L ≃ ZMod g, index = g

```lean
(ED2KernelLattice g b' c').quotient ≃+ ZMod g
```

---

## 8. The A-Window Bounds

For p ≡ 1 (mod 4):
```
L(p) := p/4 + 3/4
U(p) := 3p/4 - 3/4
```

Seek A ∈ ℤ ∩ [L(p), U(p)].

Then offset := 4*A - p (which gives offset ≡ 3 mod 4).

---

## 9. Next Steps

1. **Ask GPT for exact Lean code skeleton** for:
   - `ED2KernelLattice` definition
   - `v1_mem`, `v2_mem` proofs
   - `exists_unique_Ico_modEq` using `toIcoMod`

2. **Create file structure** in esc_stage8/

3. **Start with Window Lemma** (~200 lines) - it's independent of ESC algebra

4. **Build bridges incrementally**

---

## References

- Dyachenko 2025: arXiv:2511.07465 "Constructive Proofs of the Erdős-Straus Conjecture for Prime Numbers ≡ 1 (mod 4)"
- Mathlib.Algebra.Order.ToIntervalMod
- Mathlib.Data.Int.ModEq
- Mathlib.MeasureTheory.Group.GeometryOfNumbers (NOT needed for this approach)
