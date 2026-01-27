# Task: Eliminate a `sorry` in a Lean 4 Formalization of the Erdős-Straus Conjecture

## Context

I'm formalizing the Erdős-Straus conjecture (4/n = 1/x + 1/y + 1/z for all n ≥ 2) in Lean 4. The proof reduces to showing that for every prime p ≡ 1 (mod 4), there exist natural numbers offset, b, c with:

```
offset % 4 = 3 ∧ b > 0 ∧ c > 0 ∧
(↑p + ↑offset : ℤ) * (↑b + ↑c) = 4 * ↑offset * ↑b * ↑c
```

This is the "Type II Diophantine equation." Setting A = (p + offset)/4, it's equivalent to 4/p = 1/A + 1/(bp) + 1/(cp).

## Current State

The proof handles:
- p ≡ 2 (mod 3): explicit formula with offset=3
- p ≡ 1 (mod 3), p ≡ 5 (mod 8): explicit formula with offset=7
- p ≡ 1 (mod 24): deep case analysis on residues mod 7, 5, 11, 19, 23

For p ≡ 1 (mod 24) with p%7 ∈ {1,2,4} and p%5 ∈ {1,4}, the proof uses "Lemma D.6" (from Dyachenko 2025) with 22 different M values to cover most primes. Then 9 specific stubborn primes are handled by explicit certificates.

**One sorry remains**, at line 4757 of `Existence.lean`, inside theorem `ed2_qr_classes`. At that point in the proof, we know:
- `p : ℕ`, `hp : Nat.Prime p`, `hp24 : p % 24 = 1`
- `p % 7 ∈ {1,2,4}`, `p % 5 ∈ {1,4}`
- p is NOT in any of the D.6 covered residue classes (22 M values from 39 to 167)
- p is NOT one of the 9 certificate primes
- We need: `∃ offset b c : ℕ, offset % 4 = 3 ∧ b > 0 ∧ c > 0 ∧ (↑p + ↑offset : ℤ) * (↑b + ↑c) = 4 * ↑offset * ↑b * ↑c`

Computational analysis shows that no finite set of D.6 M-values can cover all residue classes. We need a different approach for the remaining primes.

## What I Need You To Write

Write a Lean 4 theorem that proves the Type II equation has solutions for ALL primes p ≡ 1 (mod 4) with p above some explicit bound B, using the **window lemma** approach. This theorem will replace the sorry.

### Approach: Window Lemma + Explicit Witness Construction

**Mathematical argument (from Dyachenko 2025, Prop 9.25):**

For prime p ≡ 1 (mod 4), choose any δ ≡ 3 (mod 4). Set g = δ, and consider the 2D kernel lattice L = {(u,v) ∈ ℤ² : u·b' + v·c' ≡ 0 (mod g)} where b', c' are chosen with gcd(b',g) = gcd(c',g) = 1.

The window lemma (already proven) says: any g×g rectangle contains a lattice point of L. The "A-window" for the ED2 problem has width proportional to p. So for p > g², the window is large enough.

A lattice point (u,v) in the window gives b = g·b', c = g·c' satisfying the linear congruences. The back-test: set A = b·c/δ and verify the Type II identity (p+δ)(b+c) = 4δbc.

### Available Infrastructure (already proven, in the codebase)

**File: `ErdosStraus/ED2/WindowLattice.lean`**

```lean
-- The kernel lattice L = {(u,v) : u*b' + v*c' ≡ 0 (mod g)}
def ED2KernelLattice (g : ℕ) (b' c' : ℤ) : AddSubgroup (ℤ × ℤ)

-- α = gcd(g, b'+c'),  d' = g/α  (the diagonal step)
def ed2Alpha (g : ℕ) (b' c' : ℤ) : ℕ := Nat.gcd g (Int.natAbs (b' + c'))
def ed2Step (g : ℕ) (b' c' : ℤ) : ℕ := g / ed2Alpha g b' c'

-- (c', -b') ∈ L
theorem v1_mem {g : ℕ} {b' c' : ℤ} (hb : Nat.Coprime g (Int.natAbs b'))
    (hc : Nat.Coprime g (Int.natAbs c')) : (c', -b') ∈ ED2KernelLattice g b' c'

-- (d', d') ∈ L
theorem v2_mem {g : ℕ} (hg : 0 < g) {b' c' : ℤ}
    (hb : Nat.Coprime g (Int.natAbs b')) (hc : Nat.Coprime g (Int.natAbs c')) :
    ((ed2Step g b' c' : ℤ), (ed2Step g b' c' : ℤ)) ∈ ED2KernelLattice g b' c'

-- In any half-interval [x0, x0+d) with d ≥ m, there's exactly one u ≡ r (mod m)
theorem exists_unique_Ico_modEq (m : ℕ) (hm : 0 < m) (r : ℤ) (x0 : ℤ) (H : ℕ)
    (hH : m ≤ H) : ∃! u : ℤ, u ∈ Set.Ico x0 (x0 + H) ∧ u ≡ r [ZMOD m]

-- Axis-parallel rectangle [x0, x0+H) × [y0, y0+W)
def rect (x0 y0 : ℤ) (H W : ℕ) : Set (ℤ × ℤ)

-- *** THE MAIN WINDOW LEMMA (Prop 9.25) ***
-- Any g×g rectangle contains a lattice point
theorem ed2_window_lemma
    {g : ℕ} (hg : 0 < g) {b' c' : ℤ}
    (_hb : Nat.Coprime g (Int.natAbs b')) (hc : Nat.Coprime g (Int.natAbs c')) :
    ∀ {x0 y0 : ℤ} {H W : ℕ},
      g ≤ H →
      g ≤ W →
      ∃ p : ℤ × ℤ, p ∈ ED2KernelLattice g b' c' ∧ p ∈ rect x0 y0 H W
```

**File: `ErdosStraus/ED2/Bridge.lean`**

```lean
-- The Type II equation implies Type III works
theorem typeIIeq_to_type3Z
    (p offset b c : ℤ)
    (hoff : offset % 4 = 3)
    (hp : 0 < p) (ho : 0 < offset) (hb : 0 < b) (hc : 0 < c)
    (h : (p + offset) * (b + c) = 4 * offset * b * c) :
    type3Z_works p offset b

-- ED2 parameters structure
structure ED2Params (p : ℕ) where
  δ : ℕ; b : ℕ; c : ℕ; A : ℕ
  ed2_id : (A : ℤ) * (4*b*c - b - c) = (p : ℤ) * (b*c)
  hδA : (δ : ℤ) = 4 * (A : ℤ) - (p : ℤ)
  hb : b > 0; hc : c > 0; hA : A > 0; hδ : δ > 0
  hδ_mod : δ % 4 = 3

-- ED2Params yield a Type III solution
theorem type3_of_ed2 (p : ℕ) (hp : 0 < p) (params : ED2Params p) :
    ∃ offset c : ℕ, type3_works p offset c
```

**File: `ErdosStraus/Covering.lean`**

```lean
-- Extract from List.Forall given membership
theorem forall_of_forall_mem {α : Type} {P : α → Prop} {l : List α} :
    List.Forall P l → ∀ a, a ∈ l → P a
```

**File: `ErdosStraus/ED2/Type2Data.lean`**

```lean
structure Type2Cert where
  p : ℕ; offset : ℕ; b : ℕ; c : ℕ

def Type2CertOK (cert : Type2Cert) : Prop :=
  cert.offset % 4 = 3 ∧ cert.b > 0 ∧ cert.c > 0 ∧
  (cert.p + cert.offset) * (cert.b + cert.c) = 4 * cert.offset * cert.b * cert.c
```

**File: `ErdosStraus/ED2/Type2Covering.lean`**

```lean
-- All 750 certificates are valid (native_decide)
theorem type2_certs_all_ok : List.Forall Type2CertOK type2Certs := by native_decide

-- Bridge from certificate to existential witness
theorem type2_cert_ok_gives_witness (cert : Type2Cert) (h : Type2CertOK cert) :
    ∃ offset b c : ℕ,
      offset % 4 = 3 ∧ b > 0 ∧ c > 0 ∧
      (↑cert.p + ↑offset : ℤ) * (↑b + ↑c) = 4 * ↑offset * ↑b * ↑c
```

## Approach Options (pick whichever is more feasible)

### Option A: Asymptotic Argument (eliminates sorry completely)

Write a theorem like:

```lean
theorem ed2_large_prime (p : ℕ) (hp : Nat.Prime p) (hp4 : p % 4 = 1) (hp_large : p ≥ 10000) :
    ∃ offset b c : ℕ, offset % 4 = 3 ∧ b > 0 ∧ c > 0 ∧
      (↑p + ↑offset : ℤ) * (↑b + ↑c) = 4 * ↑offset * ↑b * ↑c
```

The argument:
1. Choose δ = 3 (so offset = 3, A = (p+3)/4)
2. Set g = 3, b' = 1, c' = 1 (or appropriate coprime values)
3. Apply ed2_window_lemma to get a lattice point in the A-window
4. The lattice point gives (b, c) satisfying the identity
5. Verify positivity from the window bounds

This works when p is large enough that the A-window exceeds g in both dimensions. The challenge is connecting the lattice point back to valid (offset, b, c).

**Alternative parametrization**: Choose δ = 7, or iterate over small δ values until one works. For δ = 3, the covered fraction is primes where A² has a divisor ≡ 2 (mod 3). For δ = 7, different primes are covered.

### Option B: Bounded Certificate Verification (simpler, keeps a weaker sorry)

Write infrastructure to verify certificates up to bound B = 10,000,000:

```lean
-- In a new file ED2/Type2CertExtended.lean:

-- Extended certificate list (generated by Python, ~7500 entries)
def type2CertsExtended : List Type2Cert := [...]

-- Verify all extended certificates
theorem type2_certs_extended_all_ok : List.Forall Type2CertOK type2CertsExtended := by
  native_decide

-- All sorry-region primes up to B have certificates
-- (This requires a decidable "sorry region" predicate)
def inSorryRegion (p : ℕ) : Prop :=
  p % 24 = 1 ∧ p % 7 ≠ 0 ∧ p % 7 ≠ 3 ∧ p % 7 ≠ 5 ∧ p % 7 ≠ 6 ∧
  p % 5 ≠ 0 ∧ p % 5 ≠ 2 ∧ p % 5 ≠ 3

-- Main theorem: for p < B in sorry region, solution exists
theorem sorry_region_covered_to_B (p : ℕ) (hp : Nat.Prime p)
    (hsr : inSorryRegion p) (hlt : p < 10000000) :
    ∃ offset b c : ℕ, offset % 4 = 3 ∧ b > 0 ∧ c > 0 ∧
      (↑p + ↑offset : ℤ) * (↑b + ↑c) = 4 * ↑offset * ↑b * ↑c
```

Then at the sorry location, split on `p < 10000000` and use the bounded result for the true branch.

## Important Lean 4 Conventions

- Use `import Mathlib.Tactic` for access to `omega`, `norm_num`, `push_cast`, `nlinarith`, `linear_combination`, `positivity`, `linarith`, `ring`
- Use `import Mathlib.Data.Int.ModEq` for modular arithmetic
- Natural number subtraction is truncating (use ℤ for subtraction)
- `↑n` is `Nat.cast n` (coercion ℕ → ℤ)
- `push_cast` pushes ↑ through arithmetic operations
- `exact_mod_cast` handles goals differing only by casts
- `zify` converts ℕ goals to ℤ
- For large `norm_num` computations, use `set_option maxHeartbeats N in` before the theorem
- For `native_decide`, Lean compiles and runs the decision procedure natively

## File Structure

```
ErdosStraus/
  ED2/
    Existence.lean      -- Main proof (sorry is here at line 4757)
    WindowLattice.lean  -- Window lemma (proven)
    Bridge.lean         -- Type II → Type III bridge (proven)
    Type2Data.lean      -- Type2Cert structure
    Type2CertData.lean  -- 750 certificates
    Type2Covering.lean  -- Certificate verification
```

## What to produce

Write complete, compilable Lean 4 code. Put it in a new file (e.g., `ED2/Asymptotic.lean` or `ED2/Phase3.lean`). Include all necessary imports. The theorem should have a signature compatible with being called from the sorry location in `ed2_qr_classes`.

The sorry location needs:
```lean
∃ offset b c : ℕ, offset % 4 = 3 ∧ b > 0 ∧ c > 0 ∧
  (↑p + ↑offset : ℤ) * (↑b + ↑c) = 4 * ↑offset * ↑b * ↑c
```

where `p : ℕ` is prime with `p % 24 = 1` and various mod 7, mod 5 conditions.

Focus on getting the TYPES right. Mark difficult proof steps with `sorry` if needed, but make the overall structure and theorem statements correct. I can fill in individual sorry'd lemmas later.
