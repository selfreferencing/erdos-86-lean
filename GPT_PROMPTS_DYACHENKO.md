# GPT Prompts for Dyachenko.lean Completion

## Prompt 1: Fix quotientEquivZMod_diag (technical simp)

```
You are completing a Lean 4 formalization. I need to prove that the quotient equivalence sends π(1,1) to (α+1).

Current code with sorry:

```lean
/-- quotientEquivZMod sends π(1,1) to the class of (α+1) in ZMod (g P α) -/
theorem quotientEquivZMod_diag (P : ℕ) (α : ℤ) :
    quotientEquivZMod P α (diagQuot P α) = ((α + 1 : ℤ) : ZMod (g P α)) := by
  classical
  unfold quotientEquivZMod diagQuot linFormZModHom linForm
  simp only [AddEquiv.trans_apply, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  sorry
```

Context:
- `quotientEquivZMod` is defined as `e0.trans e1` where:
  - `e0 : ((ℤ × ℤ) ⧸ Lattice P α) ≃+ ((ℤ × ℤ) ⧸ f.ker)` via `QuotientAddGroup.quotientAddEquivOfEq`
  - `e1 : ((ℤ × ℤ) ⧸ f.ker) ≃+ ZMod (g P α)` via `QuotientAddGroup.quotientKerEquivOfSurjective`
- `f = linFormZModHom P α` where `f(u,v) = (α*u + v : ZMod (g P α))`
- `diagQuot P α = QuotientAddGroup.mk' (Lattice P α) (1, 1)`
- Goal: show f(1,1) = α*1 + 1 = α + 1

The issue is unfolding the quotient equivalence composition. After the simp, the goal should be reducible to `↑(α * 1 + 1) = ↑(α + 1)` in ZMod.

Provide a complete proof replacing the sorry. Use native_decide, decide, rfl, norm_cast, push_cast, or explicit computation tactics as needed. The proof should compile in Lean 4 with Mathlib.
```

---

## Prompt 2: Complete dyachenko_type3_existence (main theorem)

```
You are completing the main theorem in a Lean 4 formalization of Dyachenko's ESC proof.

Goal: Prove that for every prime p ≡ 1 (mod 4), p ≥ 5, there exist Type III parameters.

```lean
theorem dyachenko_type3_existence (p : ℕ) (hp : Nat.Prime p)
    (hp_mod : p % 4 = 1) (hp_ge : p ≥ 5) :
    ∃ offset c : ℕ,
      offset % 4 = 3 ∧
      c > 0 ∧
      (4 * c - 1) * offset > p ∧
      ((4 * c - 1) * offset - p) ∣ (4 * type3_x p offset * c * p) := by
  sorry
```

where `type3_x p offset := (p + offset) / 4`.

Available lemmas (all proven, no sorry):

```lean
-- Lattice definition
def Lattice (P : ℕ) (α : ℤ) : AddSubgroup (ℤ × ℤ)
def g (P : ℕ) (α : ℤ) : ℕ := Nat.gcd P (Int.natAbs (α^2 + 1))

-- Quotient infrastructure
theorem quotientEquivZMod (P : ℕ) (α : ℤ) : ((ℤ × ℤ) ⧸ Lattice P α) ≃+ ZMod (g P α)
theorem card_quotient (P : ℕ) (α : ℤ) : Nat.card ((ℤ × ℤ) ⧸ Lattice P α) = g P α
theorem quotient_isAddCyclic (P : ℕ) (α : ℤ) : IsAddCyclic ((ℤ × ℤ) ⧸ Lattice P α)

-- Generator condition
theorem diag_generates_of_isUnit (P : ℕ) (α : ℤ)
    (hunit : IsUnit (((α + 1 : ℤ) : ZMod (g P α)))) :
    AddSubgroup.zmultiples (diagQuot P α) = ⊤

-- Rectangle intersection
structure QuotientCyclicOfDiag (L : AddSubgroup (ℤ × ℤ)) (d : ℕ) : Prop where
  d_pos : d > 0
  diag_mem : ((d : ℤ), (d : ℤ)) ∈ L
  order_eq : addOrderOf (diagElem L) = d
  card_eq : Nat.card (Q L) = d

theorem rectangle_hits_diagonal_lattice
    (L : AddSubgroup (ℤ × ℤ)) (d : ℕ) [Fintype (Q L)]
    (hcyc : QuotientCyclicOfDiag L d)
    (x₀ y₀ : ℤ) (w h : ℕ) (hw : w ≥ d) (hh : h ≥ d) :
    ∃ p : ℤ × ℤ, p ∈ L ∧ x₀ ≤ p.1 ∧ p.1 ≤ x₀ + w ∧ y₀ ≤ p.2 ∧ p.2 ≤ y₀ + h

-- ED2 identity
theorem ED2_identity {P A b c δ : ℚ}
    (hP : P ≠ 0) (hA : A ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hδ : δ ≠ 0)
    (hDy : (4*b - 1) * (4*c - 1) = 4*P*δ + 1)
    (hAdef : A = (b*c)/δ) :
    (4 / P) = (1 / A) + (1 / (b*P)) + (1 / (c*P))
```

Strategy from Dyachenko 2025 (arXiv:2511.07465, Theorems 9.21/10.21):

1. **Choose α** as a quadratic non-residue mod p
   - For p ≡ 1 (mod 4), use `ZMod.exists_sq_eq_neg_one` to get i with i² = -1
   - Then α = i+1 or similar choice where α² ≢ -1 (mod p)
   - Alternative: use Legendre symbol API

2. **Compute g(p, α)** for QNR α
   - g(p, α) = gcd(p, |α² + 1|)
   - For QNR, α² ≢ -1 (mod p), so p ∤ (α² + 1)
   - But g(p, α) divides p, so g(p, α) = 1 or a proper divisor

3. **Show (α+1) is a unit mod g(p, α)**
   - Need gcd(α+1, g(p, α)) = 1
   - This ensures diagQuot generates the quotient

4. **Construct Fintype instance**
   ```lean
   haveI : Fintype ((ℤ × ℤ) ⧸ Lattice p α) :=
     Fintype.ofEquiv (ZMod (g p α)) (quotientEquivZMod p α).symm.toEquiv
   ```

5. **Apply rectangle intersection** to the box [1, (p+3)/4] × [1, (p+3)/4]
   - The box has side length (p+3)/4 - 1 + 1 = (p+3)/4
   - Need (p+3)/4 ≥ g(p, α)
   - Since g(p, α) ≤ p and (p+3)/4 ≥ (p+3)/4 > p/4, this works for large p

6. **Decode the lattice point (u, v)** to ED2 parameters
   - b = 4u - 1
   - c = 4v - 1
   - δ = ((4u-1)(4v-1) - 1) / (4p)
   - A = bc/δ

7. **Translate to Type III**
   - offset = 4A - p
   - Same c
   - Verify offset % 4 = 3 and divisibility

Provide the complete proof. This is substantial (~100 lines). Focus on:
- Correct choice of α
- Proper Fintype construction
- Careful handling of integer/natural number conversions
- The divisibility condition at the end

Use Mathlib's ZMod, Nat.Prime, and number theory APIs.
```

---

## Usage

1. Copy Prompt 1 to GPT, get the fix for `quotientEquivZMod_diag`
2. Copy Prompt 2 to GPT, get the complete proof for `dyachenko_type3_existence`
3. Paste the results into Dyachenko.lean and compile

If GPT's proofs don't compile, send the error messages back to GPT for fixes.
