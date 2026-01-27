# GPT Response 3: The Lattice/Rectangle-Hitting Proof

## Key Insight: The Axiom IS the ED2 Factorization Identity

### Normalized Form of the Axiom

Let M := 4αd'. Then X ≡ -1 (mod M) means X = Mb' - 1 for some b' ≥ 1.
Similarly Y = Mc' - 1.

The axiom is **equivalent** to:

> For every prime P ≡ 1 (mod 4), there exist:
> - α squarefree, d' ≥ 1
> - b', c' ≥ 1 with gcd(b', c') = 1
>
> such that:
> ```
> (4αd'b' - 1)(4αd'c' - 1) = 4αP(d')² + 1
> ```

This is a **single algebraic identity** plus gcd(b', c') = 1.

---

## Dyachenko's Theorem 9.21 + Remark 9.20 Imply the Axiom

From the paper:
- **Theorem 9.21**: For every P ≡ 1 (mod 4), ED2 triple (δ, b, c) exists with canonical normalization producing α squarefree, d', and gcd(b', c') = 1
- **Remark 9.20**: The normalized factorization identity holds:
  ```
  (4αd'b' - 1)(4αd'c' - 1) = 4αP(d')² + 1
  ```

This is **literally the same statement** as our axiom with X = 4αd'b' - 1, Y = 4αd'c' - 1.

**The axiom is a direct corollary of Dyachenko's Theorem 9.21 + Remark 9.20.**

---

## The Geometric Proof Mechanism

The proof is NOT about "randomness of prime factors of 4Pδ + 1".
It's about **"a lattice hits a big enough rectangle"**.

### Skeleton of the Argument

1. **Lattice encoding**: After normalization, the problem is encoded into an integer lattice:
   ```
   L = {(u,v) ∈ ℤ² : u·b' + v·c' ≡ 0 (mod g)}
   ```

2. **Diagonal period** (Lemma 9.22):
   ```
   (d', d') ∈ L,  where d' = g/α,  α = gcd(g, b'+c')
   ```

3. **1-D congruence fact** (Lemma 9.23):
   Any interval of length ≥ d' contains a representative of any residue class (mod d').

4. **Rectangle-hitting** (Proposition 9.25):
   Any axis-aligned rectangle of width ≥ d' and height ≥ d' must intersect L.

5. **Role of α** (Corollary 9.26):
   Larger α → smaller d' = g/α → higher "diagonal layer density"
   With polylog box sizes, the condition becomes satisfiable.

### The Polylog Bound

Dyachenko's theorem includes an explicit bound:
```
1 ≤ δ, b, c ≤ (log P)^{A₀}  for some fixed constant A₀ > 0
```

So B(P) = (log P)^{A₀} is guaranteed by the lattice geometry.

---

## Getting a CONSTANT Bound (δ ≤ 100)

To make B constant in a Lean-friendly way, use the **covering-congruence** strategy (Appendix D.7):

1. Choose finite family F = {(rᵢ, sᵢ)} and set moduli Mᵢ := 4αsᵢrᵢ - 1
2. Let Q = lcm(M₁, ..., Mₖ)
3. Prove "covering condition": every residue class p ∈ {0, ..., Q-1} satisfies p ≡ -4αsᵢ² (mod Mᵢ) for some i

Under the covering condition, Theorem D.14 and Corollary D.15 give explicit construction.

### Why This is Lean-Friendly

The covering condition is a **finite computation over residues modulo Q**:
- Verify by reflection / kernel computation
- Then the rest is purely algebra
- Get uniform bound: δ = α(d')² = αrᵢ² ≤ max_i αrᵢ²

**This gives a literal constant B!**

---

## Mapping to Lean

Once you have (α, d', b', c') from ED2:
- Set X := 4αd'b' - 1
- Set Y := 4αd'c' - 1
- Set N := 4αP(d')² + 1

Then:
1. N = X·Y by the normalized factorization identity
2. X ≡ Y ≡ -1 (mod 4αd') by construction
3. gcd((X+1)/(4αd'), (Y+1)/(4αd')) = gcd(b', c') = 1 by canonical constraint

**The Lean axiom becomes a theorem once you formalize ED2 lemmas.**

---

## Required Lean Lemmas

To fully formalize:
1. **Congruence-interval lemma**: Any interval of length ≥ d' contains a representative of any residue class (mod d')
2. **Diagonal-period rectangle lemma**: Rectangle of size ≥ d' × d' intersects the lattice L
3. **Translation lemma**: (b', c') ↦ (X, Y) with the factorization identity

---

## Bottom Line

| Approach | Bound | Lean Difficulty |
|----------|-------|-----------------|
| Polylog (lattice geometry) | δ ≤ (log P)^A | Moderate - need lattice lemmas |
| Constant (covering-congruence) | δ ≤ 100 | Lower - finite computation + algebra |
| Axiom (current) | N/A | None - but not a proof |

**Recommended path**: Build finite residue covering F, verify by computation, then algebra gives factorization.
