# Stage 8: ten_k_cover_complete — what is proved vs. what remains

This repo now contains a Lean statement of the Stage 8 goal in:

- `ErdosStraus/CoveringUnbounded.lean`

The file proves that the explicit 10-way disjunction

```
k5Sufficient p ∨ k7Sufficient p ∨ ... ∨ k29Sufficient p
```

follows from a single existential lemma:

```
... ∃ k, k ∈ K10 ∧ kSufficient k p
```

Everything after that is just rewriting the existential into the requested disjunction.

## The one remaining mathematical lemma

The remaining lemma is:

```
theorem ten_k_cover_exists (p : ℕ) (hp : Nat.Prime p) (hMH : MordellHard p) :
    ∃ k, k ∈ K10 ∧ kSufficient k p
```

This is the true Stage 8 content.

### Intended proof shape (from Stage 8 prompt)

Stage 8’s QR analysis suggests proving `ten_k_cover_exists` by contradiction.
Assume **every** k in K10 fails:

- `¬ d1Sufficient k p`
- `¬ QRSufficient k p`

Then (by the QR obstruction implications already proved in Stage 6A), each `¬QRSufficient k p`
forces a “QR obstruction” pattern on `x_k = x0(p) + k` modulo `m_k = 4k+3`.
The key claim then is that *all ten* QR obstructions cannot hold simultaneously.

That last claim can be attacked in three ways:

1. **CRT / residue-class intersection**: show the combined modular constraints on `x0(p)`
   have empty intersection with the Mordell-hard residue classes (mod 840).
2. **Inductive pair covering**: show the intersection of failure sets for (k=5,k=7)
   is covered by k=9,11,… and so on.
3. **Prime-factor rigidity**: show simultaneously demanding “all prime factors of x_k are QR”
   across ten shifts forces x0 into an impossibly sparse set.

## What you can do next

A recommended next step is to **encode a finite master modulus** `M` (likely a multiple of 840
and the relevant `m_k`) and a computable predicate `coversBy (k : ℕ) (r : ZMod M)` representing
‘the QR obstruction for k *cannot* hold’ at residue r.

Then you can try to prove:

```
∀ r : ZMod M,
  (MordellHardResidue r) →
  coversBy 5 r ∨ coversBy 7 r ∨ ... ∨ coversBy 29 r
```

by `native_decide`, and separately prove `coversBy k r → kSufficient p` whenever `p ≡ r (mod M)`.

