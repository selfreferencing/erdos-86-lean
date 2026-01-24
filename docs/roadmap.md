# Roadmap: from dataset certificates to an *unbounded* finite covering proof

Stage 6B adds a **fully checkable finite proof** over the verified dataset
of Mordell-hard primes `p ≤ 10^7` (20,513 primes), via explicit certificates.

The remaining goal is to replace the finite dataset with **parametric families**
(or a residue-class exhaustion theorem) that covers *all* Mordell-hard primes.

## 0. What Stage 6B already provides

Files:
- `ErdosStraus/CoveringData.lean` and `ErdosStraus/Covering.lean`

You now have:
- a fixed 10-k cover set `k ∈ {5,7,9,11,14,17,19,23,26,29}`
- a certificate list `certs : List Cert` for all Mordell-hard primes `p ≤ 10^7`
- Lean theorems (proved by `native_decide`) that every certificate satisfies:
  - positivity (`x,y,z > 0`)
  - exact ESC identity `EscEq p x y z`
  - `m = 3 + 4k`
  - `k ∈ kSet`

## 1. Cement the Bradford Type II lemma

File: `ErdosStraus/Bradford.lean`

- Finish the remaining algebraic `sorry` in `bradford_type_ii_valid`.
- Add an analogous lemma for Bradford **Type I** (needed by the 10-k cover on the dataset).

## 2. Promote “certificate correctness” → “witness correctness”

Instead of checking `EscEq` directly (as Stage 6B does), migrate to:

- a certificate format storing only `(p,k,d,type)` plus the definitional `x = x0+k`
- a proof that the Bradford congruence + divisor condition implies `EscEq`

This is the bridge needed for generalization.

## 3. Parametric families for each k in the 10-k cover

For each `k` in `{5,7,9,11,14,17,19,23,26,29}`:

- identify small sets of candidate `d` values (often very small and smooth)
- translate “d divides x^2” into modular divisibility of `x` by a small prime power
- derive explicit congruence conditions on `p` (mod some small modulus) under which:
  - `d ∣ x^2`
  - `d ≡ -x (mod m)` (Type II) or `d ≡ -p*x (mod m)` (Type I)

Encode these as `TypeIIFamily` / `TypeIFamily` objects.

## 4. Finite covering theorem (unbounded)

Final target:

- define a *finite* list of families whose congruence hypotheses cover every
  `MordellHard` residue class (possibly by exhaustion mod a master modulus `M`)
- prove each family implies `Conjecture p`
- conclude:
  `∀ p, Prime p → MordellHard p → Conjecture p`

The Stage 6B dataset proof serves as a regression suite for the family proofs:
every prime in `certs` must be discharged by at least one family.
