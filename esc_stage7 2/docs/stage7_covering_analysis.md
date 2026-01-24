# Stage 7: Unbounded residue-class covering (scaffold)

This directory upgrades the **Stage 6B bounded** proof (all Mordell-hard primes `p ≤ 10^7`) to a **Stage 7 unbounded** proof *architecture*.

At Stage 7 we are not yet claiming a complete unbounded cover: the key covering lemma remains a `sorry` in Lean (see `ErdosStraus/CoveringUnbounded.lean`).

---

## 1. Master modulus `M`

Stage 7 asks for a master modulus divisible by the ten Bradford `m`-values associated to the 10-k cover set:

- `K10 = {5,7,9,11,14,17,19,23,26,29}`
- `m(k) = 3 + 4k ∈ {23,31,39,47,59,71,79,95,107,119}`

We take:

- `Mₘ = lcm(23,31,39,47,59,71,79,95,107,119)
       = 523,171,154,575,661,865`
- `M = lcm(840, Mₘ)
     = 4,185,369,236,605,294,920`

Factorization:

- `Mₘ = 3·5·7·13·17·19·23·31·47·59·71·79·107`
- `M  = 2^3·3·5·7·13·17·19·23·31·47·59·71·79·107`

⚠️ **Important practical note:** `M` is ~`4.2×10^18`. Enumerating residues `r < M` is infeasible.

So, while `ErdosStraus/CoveringUnbounded.lean` defines the requested shape

```lean
def MordellHardResiduesM : Finset ℕ := (Finset.range M).filter ...
```

that finset is meant as a *specification*, not a computable object.

---

## 2. What “residue cover” means here

For a fixed `k`, Bradford Type II uses

- `x = ⌈p/4⌉ + k = (p + (4k+3)) / 4` (for Mordell-hard primes `p ≡ 1 (mod 4)`)
- `m = 4x - p = 3 + 4k`

and seeks a divisor `d` of `x^2` such that

- `d ≤ x`
- `d ≡ -x (mod m)`  (implemented as `Nat.ModEq m (d+x) 0`).

A **finite covering proof** is a finite collection of *sufficient conditions* that imply the existence of such a `d` for at least one `k ∈ K10`, and that collectively apply to **every** Mordell-hard prime.

---

## 3. Current Lean scaffold

### Files

- `ErdosStraus/CoveringUnbounded.lean`
  - defines `M`
  - defines `MordellHardResiduesM` (non-computable spec)
  - defines placeholder `coveringK`
  - states the key missing lemma `ten_k_cover_complete` (**sorry**)
  - proves the main theorem `erdos_straus_mordell_hard_unbounded` assuming the cover lemma

- `ErdosStraus/FamiliesK10Common.lean`
  - defines `mOfK`, `xOfK`
  - defines the **d=1 parametric family** predicate:
    ```lean
    def d1Sufficient (k p : ℕ) : Prop := p % (16*k + 12) = (12*k + 5)
    ```
  - provides a placeholder witness lemma `d1Sufficient_witness` (**sorry**)
  - provides a generic bridge `d1Sufficient_gives_solution` (**sorry**, needs Stage 6A coprimality + algebra)

- `ErdosStraus/Families_k{5,7,9,11,14,17,19,23,26,29}.lean`
  - each defines `kXSufficient p := d1Sufficient kX p`
  - each proves `kX_gives_solution` by applying `d1Sufficient_gives_solution`.

### What remains (the real Stage 7 work)

1. **Upgrade each `kSufficient` beyond the `d=1` family.**
   - The `d=1` family gives only one residue class mod `4m`.
   - Empirically (dataset up to `10^7`) almost all solutions use `d` that depends on divisors of `x`, so each `k` likely needs *several* residue families.

2. **Prove `ten_k_cover_complete`.**
   - This is the global residue covering theorem.
   - It can be attacked by building explicit residue families for each `k` and then doing a finite residue analysis on a carefully chosen smaller modulus (not the full `M`).

3. **Replace the placeholder `coveringK`.**
   - Once a finite cover is proved, `coveringK` can be implemented as a computable selector based on the residue class of `p`.

---

## 4. Suggested next step (engineering)

A practical route that matches the Stage 7 prompt without enumerating `M`:

1. For each `k ∈ K10`, pick a finite set of *explicit witnesses* `d` that are guaranteed divisors of `x^2` based on forced divisibility patterns (parity, `3 | x` when `k ≡ 2 (mod 3)`, etc.).
2. For each such `(k,d)`, translate `d ≡ -x (mod m)` into a congruence on `p`:

   - with `m = 4k+3` and `x = (p+m)/4`, the condition becomes
     
     `p ≡ -(m + 4d) (mod 4m)`.

3. Assemble these residue constraints into `kSufficient` as a disjunction of finitely many congruence classes.
4. Choose a **smaller master modulus** that is the `lcm` of the moduli used in those congruences (plus 840), and prove the cover by `native_decide` on `Fin masterModulus`.

This is the “finite covering system” in a form Lean can handle.
