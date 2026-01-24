# esc_stage6b — Stage 6B finite covering proof (bounded formalization)

This folder extends the **Stage 5** Lean scaffold with a **Stage 6B** deliverable:

- An embedded certificate table (`20,513` entries) for all *Mordell-hard* primes `p ≤ 10^7`,
  where each prime is solved by one of the 10 k-values

```
K10 = {5,7,9,11,14,17,19,23,26,29}
```

- A Lean theorem `erdos_straus_mordell_hard_upto_10M` in `ErdosStraus/Covering.lean` that
  turns the finite certificate table into `HasSolution p`.

This is a **bounded** formalization (up to `10^7`) of the computational Stage 3/4 result.
The intended next step (Stage 6C) is to replace the lookup table with a genuine residue-class
covering system to obtain an *unbounded* theorem for all Mordell-hard primes.

## Key files added in Stage 6B

- `ErdosStraus/CertificatesK10_10M.lean`
  - defines `K10` and `certsK10 : Array K10Cert`
  - proves `all_certsK10_ok : ∀ i, CertOk certsK10[i]` via `native_decide`

- `ErdosStraus/Covering.lean`
  - defines `MordellHard840` (six residue classes modulo 840)
  - defines `Covered10M p` (membership in the certificate list)
  - main theorem `erdos_straus_mordell_hard_upto_10M` (bounded)

- `ErdosStraus/FamiliesKSet.lean`
  - exposes the 10-k cover in a disjunctive “family” form, also bounded

## Data and generation scripts

- `data/hard_primes_minimal.jsonl`
  - Stage 3/4 minimal-x certificates (input)

- `data/hard_primes_k10_cover.jsonl`
  - Stage 6B cover certificates with k in K10 (generated)

- `scripts/build_k10_dataset.py`
  - regenerates `hard_primes_k10_cover.jsonl` and `CertificatesK10_10M.lean` deterministically

## Build instructions (requires Lean 4 + Mathlib)

This sandbox does **not** include a Lean toolchain, so compilation must be done in a normal
Lean+Mathlib environment:

```bash
lake update
lake exe cache get
lake build
```

If `native_decide` becomes too slow for your setup, a common mitigation is to replace the
hypothesis `Nat.Prime p` in the bounded theorem by an explicit membership in the certified
prime list, avoiding primality checks during evaluation.
