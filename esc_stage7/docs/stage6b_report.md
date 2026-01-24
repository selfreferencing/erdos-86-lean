# Stage 6B report (bounded Lean formalization)

## What this stage delivers

- A deterministic **10-k cover** for all Mordell-hard primes `p ≤ 10^7`, with
  
  \[
  K10 = \{5,7,9,11,14,17,19,23,26,29\}
  \]

- A **Lean-embedded** certificate table (`20,513` entries) giving explicit `(p,k,x,y,z)` solutions.

- Lean theorems that:
  1. verify each embedded certificate satisfies the exact Diophantine identity `ES p x y z`;
  2. prove that any `p` covered by the table has `HasSolution p`;
  3. provide a bounded theorem `erdos_straus_mordell_hard_upto_10M` for primes `p ≤ 10^7`.

## How certificates are built

Input dataset:
- `data/hard_primes_minimal.jsonl` (minimal-x Bradford certificates for all Mordell-hard primes ≤ 10^7).

Cover construction:
- For each prime `p` from the input, we run `bradford_fixed_k(p,k)` for `k ∈ K10` and take the first `k` that yields a solution.
- The resulting certificate is written to `data/hard_primes_k10_cover.jsonl`.
- A Lean file embedding all `(p,k,x,y,z)` is generated: `ErdosStraus/CertificatesK10_10M.lean`.

## Lean files

- `ErdosStraus/CertificatesK10_10M.lean`
  - defines `K10` and `certsK10 : Array K10Cert`
  - defines `CertOk` and proves `all_certsK10_ok` via `native_decide`

- `ErdosStraus/Covering.lean`
  - defines `MordellHard840` as the 6 residue classes modulo 840
  - defines `Covered10M p` (existence of a certificate in the table)
  - proves `erdos_straus_mordell_hard_upto_10M`

- `ErdosStraus/FamiliesKSet.lean`
  - provides a 10-way disjunction `ten_k_cover_upto_10M` (bounded)

## Notes and limitations

- This repository snapshot is intended to be built in a standard Lean+Mathlib environment.
  This sandbox does not include a Lean toolchain.

- The theorem `erdos_straus_mordell_hard_upto_10M` is **bounded** (up to `10^7`).
  Stage 6C is intended to replace the finite lookup with an **unbounded residue-class covering system**, so that the theorem no longer needs a numeric bound.

- About solution types:
  - Among the chosen K10 certificates, roughly `~96.3%` are Type II and `~3.7%` are Type I.
  - In this bounded formalization we embed direct `(x,y,z)` certificates, so we do not need separate Lean lemmas for Type I vs Type II Bradford witnesses.
