# Stage 6B (Lean): Finite covering proof **on the 10M dataset** (Mordell-hard primes)

This directory extends the Stage 5 Lean scaffold with a **fully machine-checkable, finite** covering proof
for the *verified dataset* of **all Mordell-hard primes `p ≤ 10^7`** (20,513 primes), using explicit
certificates `(p,x,y,z)` and the empirically discovered 10-k cover set:

`k ∈ {5,7,9,11,14,17,19,23,26,29}`.

> Important: This is a **finite** theorem over the dataset list `certs`.  
> Turning it into an **unbounded** covering proof for *all* Mordell-hard primes requires Stage 7
> (parametric families / residue-class covering), which is sketched in `docs/roadmap.md`.

## New files added in Stage 6B

* `ErdosStraus/CoveringData.lean`
  - Defines the structure `Cert` and the constant list `certs : List Cert` (20,513 items),
    generated from `data/kset_certificates_10M.jsonl`.
* `ErdosStraus/Covering.lean`
  - Defines the 10-k set as `kSet`
  - Proves via `native_decide` that **every** certificate in `certs` satisfies:
    - positivity of `x,y,z`
    - the exact identity `EscEq p x y z`
    - `m = 3 + 4k`
    - `k ∈ kSet`
  - Derives `Conjecture p` for each `p` in the dataset.
* `ErdosStraus/Families_k*.lean`
  - For each k in the 10-k set, defines the filtered sublist `certs_k{k}` and proves
    certificate correctness on that sublist using `native_decide`.

## Data

* `data/kset_certificates_10M.jsonl`
  - One line per Mordell-hard prime `p ≤ 10^7`, with fields:
    `{p,residue_840,k,m,type,x,d,y,z}`
  - Here `type ∈ {"I","II"}` indicates Bradford Type I vs Type II.

## Regenerating the Lean data file

The Lean data file was generated from the JSONL using a small Python generator.
See `scripts/generate_covering_lean.py` (created in this stage).

## Build (in an environment with Lean + internet)

```bash
lake update
lake build
```

## Notes about this sandbox

In this ChatGPT execution sandbox we do **not** have a Lean toolchain preinstalled and outbound
network access is restricted, so the code here is authored to be buildable in a standard
Lean+mathlib setup but could not be compiled end-to-end *inside this container*.
