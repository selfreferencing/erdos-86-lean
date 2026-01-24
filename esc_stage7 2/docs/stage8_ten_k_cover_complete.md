# Stage 8: `ten_k_cover_complete` — current status and remaining gap

This repository snapshot now implements the **logical Stage 8 reduction** in Lean:

* `kXSufficient p` is upgraded to
  ```lean
  d1Sufficient k p ∨ QRSufficient k p
  ```
  for each `k ∈ {5,7,9,11,14,17,19,23,26,29}`.

* `CoveringUnbounded.lean` proves `ten_k_cover_complete` **from** a single missing lemma
  `no_tenfold_obstruction`.

## New/updated Lean files

* `ErdosStraus/QRCommon.lean`
  - defines the Stage 8 QR predicates:
    - `PrimeFactorQR m x`
    - `TargetNQR m x`
    - `QRSufficient k p := ¬(PrimeFactorQR (mOfK k) (xOfK p k) ∧ TargetNQR (mOfK k) (xOfK p k))`
  - records the equivalence
    ```lean
    ¬QRSufficient k p ↔ (PrimeFactorQR ... ∧ TargetNQR ...)
    ```
  - introduces the bridge lemma
    ```lean
    QRSufficient_gives_solution
    ```
    (currently a single isolated `sorry`, expected to be supplied by the Stage 8 algebra).

* `ErdosStraus/TenKObstruction.lean`
  - defines `TenfoldObstruction p` = the conjunction of the 10 QR obstructions.
  - isolates the Stage 8 target lemma
    ```lean
    theorem no_tenfold_obstruction (p) (hp : Prime p) (hMH : MordellHard840 p) :
      ¬ TenfoldObstruction p
    ```
    This is currently `sorry`, and is exactly the *unbounded* number-theoretic statement
    needed to finish Stage 8.

* `ErdosStraus/CoveringUnbounded.lean`
  - `ten_k_cover_complete` is no longer `sorry`.
  - It is proved by contradiction using:
    1. `¬(k5Sufficient p ∨ ... ∨ k29Sufficient p)`
    2. extracting `¬QRSufficient k p` for each `k`
    3. converting those into `TenfoldObstruction p`
    4. contradicting `no_tenfold_obstruction p`.

So: **Stage 8 is now reduced to proving `no_tenfold_obstruction` and the bridge
`QRSufficient_gives_solution`.**

## What is still missing

There are two mathematically substantive steps:

1. **QR-to-witness bridge** (`QRSufficient_gives_solution`).
   The current `QRSufficient` is defined as “not QR-obstructed”. To turn that into a
   Bradford Type II solution, one needs a lemma that *constructs* (or proves existence of)
   a divisor `d ∣ x^2` with `d ≡ -x (mod m)` under non-obstruction.

2. **Unbounded cover** (`no_tenfold_obstruction`).
   This is the real “Stage 8 theorem”: showing that a Mordell-hard prime cannot produce
   QR obstructions simultaneously for all ten shifts.

The Stage 8 prompt lists plausible approaches (CRT-based elimination, pairwise covering,
or structural constraints on prime factors of the arithmetic progression
`x_5, x_5+2, ..., x_5+24`).

At the moment, **there is no known Mathlib lemma that directly implies `no_tenfold_obstruction`**.
Any proof will require new number theory (or a reformulation into a finite modular covering).

## Optional empirical sanity-check

This repo includes a lightweight Python check (not used by Lean):

* `scripts/stage8_k10_random_check.py`
  - samples random Mordell-hard primes in a larger interval (default `[10^7, 10^8)`)
  - for each sample, tries all `k ∈ K10` and searches for a Bradford Type II witness divisor
    `d ∣ x^2` with `d ≡ -x (mod m)`
  - reports the first `k` found and the distribution over the sample.

This is only to build confidence; it does not replace the missing formal lemmas.
