# Stage 5 report (Lean formalization)

This report explains what the Lean files in `esc_stage5/` contain, how they connect to Stage 4 patterns, and what remains for Stage 6.

## 1. Bradford Type II formalization

File: `ErdosStraus/Bradford.lean`

- Defines the cross-multiplied Erdős–Straus equation predicate:

  \[ 4xyz = p(xy + xz + yz). \]

- Encodes the **Type II** Bradford witness condition:

  - `m = 4x - p` (must be positive)
  - `d ∣ x^2`
  - congruence `d ≡ -x (mod m)` written equivalently as `d + x ≡ 0 (mod m)`
  - (optional) `d ≤ x`

- Defines the reconstruction formulas

  - `y = p*(x+d)/m`
  - `z = p*(x + x^2/d)/m`

- The main theorem `bradford_typeII_valid` is structured so that:

  1. The **equation** follows from algebra + `d * (x^2/d) = x^2`.
  2. The **integrality** of `y` follows from `m ∣ (x+d)`.
  3. The **integrality** of `z` follows from `m ∣ (x + x^2/d)`;
     this is where the cancellation using `Nat.Coprime x m` is used.

## 2. k=0 theorem (m=3)

File: `ErdosStraus/K0.lean`

- Specializes Bradford Type II to `k=0`, where (empirically and by identity)

  - `m = 3`
  - `x0 = ceil(p/4)`

- For Mordell-hard primes (`p ≡ 1 (mod 12)`), we get `x0 ≡ 1 (mod 3)`.

- The central equivalence is stated as:

  `k=0 works  ↔  ∃ q : ℕ, Nat.Prime q ∧ q ∣ x0 ∧ q % 3 = 2`.

The file is organized so the forward/backward directions are separated:

- `→` uses: if `d ∣ x0^2` and `d ≡ 2 (mod 3)` then there exists a prime divisor `q` of `d` with `q % 3 = 2`, and `q ∣ x0`.
- `←` is constructive: take `d=q`.

## 3. k=1 theorem (m=7)

File: `ErdosStraus/K1.lean`

- Specializes to `k=1`, where `m=7` and `x1 = ceil(p/4)+1`.

- Uses the **QR obstruction** viewpoint:

  - If all prime factors of `x1` are quadratic residues mod 7, then every divisor of `x1^2` is a quadratic residue mod 7.
  - Since `-1` is a nonresidue mod 7, `-x1` flips QR/NQR.
  - Therefore, if `-x1` is nonresidue and all prime factors of `x1` are QR, the congruence class `d ≡ -x1 (mod 7)` is impossible.

The statement is formulated both in:

- `ZMod 7` + `IsSquare` form, and
- explicit residue-set form `{0,1,2,4}` vs `{3,5,6}` (helpful for brute-force closure lemmas).

## 4. Parametric family template

File: `ErdosStraus/Families.lean`

Introduces a structure for reusable “family lemmas” of the form:

- a modulus `M`
- a residue set `S : Finset (ZMod M)`
- a function producing `k`, `d` witnesses from a proof `p ∈ S`
- a correctness theorem that the produced `k,d` satisfy Bradford conditions

This is intended to become the backbone of a *finite covering proof*.

## 5. Remaining gaps / isolated axioms

File: `ErdosStraus/Axioms.lean`

Any missing number-theoretic lemma is isolated here.
The intent is:

- keep the project compiling early,
- concentrate “hard mathlib plumbing” in one place,
- replace axioms by proofs incrementally.

## 6. Stage 6 roadmap

1. Decide a target modulus `M` for the cover (empirically `M` is often a multiple of 840 and small odd primes `3+4k`).
2. For each residue class `a mod M`, pick a small `k ≤ K` and prove a lemma guaranteeing a divisor `d` satisfying Bradford congruence.
3. Combine the cases into a final `coverage` lemma:

   `∀ p prime, mordellHard p → ∃ k ≤ K, hasBradfordWitness p k`.

4. Combine with `bradford_typeII_valid` to obtain explicit certificates.

